/******************************************************************************
 * platform_hypercall.c
 * 
 * Hardware platform operations. Intended for use by domain-0 kernel.
 * 
 * Copyright (c) 2002-2006, K Fraser
 */

#include <xen/config.h>
#include <xen/types.h>
#include <xen/lib.h>
#include <xen/mm.h>
#include <xen/sched.h>
#include <xen/domain.h>
#include <xen/event.h>
#include <xen/domain_page.h>
#include <xen/trace.h>
#include <xen/console.h>
#include <xen/iocap.h>
#include <xen/guest_access.h>
#include <xen/acpi.h>
#include <asm/current.h>
#include <public/platform.h>
#include <asm/edd.h>
#include <asm/mtrr.h>
#include "cpu/mtrr/mtrr.h"
#include <xsm/xsm.h>

extern uint16_t boot_edid_caps;
extern uint8_t boot_edid_info[];

#ifndef COMPAT
typedef long ret_t;
DEFINE_SPINLOCK(xenpf_lock);
# undef copy_from_compat
# define copy_from_compat copy_from_guest
# undef copy_to_compat
# define copy_to_compat copy_to_guest
# undef guest_from_compat_handle
# define guest_from_compat_handle(x,y) ((x)=(y))
#else
extern spinlock_t xenpf_lock;
#endif

static DEFINE_PER_CPU(uint64_t, freq);

static long cpu_frequency_change_helper(void *data)
{
    return cpu_frequency_change(this_cpu(freq));
}

ret_t do_platform_op(XEN_GUEST_HANDLE(xen_platform_op_t) u_xenpf_op)
{
    ret_t ret = 0;
    struct xen_platform_op curop, *op = &curop;

    if ( !IS_PRIV(current->domain) )
        return -EPERM;

    if ( copy_from_guest(op, u_xenpf_op, 1) )
        return -EFAULT;

    if ( op->interface_version != XENPF_INTERFACE_VERSION )
        return -EACCES;

    spin_lock(&xenpf_lock);

    switch ( op->cmd )
    {
    case XENPF_settime:
    {
        ret = xsm_xen_settime();
        if ( ret )
            break;

        do_settime(op->u.settime.secs, 
                   op->u.settime.nsecs, 
                   op->u.settime.system_time);
        ret = 0;
    }
    break;

    case XENPF_add_memtype:
    {
        ret = xsm_memtype(op->cmd);
        if ( ret )
            break;

        ret = mtrr_add_page(
            op->u.add_memtype.mfn,
            op->u.add_memtype.nr_mfns,
            op->u.add_memtype.type,
            1);
        if ( ret >= 0 )
        {
            op->u.add_memtype.handle = 0;
            op->u.add_memtype.reg    = ret;
            ret = copy_to_guest(u_xenpf_op, op, 1) ? -EFAULT : 0;
            if ( ret != 0 )
                mtrr_del_page(ret, 0, 0);
        }
    }
    break;

    case XENPF_del_memtype:
    {
        ret = xsm_memtype(op->cmd);
        if ( ret )
            break;

        if (op->u.del_memtype.handle == 0
            /* mtrr/main.c otherwise does a lookup */
            && (int)op->u.del_memtype.reg >= 0)
        {
            ret = mtrr_del_page(op->u.del_memtype.reg, 0, 0);
            if ( ret > 0 )
                ret = 0;
        }
        else
            ret = -EINVAL;
    }
    break;

    case XENPF_read_memtype:
    {
        unsigned long mfn, nr_mfns;
        mtrr_type     type;

        ret = xsm_memtype(op->cmd);
        if ( ret )
            break;

        ret = -EINVAL;
        if ( op->u.read_memtype.reg < num_var_ranges )
        {
            mtrr_if->get(op->u.read_memtype.reg, &mfn, &nr_mfns, &type);
            op->u.read_memtype.mfn     = mfn;
            op->u.read_memtype.nr_mfns = nr_mfns;
            op->u.read_memtype.type    = type;
            ret = copy_to_guest(u_xenpf_op, op, 1) ? -EFAULT : 0;
        }
    }
    break;

    case XENPF_microcode_update:
    {
        extern int microcode_update(XEN_GUEST_HANDLE(void), unsigned long len);
        XEN_GUEST_HANDLE(void) data;

        ret = xsm_microcode();
        if ( ret )
            break;

        guest_from_compat_handle(data, op->u.microcode.data);
        ret = microcode_update(data, op->u.microcode.length);
    }
    break;

    case XENPF_platform_quirk:
    {
        extern int opt_noirqbalance;
        int quirk_id = op->u.platform_quirk.quirk_id;

        ret = xsm_platform_quirk(quirk_id);
        if ( ret )
            break;

        switch ( quirk_id )
        {
        case QUIRK_NOIRQBALANCING:
            printk("Platform quirk -- Disabling IRQ balancing/affinity.\n");
            opt_noirqbalance = 1;
            setup_ioapic_dest();
            break;
        case QUIRK_IOAPIC_BAD_REGSEL:
        case QUIRK_IOAPIC_GOOD_REGSEL:
#ifndef sis_apic_bug
            sis_apic_bug = (quirk_id == QUIRK_IOAPIC_BAD_REGSEL);
            dprintk(XENLOG_INFO, "Domain 0 says that IO-APIC REGSEL is %s\n",
                    sis_apic_bug ? "bad" : "good");
#else
            BUG_ON(sis_apic_bug != (quirk_id == QUIRK_IOAPIC_BAD_REGSEL));
#endif
            break;
        default:
            ret = -EINVAL;
            break;
        }
    }
    break;

    case XENPF_firmware_info:
        switch ( op->u.firmware_info.type )
        {
        case XEN_FW_DISK_INFO: {
            const struct edd_info *info;
            u16 length;

            ret = -ESRCH;
            if ( op->u.firmware_info.index >= bootsym(boot_edd_info_nr) )
                break;

            info = bootsym(boot_edd_info) + op->u.firmware_info.index;

            /* Transfer the EDD info block. */
            ret = -EFAULT;
            if ( copy_from_compat(&length, op->u.firmware_info.u.
                                  disk_info.edd_params, 1) )
                break;
            if ( length > info->edd_device_params.length )
                length = info->edd_device_params.length;
            if ( copy_to_compat(op->u.firmware_info.u.disk_info.edd_params,
                                (u8 *)&info->edd_device_params,
                                length) )
                break;
            if ( copy_to_compat(op->u.firmware_info.u.disk_info.edd_params,
                                &length, 1) )
                break;

            /* Transfer miscellaneous other information values. */
#define C(x) op->u.firmware_info.u.disk_info.x = info->x
            C(device);
            C(version);
            C(interface_support);
            C(legacy_max_cylinder);
            C(legacy_max_head);
            C(legacy_sectors_per_track);
#undef C

            ret = (copy_field_to_guest(u_xenpf_op, op,
                                      u.firmware_info.u.disk_info)
                   ? -EFAULT : 0);
            break;
        }
        case XEN_FW_DISK_MBR_SIGNATURE: {
            const struct mbr_signature *sig;

            ret = -ESRCH;
            if ( op->u.firmware_info.index >= bootsym(boot_mbr_signature_nr) )
                break;

            sig = bootsym(boot_mbr_signature) + op->u.firmware_info.index;

            op->u.firmware_info.u.disk_mbr_signature.device = sig->device;
            op->u.firmware_info.u.disk_mbr_signature.mbr_signature =
                sig->signature;

            ret = (copy_field_to_guest(u_xenpf_op, op,
                                      u.firmware_info.u.disk_mbr_signature)
                   ? -EFAULT : 0);
            break;
        }
        case XEN_FW_VBEDDC_INFO:
            ret = -ESRCH;
            if ( op->u.firmware_info.index != 0 )
                break;
            if ( *(u32 *)bootsym(boot_edid_info) == 0x13131313 )
                break;

            op->u.firmware_info.u.vbeddc_info.capabilities =
                bootsym(boot_edid_caps);
            op->u.firmware_info.u.vbeddc_info.edid_transfer_time =
                bootsym(boot_edid_caps) >> 8;

            ret = 0;
            if ( copy_field_to_guest(u_xenpf_op, op, u.firmware_info.
                                     u.vbeddc_info.capabilities) ||
                 copy_field_to_guest(u_xenpf_op, op, u.firmware_info.
                                     u.vbeddc_info.edid_transfer_time) ||
                 copy_to_compat(op->u.firmware_info.u.vbeddc_info.edid,
                                bootsym(boot_edid_info), 128) )
                ret = -EFAULT;
            break;
        default:
            ret = -EINVAL;
            break;
        }
        break;

    case XENPF_enter_acpi_sleep:
        ret = acpi_enter_sleep(&op->u.enter_acpi_sleep);
        break;

    case XENPF_change_freq:
        ret = -ENOSYS;
        if ( cpufreq_controller != FREQCTL_dom0_kernel )
            break;
        ret = -EINVAL;
        if ( op->u.change_freq.flags || !cpu_online(op->u.change_freq.cpu) )
            break;
        per_cpu(freq, op->u.change_freq.cpu) = op->u.change_freq.freq;
        ret = continue_hypercall_on_cpu(op->u.change_freq.cpu,
                                        cpu_frequency_change_helper,
                                        NULL);
        break;

    case XENPF_getidletime:
    {
        uint32_t cpu;
        uint64_t idletime, now = NOW();
        struct vcpu *v;
        struct xenctl_cpumap ctlmap;
        cpumask_t cpumap;
        XEN_GUEST_HANDLE(uint8) cpumap_bitmap;
        XEN_GUEST_HANDLE(uint64) idletimes;

        ret = -ENOSYS;
        if ( cpufreq_controller != FREQCTL_dom0_kernel )
            break;

        ctlmap.nr_cpus  = op->u.getidletime.cpumap_nr_cpus;
        guest_from_compat_handle(cpumap_bitmap,
                                 op->u.getidletime.cpumap_bitmap);
        ctlmap.bitmap.p = cpumap_bitmap.p; /* handle -> handle_64 conversion */
        xenctl_cpumap_to_cpumask(&cpumap, &ctlmap);
        guest_from_compat_handle(idletimes, op->u.getidletime.idletime);

        for_each_cpu_mask ( cpu, cpumap )
        {
            if ( (v = idle_vcpu[cpu]) != NULL )
            {
                idletime = v->runstate.time[RUNSTATE_running];
                if ( v->is_running )
                    idletime += now - v->runstate.state_entry_time;
            }
            else
            {
                idletime = 0;
                cpu_clear(cpu, cpumap);
            }

            ret = -EFAULT;
            if ( copy_to_guest_offset(idletimes, cpu, &idletime, 1) )
                goto out;
        }

        op->u.getidletime.now = now;
        cpumask_to_xenctl_cpumap(&ctlmap, &cpumap);
        ret = copy_to_guest(u_xenpf_op, op, 1) ? -EFAULT : 0;
    }
    break;

    default:
        ret = -ENOSYS;
        break;
    }

 out:
    spin_unlock(&xenpf_lock);

    return ret;
}

/*
 * Local variables:
 * mode: C
 * c-set-style: "BSD"
 * c-basic-offset: 4
 * tab-width: 4
 * indent-tabs-mode: nil
 * End:
 */
