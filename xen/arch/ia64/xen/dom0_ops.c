/******************************************************************************
 * Arch-specific dom0_ops.c
 * 
 * Process command requests from domain-0 guest OS.
 * 
 * Copyright (c) 2002, K A Fraser
 */

#include <xen/config.h>
#include <xen/types.h>
#include <xen/lib.h>
#include <xen/mm.h>
#include <public/domctl.h>
#include <public/sysctl.h>
#include <xen/sched.h>
#include <xen/event.h>
#include <asm/pdb.h>
#include <xen/trace.h>
#include <xen/console.h>
#include <xen/guest_access.h>
#include <asm/vmx.h>
#include <asm/dom_fw.h>
#include <xen/iocap.h>
#include <xen/errno.h>
#include <xen/nodemask.h>
#include <asm/dom_fw_utils.h>
#include <asm/hvm/support.h>
#include <xsm/xsm.h>
#include <public/hvm/save.h>

#define get_xen_guest_handle(val, hnd)  do { val = (hnd).p; } while (0)

extern unsigned long total_pages;

long arch_do_domctl(xen_domctl_t *op, XEN_GUEST_HANDLE(xen_domctl_t) u_domctl)
{
    long ret = 0;

    if ( !IS_PRIV(current->domain) )
        return -EPERM;

    switch ( op->cmd )
    {
    case XEN_DOMCTL_getmemlist:
    {
        unsigned long i;
        struct domain *d = get_domain_by_id(op->domain);
        unsigned long start_page = op->u.getmemlist.start_pfn;
        unsigned long nr_pages = op->u.getmemlist.max_pfns;
        uint64_t mfn;

        if ( d == NULL ) {
            ret = -EINVAL;
            break;
        }
        for (i = 0 ; i < nr_pages ; i++) {
            pte_t *pte;

            pte = (pte_t *)lookup_noalloc_domain_pte(d,
                                               (start_page + i) << PAGE_SHIFT);
            if (pte && pte_present(*pte))
                mfn = start_page + i;
            else
                mfn = INVALID_MFN;

            if ( copy_to_guest_offset(op->u.getmemlist.buffer, i, &mfn, 1) ) {
                    ret = -EFAULT;
                    break;
            }
        }

        op->u.getmemlist.num_pfns = i;
        if (copy_to_guest(u_domctl, op, 1))
            ret = -EFAULT;

        put_domain(d);
    }
    break;

    case XEN_DOMCTL_arch_setup:
    {
        xen_domctl_arch_setup_t *ds = &op->u.arch_setup;
        struct domain *d = get_domain_by_id(op->domain);

        if ( d == NULL) {
            ret = -EINVAL;
            break;
        }

        if (ds->flags & XEN_DOMAINSETUP_query) {
            /* Set flags.  */
            if (d->arch.is_vti)
                ds->flags |= XEN_DOMAINSETUP_hvm_guest;
            /* Set params.  */
            ds->bp = 0;		/* unknown.  */
            ds->maxmem = d->arch.convmem_end;
            ds->xsi_va = d->arch.shared_info_va;
            ds->hypercall_imm = d->arch.breakimm;
#ifdef CONFIG_XEN_IA64_PERVCPU_VHPT
            ds->vhpt_size_log2 = d->arch.vhpt_size_log2;
#endif
            /* Copy back.  */
            if ( copy_to_guest(u_domctl, op, 1) )
                ret = -EFAULT;
        }
        else {
            if (ds->flags & XEN_DOMAINSETUP_hvm_guest) {
                if (!vmx_enabled) {
                    printk("No VMX hardware feature for vmx domain.\n");
                    ret = -EINVAL;
                } else {
                    d->arch.is_vti = 1;
                    xen_ia64_set_convmem_end(d, ds->maxmem);
                    ret = vmx_setup_platform(d);
                }
            }
            else {
                if (ds->hypercall_imm) {
                    /* dom_fw_setup() reads d->arch.breakimm */
                    struct vcpu *v;
                    d->arch.breakimm = ds->hypercall_imm;
                    for_each_vcpu (d, v)
                        v->arch.breakimm = d->arch.breakimm;
                }
#ifdef CONFIG_XEN_IA64_PERVCPU_VHPT
                if (ds->vhpt_size_log2 == -1) {
                    d->arch.has_pervcpu_vhpt = 0;
                    ds->vhpt_size_log2 = -1;
                    printk(XENLOG_INFO "XEN_DOMCTL_arch_setup: "
                           "domain %d VHPT is global.\n", d->domain_id);
                } else {
                    d->arch.has_pervcpu_vhpt = 1;
                    d->arch.vhpt_size_log2 = ds->vhpt_size_log2;
                    printk(XENLOG_INFO "XEN_DOMCTL_arch_setup: "
                           "domain %d VHPT is per vcpu. size=2**%d\n",
                           d->domain_id, ds->vhpt_size_log2);
                }
#endif
                if (ds->xsi_va)
                    d->arch.shared_info_va = ds->xsi_va;
                ret = dom_fw_setup(d, ds->bp, ds->maxmem);
            }
            if (ret == 0) {
                /*
                 * XXX IA64_SHARED_INFO_PADDR
                 * assign these pages into guest psudo physical address
                 * space for dom0 to map this page by gmfn.
                 * this is necessary for domain build, save, restore and 
                 * dump-core.
                 */
                unsigned long i;
                for (i = 0; i < XSI_SIZE; i += PAGE_SIZE)
                    assign_domain_page(d, IA64_SHARED_INFO_PADDR + i,
                                       virt_to_maddr(d->shared_info + i));
            }
        }

        put_domain(d);
    }
    break;

    case XEN_DOMCTL_shadow_op:
    {
        struct domain *d; 
        ret = -ESRCH;
        d = get_domain_by_id(op->domain);
        if ( d != NULL )
        {
            ret = shadow_mode_control(d, &op->u.shadow_op);
            put_domain(d);
            if (copy_to_guest(u_domctl, op, 1))
                ret = -EFAULT;
        } 
    }
    break;

    case XEN_DOMCTL_ioport_permission:
    {
        struct domain *d;
        unsigned int fp = op->u.ioport_permission.first_port;
        unsigned int np = op->u.ioport_permission.nr_ports;
        unsigned int lp = fp + np - 1;

        ret = -ESRCH;
        d = get_domain_by_id(op->domain);
        if (unlikely(d == NULL))
            break;

        if (np == 0)
            ret = 0;
        else {
            if (op->u.ioport_permission.allow_access)
                ret = ioports_permit_access(d, fp, lp);
            else
                ret = ioports_deny_access(d, fp, lp);
        }

        put_domain(d);
    }
    break;

    case XEN_DOMCTL_sendtrigger:
    {
        struct domain *d;
        struct vcpu *v;

        ret = -ESRCH;
        d = get_domain_by_id(op->domain);
        if ( d == NULL )
            break;

        ret = -EINVAL;
        if ( op->u.sendtrigger.vcpu >= MAX_VIRT_CPUS )
            goto sendtrigger_out;

        ret = -ESRCH;
        if ( (v = d->vcpu[op->u.sendtrigger.vcpu]) == NULL )
            goto sendtrigger_out;

        ret = 0;
        switch (op->u.sendtrigger.trigger)
        {
        case XEN_DOMCTL_SENDTRIGGER_INIT:
        {
            if (VMX_DOMAIN(v))
                vmx_pend_pal_init(d);
            else
                ret = -ENOSYS;
        }
        break;

        default:
            ret = -ENOSYS;
        }

    sendtrigger_out:
        put_domain(d);
    }
    break;

    case XEN_DOMCTL_sethvmcontext:
    { 
        struct hvm_domain_context c;
        struct domain *d;

        c.cur = 0;
        c.size = op->u.hvmcontext.size;
        c.data = NULL;
        
        ret = -ESRCH;
        d = rcu_lock_domain_by_id(op->domain);
        if (d == NULL)
            break;

#ifdef CONFIG_X86
        ret = xsm_hvmcontext(d, op->cmd);
        if (ret)
            goto sethvmcontext_out;
#endif /* CONFIG_X86 */

        ret = -EINVAL;
        if (!is_hvm_domain(d)) 
            goto sethvmcontext_out;

        ret = -ENOMEM;
        c.data = xmalloc_bytes(c.size);
        if (c.data == NULL)
            goto sethvmcontext_out;

        ret = -EFAULT;
        if (copy_from_guest(c.data, op->u.hvmcontext.buffer, c.size) != 0)
            goto sethvmcontext_out;

        domain_pause(d);
        ret = hvm_load(d, &c);
        domain_unpause(d);

    sethvmcontext_out:
        if (c.data != NULL)
            xfree(c.data);

        rcu_unlock_domain(d);
    }
    break;

    case XEN_DOMCTL_gethvmcontext:
    { 
        struct hvm_domain_context c;
        struct domain *d;

        ret = -ESRCH;
        d = rcu_lock_domain_by_id(op->domain);
        if (d == NULL)
            break;

#ifdef CONFIG_X86
        ret = xsm_hvmcontext(d, op->cmd);
        if (ret)
            goto gethvmcontext_out;
#endif /* CONFIG_X86 */

        ret = -EINVAL;
        if (!is_hvm_domain(d)) 
            goto gethvmcontext_out;

        c.cur = 0;
        c.size = hvm_save_size(d);
        c.data = NULL;

        if (guest_handle_is_null(op->u.hvmcontext.buffer)) {
            /* Client is querying for the correct buffer size */
            op->u.hvmcontext.size = c.size;
            ret = 0;
            goto gethvmcontext_out;            
        }

        /* Check that the client has a big enough buffer */
        ret = -ENOSPC;
        if (op->u.hvmcontext.size < c.size) 
            goto gethvmcontext_out;

        /* Allocate our own marshalling buffer */
        ret = -ENOMEM;
        c.data = xmalloc_bytes(c.size);
        if (c.data == NULL)
            goto gethvmcontext_out;

        domain_pause(d);
        ret = hvm_save(d, &c);
        domain_unpause(d);

        op->u.hvmcontext.size = c.cur;
        if (copy_to_guest(op->u.hvmcontext.buffer, c.data, c.size) != 0)
            ret = -EFAULT;

    gethvmcontext_out:
        if (copy_to_guest(u_domctl, op, 1))
            ret = -EFAULT;

        if (c.data != NULL)
            xfree(c.data);

        rcu_unlock_domain(d);
    }
    break;

    case XEN_DOMCTL_set_opt_feature:
    {
        struct xen_ia64_opt_feature *optf = &op->u.set_opt_feature.optf;
        struct domain *d = get_domain_by_id(op->domain);

        if (d == NULL) {
            ret = -EINVAL;
            break;
        }

        ret = domain_opt_feature(d, optf);
        put_domain(d);
    }
    break;

    default:
        printk("arch_do_domctl: unrecognized domctl: %d!!!\n",op->cmd);
        ret = -ENOSYS;

    }

    return ret;
}

long arch_do_sysctl(xen_sysctl_t *op, XEN_GUEST_HANDLE(xen_sysctl_t) u_sysctl)
{
    long ret = 0;

    switch ( op->cmd )
    {
    case XEN_SYSCTL_physinfo:
    {
        int i;
        uint32_t max_array_ent;

        xen_sysctl_physinfo_t *pi = &op->u.physinfo;

        pi->threads_per_core = cpus_weight(cpu_sibling_map[0]);
        pi->cores_per_socket =
            cpus_weight(cpu_core_map[0]) / pi->threads_per_core;
        pi->nr_cpus          = (u32)num_online_cpus();
        pi->nr_nodes         = num_online_nodes();
        pi->total_pages      = total_pages; 
        pi->free_pages       = avail_domheap_pages();
        pi->scrub_pages      = avail_scrub_pages();
        pi->cpu_khz          = local_cpu_data->proc_freq / 1000;
        memset(pi->hw_cap, 0, sizeof(pi->hw_cap));

        max_array_ent = pi->max_cpu_id;
        pi->max_cpu_id = last_cpu(cpu_online_map);
        max_array_ent = min_t(uint32_t, max_array_ent, pi->max_cpu_id);

        ret = 0;

        if (!guest_handle_is_null(pi->cpu_to_node)) {
            for (i = 0; i <= max_array_ent; i++) {
                uint32_t node = cpu_online(i) ? cpu_to_node(i) : ~0u;
                if (copy_to_guest_offset(pi->cpu_to_node, i, &node, 1)) {
                    ret = -EFAULT;
                    break;
                }
            }
        }

        if ( copy_to_guest(u_sysctl, op, 1) )
            ret = -EFAULT;
    }
    break;

    default:
        printk("arch_do_sysctl: unrecognized sysctl: %d!!!\n",op->cmd);
        ret = -ENOSYS;

    }

    return ret;
}

static unsigned long
dom0vp_ioremap(struct domain *d, unsigned long mpaddr, unsigned long size)
{
    unsigned long end;

    /* Linux may use a 0 size!  */
    if (size == 0)
        size = PAGE_SIZE;

    if (size == 0)
        printk(XENLOG_WARNING "ioremap(): Trying to map %lx, size 0\n", mpaddr);

    end = PAGE_ALIGN(mpaddr + size);

    if (!iomem_access_permitted(d, mpaddr >> PAGE_SHIFT,
                                (end >> PAGE_SHIFT) - 1))
        return -EPERM;

    return assign_domain_mmio_page(d, mpaddr, mpaddr, size,
                                   ASSIGN_writable | ASSIGN_nocache);
}

static unsigned long
dom0vp_fpswa_revision(XEN_GUEST_HANDLE(uint) revision)
{
    if (fpswa_interface == NULL)
        return -ENOSYS;
    if (copy_to_guest(revision, &fpswa_interface->revision, 1))
        return -EFAULT;
    return 0;
}

static unsigned long
dom0vp_add_io_space(struct domain *d, unsigned long phys_base,
                    unsigned long sparse, unsigned long space_number)
{
    unsigned int fp, lp;

    /*
     * Registering new io_space roughly based on linux
     * arch/ia64/pci/pci.c:new_space()
     */

    /* Skip legacy I/O port space, we already know about it */
    if (phys_base == 0)
        return 0;

    /*
     * Dom0 Linux initializes io spaces sequentially, if that changes,
     * we'll need to add thread protection and the ability to handle
     * a sparsely populated io_space array.
     */
    if (space_number > MAX_IO_SPACES || space_number != num_io_spaces)
        return -EINVAL;

    io_space[space_number].mmio_base = phys_base;
    io_space[space_number].sparse = sparse;

    num_io_spaces++;

    fp = space_number << IO_SPACE_BITS;
    lp = fp | 0xffff;

    return ioports_permit_access(d, fp, lp);
}

unsigned long
do_dom0vp_op(unsigned long cmd,
             unsigned long arg0, unsigned long arg1, unsigned long arg2,
             unsigned long arg3)
{
    unsigned long ret = 0;
    struct domain *d = current->domain;

    switch (cmd) {
    case IA64_DOM0VP_ioremap:
        ret = dom0vp_ioremap(d, arg0, arg1);
        break;
    case IA64_DOM0VP_phystomach:
        ret = ____lookup_domain_mpa(d, arg0 << PAGE_SHIFT);
        if (ret == INVALID_MFN) {
            dprintk(XENLOG_INFO, "%s: INVALID_MFN ret: 0x%lx\n",
                     __func__, ret);
        } else {
            ret = (ret & _PFN_MASK) >> PAGE_SHIFT;//XXX pte_pfn()
        }
        perfc_incr(dom0vp_phystomach);
        break;
    case IA64_DOM0VP_machtophys:
        if (!mfn_valid(arg0)) {
            ret = INVALID_M2P_ENTRY;
            break;
        }
        ret = get_gpfn_from_mfn(arg0);
        perfc_incr(dom0vp_machtophys);
        break;
    case IA64_DOM0VP_zap_physmap:
        ret = dom0vp_zap_physmap(d, arg0, (unsigned int)arg1);
        break;
    case IA64_DOM0VP_add_physmap:
        if (!IS_PRIV(d))
            return -EPERM;
        ret = dom0vp_add_physmap(d, arg0, arg1, (unsigned int)arg2,
                                 (domid_t)arg3);
        break;
    case IA64_DOM0VP_add_physmap_with_gmfn:
        if (!IS_PRIV(d))
            return -EPERM;
        ret = dom0vp_add_physmap_with_gmfn(d, arg0, arg1, (unsigned int)arg2,
                                           (domid_t)arg3);
        break;
    case IA64_DOM0VP_expose_p2m:
        ret = dom0vp_expose_p2m(d, arg0, arg1, arg2, arg3);
        break;
    case IA64_DOM0VP_perfmon: {
        XEN_GUEST_HANDLE(void) hnd;
        set_xen_guest_handle(hnd, (void*)arg1);
        ret = do_perfmon_op(arg0, hnd, arg2);
        break;
    }
    case IA64_DOM0VP_fpswa_revision: {
        XEN_GUEST_HANDLE(uint) hnd;
        set_xen_guest_handle(hnd, (uint*)arg0);
        ret = dom0vp_fpswa_revision(hnd);
        break;
    }
    case IA64_DOM0VP_add_io_space:
        ret = dom0vp_add_io_space(d, arg0, arg1, arg2);
        break;
    case IA64_DOM0VP_expose_foreign_p2m: {
        XEN_GUEST_HANDLE(char) hnd;
        set_xen_guest_handle(hnd, (char*)arg2);
        ret = dom0vp_expose_foreign_p2m(d, arg0, (domid_t)arg1, hnd, arg3);
        break;
    }
    case IA64_DOM0VP_unexpose_foreign_p2m:
        ret = dom0vp_unexpose_foreign_p2m(d, arg0, arg1);
        break;
    default:
        ret = -1;
		printk("unknown dom0_vp_op 0x%lx\n", cmd);
        break;
    }

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
