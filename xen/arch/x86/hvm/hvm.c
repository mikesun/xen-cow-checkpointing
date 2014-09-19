/*
 * hvm.c: Common hardware virtual machine abstractions.
 *
 * Copyright (c) 2004, Intel Corporation.
 * Copyright (c) 2005, International Business Machines Corporation.
 *
 * This program is free software; you can redistribute it and/or modify it
 * under the terms and conditions of the GNU General Public License,
 * version 2, as published by the Free Software Foundation.
 *
 * This program is distributed in the hope it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
 * more details.
 *
 * You should have received a copy of the GNU General Public License along with
 * this program; if not, write to the Free Software Foundation, Inc., 59 Temple
 * Place - Suite 330, Boston, MA 02111-1307 USA.
 */

#include <xen/config.h>
#include <xen/init.h>
#include <xen/lib.h>
#include <xen/trace.h>
#include <xen/sched.h>
#include <xen/irq.h>
#include <xen/softirq.h>
#include <xen/domain.h>
#include <xen/domain_page.h>
#include <xen/hypercall.h>
#include <xen/guest_access.h>
#include <xen/event.h>
#include <asm/current.h>
#include <asm/e820.h>
#include <asm/io.h>
#include <asm/paging.h>
#include <asm/regs.h>
#include <asm/cpufeature.h>
#include <asm/processor.h>
#include <asm/types.h>
#include <asm/msr.h>
#include <asm/mc146818rtc.h>
#include <asm/spinlock.h>
#include <asm/hvm/hvm.h>
#include <asm/hvm/vpt.h>
#include <asm/hvm/support.h>
#include <asm/hvm/cacheattr.h>
#include <public/sched.h>
#include <public/hvm/ioreq.h>
#include <public/version.h>
#include <public/memory.h>

/*
 * Xen command-line option to allow/disallow hardware-assisted paging.
 * Since the phys-to-machine table of AMD NPT is in host format, 32-bit Xen
 * can only support guests using NPT with up to a 4GB memory map. Therefore
 * we disallow HAP by default on PAE Xen (by default we want to support an
 * 8GB pseudophysical memory map for HVM guests on a PAE host).
 */
static int opt_hap_permitted = (CONFIG_PAGING_LEVELS != 3);
boolean_param("hap", opt_hap_permitted);

int hvm_enabled __read_mostly;

unsigned int opt_hvm_debug_level __read_mostly;
integer_param("hvm_debug", opt_hvm_debug_level);

struct hvm_function_table hvm_funcs __read_mostly;

/* I/O permission bitmap is globally shared by all HVM guests. */
char __attribute__ ((__section__ (".bss.page_aligned")))
    hvm_io_bitmap[3*PAGE_SIZE];

void hvm_enable(struct hvm_function_table *fns)
{
    BUG_ON(hvm_enabled);
    printk("HVM: %s enabled\n", fns->name);

    /*
     * Allow direct access to the PC debug port (it is often used for I/O
     * delays, but the vmexits simply slow things down).
     */
    memset(hvm_io_bitmap, ~0, sizeof(hvm_io_bitmap));
    __clear_bit(0x80, hvm_io_bitmap);

    hvm_funcs   = *fns;
    hvm_enabled = 1;

    if ( hvm_funcs.hap_supported )
    {
        if ( !opt_hap_permitted )
            hvm_funcs.hap_supported = 0;
        printk("HVM: Hardware Assisted Paging detected %s.\n",
               hvm_funcs.hap_supported ? "and enabled" : "but disabled");
    }
}

void hvm_set_guest_tsc(struct vcpu *v, u64 guest_tsc)
{
    u64 host_tsc;

    rdtscll(host_tsc);

    v->arch.hvm_vcpu.cache_tsc_offset = guest_tsc - host_tsc;
    hvm_funcs.set_tsc_offset(v, v->arch.hvm_vcpu.cache_tsc_offset);
}

u64 hvm_get_guest_tsc(struct vcpu *v)
{
    u64 host_tsc;

    rdtscll(host_tsc);
    return host_tsc + v->arch.hvm_vcpu.cache_tsc_offset;
}

void hvm_migrate_timers(struct vcpu *v)
{
    rtc_migrate_timers(v);
    hpet_migrate_timers(v);
    pt_migrate(v);
}

void hvm_do_resume(struct vcpu *v)
{
    ioreq_t *p;

    pt_restore_timer(v);

    /* NB. Optimised for common case (p->state == STATE_IOREQ_NONE). */
    p = &get_ioreq(v)->vp_ioreq;
    while ( p->state != STATE_IOREQ_NONE )
    {
        switch ( p->state )
        {
        case STATE_IORESP_READY: /* IORESP_READY -> NONE */
            hvm_io_assist();
            break;
        case STATE_IOREQ_READY:  /* IOREQ_{READY,INPROCESS} -> IORESP_READY */
        case STATE_IOREQ_INPROCESS:
            wait_on_xen_event_channel(v->arch.hvm_vcpu.xen_port,
                                      (p->state != STATE_IOREQ_READY) &&
                                      (p->state != STATE_IOREQ_INPROCESS));
            break;
        default:
            gdprintk(XENLOG_ERR, "Weird HVM iorequest state %d.\n", p->state);
            domain_crash_synchronous();
        }
    }
}

static void hvm_init_ioreq_page(
    struct domain *d, struct hvm_ioreq_page *iorp)
{
    memset(iorp, 0, sizeof(*iorp));
    spin_lock_init(&iorp->lock);
    domain_pause(d);
}

static void hvm_destroy_ioreq_page(
    struct domain *d, struct hvm_ioreq_page *iorp)
{
    spin_lock(&iorp->lock);

    ASSERT(d->is_dying);

    if ( iorp->va != NULL )
    {
        unmap_domain_page_global(iorp->va);
        put_page_and_type(iorp->page);
        iorp->va = NULL;
    }

    spin_unlock(&iorp->lock);
}

static int hvm_set_ioreq_page(
    struct domain *d, struct hvm_ioreq_page *iorp, unsigned long gmfn)
{
    struct page_info *page;
    p2m_type_t p2mt;
    unsigned long mfn;
    void *va;

    mfn = mfn_x(gfn_to_mfn(d, gmfn, &p2mt));
    if ( !p2m_is_ram(p2mt) )
        return -EINVAL;
    ASSERT(mfn_valid(mfn));

    page = mfn_to_page(mfn);
    if ( !get_page_and_type(page, d, PGT_writable_page) )
        return -EINVAL;

    va = map_domain_page_global(mfn);
    if ( va == NULL )
    {
        put_page_and_type(page);
        return -ENOMEM;
    }

    spin_lock(&iorp->lock);

    if ( (iorp->va != NULL) || d->is_dying )
    {
        spin_unlock(&iorp->lock);
        unmap_domain_page_global(va);
        put_page_and_type(mfn_to_page(mfn));
        return -EINVAL;
    }

    iorp->va = va;
    iorp->page = page;

    spin_unlock(&iorp->lock);

    domain_unpause(d);

    return 0;
}

int hvm_domain_initialise(struct domain *d)
{
    int rc;

    if ( !hvm_enabled )
    {
        gdprintk(XENLOG_WARNING, "Attempt to create a HVM guest "
                 "on a non-VT/AMDV platform.\n");
        return -EINVAL;
    }

    spin_lock_init(&d->arch.hvm_domain.pbuf_lock);
    spin_lock_init(&d->arch.hvm_domain.irq_lock);
    spin_lock_init(&d->arch.hvm_domain.uc_lock);

    hvm_init_cacheattr_region_list(d);

    rc = paging_enable(d, PG_refcounts|PG_translate|PG_external);
    if ( rc != 0 )
        goto fail1;

    vpic_init(d);

    rc = vioapic_init(d);
    if ( rc != 0 )
        goto fail1;

    stdvga_init(d);

    hvm_init_ioreq_page(d, &d->arch.hvm_domain.ioreq);
    hvm_init_ioreq_page(d, &d->arch.hvm_domain.buf_ioreq);

    rc = hvm_funcs.domain_initialise(d);
    if ( rc != 0 )
        goto fail2;

    return 0;

 fail2:
    vioapic_deinit(d);
 fail1:
    hvm_destroy_cacheattr_region_list(d);
    return rc;
}

void hvm_domain_relinquish_resources(struct domain *d)
{
    hvm_destroy_ioreq_page(d, &d->arch.hvm_domain.ioreq);
    hvm_destroy_ioreq_page(d, &d->arch.hvm_domain.buf_ioreq);

    pit_deinit(d);
    rtc_deinit(d);
    pmtimer_deinit(d);
    hpet_deinit(d);
    stdvga_deinit(d);
}

void hvm_domain_destroy(struct domain *d)
{
    hvm_funcs.domain_destroy(d);
    vioapic_deinit(d);
    hvm_destroy_cacheattr_region_list(d);
}

static int hvm_save_cpu_ctxt(struct domain *d, hvm_domain_context_t *h)
{
    struct vcpu *v;
    struct hvm_hw_cpu ctxt;
    struct vcpu_guest_context *vc;

    for_each_vcpu(d, v)
    {
        /* We don't need to save state for a vcpu that is down; the restore 
         * code will leave it down if there is nothing saved. */
        if ( test_bit(_VPF_down, &v->pause_flags) ) 
            continue;

        /* Architecture-specific vmcs/vmcb bits */
        hvm_funcs.save_cpu_ctxt(v, &ctxt);

        /* Other vcpu register state */
        vc = &v->arch.guest_context;
        if ( v->fpu_initialised )
            memcpy(ctxt.fpu_regs, &vc->fpu_ctxt, sizeof(ctxt.fpu_regs));
        else 
            memset(ctxt.fpu_regs, 0, sizeof(ctxt.fpu_regs));
        ctxt.rax = vc->user_regs.eax;
        ctxt.rbx = vc->user_regs.ebx;
        ctxt.rcx = vc->user_regs.ecx;
        ctxt.rdx = vc->user_regs.edx;
        ctxt.rbp = vc->user_regs.ebp;
        ctxt.rsi = vc->user_regs.esi;
        ctxt.rdi = vc->user_regs.edi;
        ctxt.rsp = vc->user_regs.esp;
        ctxt.rip = vc->user_regs.eip;
        ctxt.rflags = vc->user_regs.eflags;
#ifdef __x86_64__
        ctxt.r8  = vc->user_regs.r8;
        ctxt.r9  = vc->user_regs.r9;
        ctxt.r10 = vc->user_regs.r10;
        ctxt.r11 = vc->user_regs.r11;
        ctxt.r12 = vc->user_regs.r12;
        ctxt.r13 = vc->user_regs.r13;
        ctxt.r14 = vc->user_regs.r14;
        ctxt.r15 = vc->user_regs.r15;
#endif
        ctxt.dr0 = vc->debugreg[0];
        ctxt.dr1 = vc->debugreg[1];
        ctxt.dr2 = vc->debugreg[2];
        ctxt.dr3 = vc->debugreg[3];
        ctxt.dr6 = vc->debugreg[6];
        ctxt.dr7 = vc->debugreg[7];

        if ( hvm_save_entry(CPU, v->vcpu_id, h, &ctxt) != 0 )
            return 1; 
    }
    return 0;
}

static int hvm_load_cpu_ctxt(struct domain *d, hvm_domain_context_t *h)
{
    int vcpuid, rc;
    struct vcpu *v;
    struct hvm_hw_cpu ctxt;
    struct vcpu_guest_context *vc;

    /* Which vcpu is this? */
    vcpuid = hvm_load_instance(h);
    if ( vcpuid > MAX_VIRT_CPUS || (v = d->vcpu[vcpuid]) == NULL ) 
    {
        gdprintk(XENLOG_ERR, "HVM restore: domain has no vcpu %u\n", vcpuid);
        return -EINVAL;
    }
    vc = &v->arch.guest_context;

    /* Need to init this vcpu before loading its contents */
    LOCK_BIGLOCK(d);
    if ( !v->is_initialised )
        if ( (rc = boot_vcpu(d, vcpuid, vc)) != 0 )
            return rc;
    UNLOCK_BIGLOCK(d);

    if ( hvm_load_entry(CPU, h, &ctxt) != 0 ) 
        return -EINVAL;

    /* Sanity check some control registers. */
    if ( (ctxt.cr0 & HVM_CR0_GUEST_RESERVED_BITS) ||
         !(ctxt.cr0 & X86_CR0_ET) ||
         ((ctxt.cr0 & (X86_CR0_PE|X86_CR0_PG)) == X86_CR0_PG) )
    {
        gdprintk(XENLOG_ERR, "HVM restore: bad CR0 0x%"PRIx64"\n",
                 ctxt.cr0);
        return -EINVAL;
    }

    if ( ctxt.cr4 & HVM_CR4_GUEST_RESERVED_BITS )
    {
        gdprintk(XENLOG_ERR, "HVM restore: bad CR4 0x%"PRIx64"\n",
                 ctxt.cr4);
        return -EINVAL;
    }

    if ( (ctxt.msr_efer & ~(EFER_FFXSE | EFER_LME | EFER_LMA |
                            EFER_NX | EFER_SCE)) ||
         ((sizeof(long) != 8) && (ctxt.msr_efer & EFER_LME)) ||
         (!cpu_has_nx && (ctxt.msr_efer & EFER_NX)) ||
         (!cpu_has_syscall && (ctxt.msr_efer & EFER_SCE)) ||
         (!cpu_has_ffxsr && (ctxt.msr_efer & EFER_FFXSE)) ||
         ((ctxt.msr_efer & (EFER_LME|EFER_LMA)) == EFER_LMA) )
    {
        gdprintk(XENLOG_ERR, "HVM restore: bad EFER 0x%"PRIx64"\n",
                 ctxt.msr_efer);
        return -EINVAL;
    }

    /* Architecture-specific vmcs/vmcb bits */
    if ( hvm_funcs.load_cpu_ctxt(v, &ctxt) < 0 )
        return -EINVAL;

    /* Other vcpu register state */
    memcpy(&vc->fpu_ctxt, ctxt.fpu_regs, sizeof(ctxt.fpu_regs));
    vc->user_regs.eax = ctxt.rax;
    vc->user_regs.ebx = ctxt.rbx;
    vc->user_regs.ecx = ctxt.rcx;
    vc->user_regs.edx = ctxt.rdx;
    vc->user_regs.ebp = ctxt.rbp;
    vc->user_regs.esi = ctxt.rsi;
    vc->user_regs.edi = ctxt.rdi;
    vc->user_regs.esp = ctxt.rsp;
    vc->user_regs.eip = ctxt.rip;
    vc->user_regs.eflags = ctxt.rflags | 2;
#ifdef __x86_64__
    vc->user_regs.r8  = ctxt.r8; 
    vc->user_regs.r9  = ctxt.r9; 
    vc->user_regs.r10 = ctxt.r10;
    vc->user_regs.r11 = ctxt.r11;
    vc->user_regs.r12 = ctxt.r12;
    vc->user_regs.r13 = ctxt.r13;
    vc->user_regs.r14 = ctxt.r14;
    vc->user_regs.r15 = ctxt.r15;
#endif
    vc->debugreg[0] = ctxt.dr0;
    vc->debugreg[1] = ctxt.dr1;
    vc->debugreg[2] = ctxt.dr2;
    vc->debugreg[3] = ctxt.dr3;
    vc->debugreg[6] = ctxt.dr6;
    vc->debugreg[7] = ctxt.dr7;

    vc->flags = VGCF_online;
    v->fpu_initialised = 1;

    /* Auxiliary processors should be woken immediately. */
    if ( test_and_clear_bit(_VPF_down, &v->pause_flags) )
        vcpu_wake(v);

    return 0;
}

HVM_REGISTER_SAVE_RESTORE(CPU, hvm_save_cpu_ctxt, hvm_load_cpu_ctxt,
                          1, HVMSR_PER_VCPU);

extern int reset_vmsr(struct mtrr_state *m, u64 *p);

int hvm_vcpu_initialise(struct vcpu *v)
{
    int rc;

    if ( (rc = vlapic_init(v)) != 0 )
        goto fail1;

    if ( (rc = hvm_funcs.vcpu_initialise(v)) != 0 )
        goto fail2;

    /* Create ioreq event channel. */
    rc = alloc_unbound_xen_event_channel(v, 0);
    if ( rc < 0 )
        goto fail3;

    /* Register ioreq event channel. */
    v->arch.hvm_vcpu.xen_port = rc;
    spin_lock(&v->domain->arch.hvm_domain.ioreq.lock);
    if ( v->domain->arch.hvm_domain.ioreq.va != NULL )
        get_ioreq(v)->vp_eport = v->arch.hvm_vcpu.xen_port;
    spin_unlock(&v->domain->arch.hvm_domain.ioreq.lock);

    spin_lock_init(&v->arch.hvm_vcpu.tm_lock);
    INIT_LIST_HEAD(&v->arch.hvm_vcpu.tm_list);

    rc = reset_vmsr(&v->arch.hvm_vcpu.mtrr, &v->arch.hvm_vcpu.pat_cr);
    if ( rc != 0 )
        goto fail3;

    v->arch.guest_context.user_regs.eflags = 2;

    if ( v->vcpu_id == 0 )
    {
        /* NB. All these really belong in hvm_domain_initialise(). */
        pit_init(v, cpu_khz);
        rtc_init(v, RTC_PORT(0));
        pmtimer_init(v);
        hpet_init(v);
 
        /* Init guest TSC to start from zero. */
        hvm_set_guest_time(v, 0);

        /* Can start up without SIPI-SIPI or setvcpucontext domctl. */
        v->is_initialised = 1;
        clear_bit(_VPF_down, &v->pause_flags);
    }

    return 0;

 fail3:
    hvm_funcs.vcpu_destroy(v);
 fail2:
    vlapic_destroy(v);
 fail1:
    return rc;
}

void hvm_vcpu_destroy(struct vcpu *v)
{
    xfree(v->arch.hvm_vcpu.mtrr.var_ranges);

    vlapic_destroy(v);
    hvm_funcs.vcpu_destroy(v);

    /* Event channel is already freed by evtchn_destroy(). */
    /*free_xen_event_channel(v, v->arch.hvm_vcpu.xen_port);*/
}


void hvm_vcpu_reset(struct vcpu *v)
{
    vcpu_pause(v);

    vlapic_reset(vcpu_vlapic(v));

    hvm_funcs.vcpu_initialise(v);

    set_bit(_VPF_down, &v->pause_flags);
    clear_bit(_VPF_blocked, &v->pause_flags);
    v->fpu_initialised = 0;
    v->fpu_dirtied     = 0;
    v->is_initialised  = 0;

    vcpu_unpause(v);
}

static void hvm_vcpu_down(void)
{
    struct vcpu *v = current;
    struct domain *d = v->domain;
    int online_count = 0;

    gdprintk(XENLOG_INFO, "VCPU%d: going offline.\n", v->vcpu_id);

    /* Doesn't halt us immediately, but we'll never return to guest context. */
    set_bit(_VPF_down, &v->pause_flags);
    vcpu_sleep_nosync(v);

    /* Any other VCPUs online? ... */
    LOCK_BIGLOCK(d);
    for_each_vcpu ( d, v )
        if ( !test_bit(_VPF_down, &v->pause_flags) )
            online_count++;
    UNLOCK_BIGLOCK(d);

    /* ... Shut down the domain if not. */
    if ( online_count == 0 )
    {
        gdprintk(XENLOG_INFO, "all CPUs offline -- powering off.\n");
        domain_shutdown(d, SHUTDOWN_poweroff);
    }
}

void hvm_send_assist_req(struct vcpu *v)
{
    ioreq_t *p;

    if ( unlikely(!vcpu_start_shutdown_deferral(v)) )
        return; /* implicitly bins the i/o operation */

    p = &get_ioreq(v)->vp_ioreq;
    if ( unlikely(p->state != STATE_IOREQ_NONE) )
    {
        /* This indicates a bug in the device model.  Crash the domain. */
        gdprintk(XENLOG_ERR, "Device model set bad IO state %d.\n", p->state);
        domain_crash_synchronous();
    }

    prepare_wait_on_xen_event_channel(v->arch.hvm_vcpu.xen_port);

    /*
     * Following happens /after/ blocking and setting up ioreq contents.
     * prepare_wait_on_xen_event_channel() is an implicit barrier.
     */
    p->state = STATE_IOREQ_READY;
    notify_via_xen_event_channel(v->arch.hvm_vcpu.xen_port);
}

void hvm_hlt(unsigned long rflags)
{
    /*
     * If we halt with interrupts disabled, that's a pretty sure sign that we
     * want to shut down. In a real processor, NMIs are the only way to break
     * out of this.
     */
    if ( unlikely(!(rflags & X86_EFLAGS_IF)) )
        return hvm_vcpu_down();

    do_sched_op_compat(SCHEDOP_block, 0);
}

void hvm_triple_fault(void)
{
    struct vcpu *v = current;
    gdprintk(XENLOG_INFO, "Triple fault on VCPU%d - "
             "invoking HVM system reset.\n", v->vcpu_id);
    domain_shutdown(v->domain, SHUTDOWN_reboot);
}

int hvm_set_efer(uint64_t value)
{
    struct vcpu *v = current;

    value &= ~EFER_LMA;

    if ( (value & ~(EFER_FFXSE | EFER_LME | EFER_NX | EFER_SCE)) ||
         ((sizeof(long) != 8) && (value & EFER_LME)) ||
         (!cpu_has_nx && (value & EFER_NX)) ||
         (!cpu_has_syscall && (value & EFER_SCE)) ||
         (!cpu_has_ffxsr && (value & EFER_FFXSE)) )
    {
        gdprintk(XENLOG_WARNING, "Trying to set reserved bit in "
                 "EFER: %"PRIx64"\n", value);
        hvm_inject_exception(TRAP_gp_fault, 0, 0);
        return 0;
    }

    if ( ((value ^ v->arch.hvm_vcpu.guest_efer) & EFER_LME) &&
         hvm_paging_enabled(v) )
    {
        gdprintk(XENLOG_WARNING,
                 "Trying to change EFER.LME with paging enabled\n");
        hvm_inject_exception(TRAP_gp_fault, 0, 0);
        return 0;
    }

    value |= v->arch.hvm_vcpu.guest_efer & EFER_LMA;
    v->arch.hvm_vcpu.guest_efer = value;
    hvm_update_guest_efer(v);

    return 1;
}

extern void shadow_blow_tables_per_domain(struct domain *d);
extern bool_t mtrr_pat_not_equal(struct vcpu *vd, struct vcpu *vs);

/* Exit UC mode only if all VCPUs agree on MTRR/PAT and are not in no_fill. */
static bool_t domain_exit_uc_mode(struct vcpu *v)
{
    struct domain *d = v->domain;
    struct vcpu *vs;

    for_each_vcpu ( d, vs )
    {
        if ( (vs == v) || !vs->is_initialised )
            continue;
        if ( (vs->arch.hvm_vcpu.cache_mode == NO_FILL_CACHE_MODE) ||
             mtrr_pat_not_equal(vs, v) )
            return 0;
    }

    return 1;
}

static void local_flush_cache(void *info)
{
    wbinvd();
}

int hvm_set_cr0(unsigned long value)
{
    struct vcpu *v = current;
    p2m_type_t p2mt;
    unsigned long gfn, mfn, old_value = v->arch.hvm_vcpu.guest_cr[0];

    HVM_DBG_LOG(DBG_LEVEL_VMMU, "Update CR0 value = %lx", value);

    if ( (u32)value != value )
    {
        HVM_DBG_LOG(DBG_LEVEL_1,
                    "Guest attempts to set upper 32 bits in CR0: %lx",
                    value);
        hvm_inject_exception(TRAP_gp_fault, 0, 0);
        return 0;
    }

    value &= ~HVM_CR0_GUEST_RESERVED_BITS;

    /* ET is reserved and should be always be 1. */
    value |= X86_CR0_ET;

    if ( (value & (X86_CR0_PE | X86_CR0_PG)) == X86_CR0_PG )
    {
        hvm_inject_exception(TRAP_gp_fault, 0, 0);
        return 0;
    }

    if ( (value & X86_CR0_PG) && !(old_value & X86_CR0_PG) )
    {
        if ( v->arch.hvm_vcpu.guest_efer & EFER_LME )
        {
            if ( !(v->arch.hvm_vcpu.guest_cr[4] & X86_CR4_PAE) )
            {
                HVM_DBG_LOG(DBG_LEVEL_1, "Enable paging before PAE enable");
                hvm_inject_exception(TRAP_gp_fault, 0, 0);
                return 0;
            }
            HVM_DBG_LOG(DBG_LEVEL_1, "Enabling long mode");
            v->arch.hvm_vcpu.guest_efer |= EFER_LMA;
            hvm_update_guest_efer(v);
        }

        if ( !paging_mode_hap(v->domain) )
        {
            /* The guest CR3 must be pointing to the guest physical. */
            gfn = v->arch.hvm_vcpu.guest_cr[3]>>PAGE_SHIFT;
            mfn = mfn_x(gfn_to_mfn_current(gfn, &p2mt));
            if ( !p2m_is_ram(p2mt) || !mfn_valid(mfn) ||
                 !get_page(mfn_to_page(mfn), v->domain))
            {
                gdprintk(XENLOG_ERR, "Invalid CR3 value = %lx (mfn=%lx)\n",
                         v->arch.hvm_vcpu.guest_cr[3], mfn);
                domain_crash(v->domain);
                return 0;
            }

            /* Now arch.guest_table points to machine physical. */
            v->arch.guest_table = pagetable_from_pfn(mfn);

            HVM_DBG_LOG(DBG_LEVEL_VMMU, "Update CR3 value = %lx, mfn = %lx",
                        v->arch.hvm_vcpu.guest_cr[3], mfn);
        }
    }
    else if ( !(value & X86_CR0_PG) && (old_value & X86_CR0_PG) )
    {
        /* When CR0.PG is cleared, LMA is cleared immediately. */
        if ( hvm_long_mode_enabled(v) )
        {
            v->arch.hvm_vcpu.guest_efer &= ~EFER_LMA;
            hvm_update_guest_efer(v);
        }

        if ( !paging_mode_hap(v->domain) )
        {
            put_page(pagetable_get_page(v->arch.guest_table));
            v->arch.guest_table = pagetable_null();
        }
    }

    if ( !list_empty(&domain_hvm_iommu(v->domain)->pdev_list) )
    {
        if ( (value & X86_CR0_CD) && !(value & X86_CR0_NW) )
        {
            /* Entering no fill cache mode. */
            spin_lock(&v->domain->arch.hvm_domain.uc_lock);
            v->arch.hvm_vcpu.cache_mode = NO_FILL_CACHE_MODE;

            if ( !v->domain->arch.hvm_domain.is_in_uc_mode )
            {
                /* Flush physical caches. */
                on_each_cpu(local_flush_cache, NULL, 1, 1);
                /* Shadow pagetables must recognise UC mode. */
                v->domain->arch.hvm_domain.is_in_uc_mode = 1;
                shadow_blow_tables_per_domain(v->domain);
            }
            spin_unlock(&v->domain->arch.hvm_domain.uc_lock);
        }
        else if ( !(value & (X86_CR0_CD | X86_CR0_NW)) &&
                  (v->arch.hvm_vcpu.cache_mode == NO_FILL_CACHE_MODE) )
        {
            /* Exit from no fill cache mode. */
            spin_lock(&v->domain->arch.hvm_domain.uc_lock);
            v->arch.hvm_vcpu.cache_mode = NORMAL_CACHE_MODE;

            if ( domain_exit_uc_mode(v) )
            {
                /* Shadow pagetables must recognise normal caching mode. */
                v->domain->arch.hvm_domain.is_in_uc_mode = 0;
                shadow_blow_tables_per_domain(v->domain);
            }
            spin_unlock(&v->domain->arch.hvm_domain.uc_lock);
        }
    }

    v->arch.hvm_vcpu.guest_cr[0] = value;
    hvm_update_guest_cr(v, 0);

    if ( (value ^ old_value) & X86_CR0_PG )
        paging_update_paging_modes(v);

    return 1;
}

int hvm_set_cr3(unsigned long value)
{
    unsigned long mfn;
    p2m_type_t p2mt;
    struct vcpu *v = current;

    if ( hvm_paging_enabled(v) && !paging_mode_hap(v->domain) &&
         (value != v->arch.hvm_vcpu.guest_cr[3]) )
    {
        /* Shadow-mode CR3 change. Check PDBR and update refcounts. */
        HVM_DBG_LOG(DBG_LEVEL_VMMU, "CR3 value = %lx", value);
        mfn = mfn_x(gfn_to_mfn_current(value >> PAGE_SHIFT, &p2mt));
        if ( !p2m_is_ram(p2mt) || !mfn_valid(mfn) ||
             !get_page(mfn_to_page(mfn), v->domain) )
              goto bad_cr3;

        put_page(pagetable_get_page(v->arch.guest_table));
        v->arch.guest_table = pagetable_from_pfn(mfn);

        HVM_DBG_LOG(DBG_LEVEL_VMMU, "Update CR3 value = %lx", value);
    }

    v->arch.hvm_vcpu.guest_cr[3] = value;
    paging_update_cr3(v);
    return 1;

 bad_cr3:
    gdprintk(XENLOG_ERR, "Invalid CR3\n");
    domain_crash(v->domain);
    return 0;
}

int hvm_set_cr4(unsigned long value)
{
    struct vcpu *v = current;
    unsigned long old_cr;

    if ( value & HVM_CR4_GUEST_RESERVED_BITS )
    {
        HVM_DBG_LOG(DBG_LEVEL_1,
                    "Guest attempts to set reserved bit in CR4: %lx",
                    value);
        goto gpf;
    }

    if ( !(value & X86_CR4_PAE) && hvm_long_mode_enabled(v) )
    {
        HVM_DBG_LOG(DBG_LEVEL_1, "Guest cleared CR4.PAE while "
                    "EFER.LMA is set");
        goto gpf;
    }

    old_cr = v->arch.hvm_vcpu.guest_cr[4];
    v->arch.hvm_vcpu.guest_cr[4] = value;
    hvm_update_guest_cr(v, 4);

    /* Modifying CR4.{PSE,PAE,PGE} invalidates all TLB entries, inc. Global. */
    if ( (old_cr ^ value) & (X86_CR4_PSE | X86_CR4_PGE | X86_CR4_PAE) )
        paging_update_paging_modes(v);

    return 1;

 gpf:
    hvm_inject_exception(TRAP_gp_fault, 0, 0);
    return 0;
}

int hvm_virtual_to_linear_addr(
    enum x86_segment seg,
    struct segment_register *reg,
    unsigned long offset,
    unsigned int bytes,
    enum hvm_access_type access_type,
    unsigned int addr_size,
    unsigned long *linear_addr)
{
    unsigned long addr = offset;
    uint32_t last_byte;

    if ( addr_size != 64 )
    {
        /*
         * COMPATIBILITY MODE: Apply segment checks and add base.
         */

        switch ( access_type )
        {
        case hvm_access_read:
            if ( (reg->attr.fields.type & 0xa) == 0x8 )
                goto gpf; /* execute-only code segment */
            break;
        case hvm_access_write:
            if ( (reg->attr.fields.type & 0xa) != 0x2 )
                goto gpf; /* not a writable data segment */
            break;
        default:
            break;
        }

        last_byte = offset + bytes - 1;

        /* Is this a grows-down data segment? Special limit check if so. */
        if ( (reg->attr.fields.type & 0xc) == 0x4 )
        {
            /* Is upper limit 0xFFFF or 0xFFFFFFFF? */
            if ( !reg->attr.fields.db )
                last_byte = (uint16_t)last_byte;

            /* Check first byte and last byte against respective bounds. */
            if ( (offset <= reg->limit) || (last_byte < offset) )
                goto gpf;
        }
        else if ( (last_byte > reg->limit) || (last_byte < offset) )
            goto gpf; /* last byte is beyond limit or wraps 0xFFFFFFFF */

        /*
         * Hardware truncates to 32 bits in compatibility mode.
         * It does not truncate to 16 bits in 16-bit address-size mode.
         */
        addr = (uint32_t)(addr + reg->base);
    }
    else
    {
        /*
         * LONG MODE: FS and GS add segment base. Addresses must be canonical.
         */

        if ( (seg == x86_seg_fs) || (seg == x86_seg_gs) )
            addr += reg->base;

        if ( !is_canonical_address(addr) )
            goto gpf;
    }

    *linear_addr = addr;
    return 1;

 gpf:
    return 0;
}

static void *hvm_map_entry(unsigned long va)
{
    unsigned long gfn, mfn;
    p2m_type_t p2mt;
    uint32_t pfec;

    if ( ((va & ~PAGE_MASK) + 8) > PAGE_SIZE )
    {
        gdprintk(XENLOG_ERR, "Descriptor table entry "
                 "straddles page boundary\n");
        domain_crash(current->domain);
        return NULL;
    }

    /* We're mapping on behalf of the segment-load logic, which might
     * write the accessed flags in the descriptors (in 32-bit mode), but
     * we still treat it as a kernel-mode read (i.e. no access checks). */
    pfec = PFEC_page_present;
    gfn = paging_gva_to_gfn(current, va, &pfec);
    mfn = mfn_x(gfn_to_mfn_current(gfn, &p2mt));
    if ( !p2m_is_ram(p2mt) )
    {
        gdprintk(XENLOG_ERR, "Failed to look up descriptor table entry\n");
        domain_crash(current->domain);
        return NULL;
    }

    ASSERT(mfn_valid(mfn));

    paging_mark_dirty(current->domain, mfn);

    return (char *)map_domain_page(mfn) + (va & ~PAGE_MASK);
}

static void hvm_unmap_entry(void *p)
{
    if ( p )
        unmap_domain_page(p);
}

static int hvm_load_segment_selector(
    struct vcpu *v, enum x86_segment seg, uint16_t sel)
{
    struct segment_register desctab, cs, segr;
    struct desc_struct *pdesc, desc;
    u8 dpl, rpl, cpl;
    int fault_type = TRAP_invalid_tss;

    /* NULL selector? */
    if ( (sel & 0xfffc) == 0 )
    {
        if ( (seg == x86_seg_cs) || (seg == x86_seg_ss) )
            goto fail;
        memset(&segr, 0, sizeof(segr));
        hvm_set_segment_register(v, seg, &segr);
        return 0;
    }

    /* LDT descriptor must be in the GDT. */
    if ( (seg == x86_seg_ldtr) && (sel & 4) )
        goto fail;

    hvm_get_segment_register(v, x86_seg_cs, &cs);
    hvm_get_segment_register(
        v, (sel & 4) ? x86_seg_ldtr : x86_seg_gdtr, &desctab);

    /* Check against descriptor table limit. */
    if ( ((sel & 0xfff8) + 7) > desctab.limit )
        goto fail;

    pdesc = hvm_map_entry(desctab.base + (sel & 0xfff8));
    if ( pdesc == NULL )
        goto hvm_map_fail;

    do {
        desc = *pdesc;

        /* Segment present in memory? */
        if ( !(desc.b & (1u<<15)) )
        {
            fault_type = TRAP_no_segment;
            goto unmap_and_fail;
        }

        /* LDT descriptor is a system segment. All others are code/data. */
        if ( (desc.b & (1u<<12)) == ((seg == x86_seg_ldtr) << 12) )
            goto unmap_and_fail;

        dpl = (desc.b >> 13) & 3;
        rpl = sel & 3;
        cpl = cs.sel & 3;

        switch ( seg )
        {
        case x86_seg_cs:
            /* Code segment? */
            if ( !(desc.b & (1u<<11)) )
                goto unmap_and_fail;
            /* Non-conforming segment: check DPL against RPL. */
            if ( ((desc.b & (6u<<9)) != 6) && (dpl != rpl) )
                goto unmap_and_fail;
            break;
        case x86_seg_ss:
            /* Writable data segment? */
            if ( (desc.b & (5u<<9)) != (1u<<9) )
                goto unmap_and_fail;
            if ( (dpl != cpl) || (dpl != rpl) )
                goto unmap_and_fail;
            break;
        case x86_seg_ldtr:
            /* LDT system segment? */
            if ( (desc.b & (15u<<8)) != (2u<<8) )
                goto unmap_and_fail;
            goto skip_accessed_flag;
        default:
            /* Readable code or data segment? */
            if ( (desc.b & (5u<<9)) == (4u<<9) )
                goto unmap_and_fail;
            /* Non-conforming segment: check DPL against RPL and CPL. */
            if ( ((desc.b & (6u<<9)) != 6) && ((dpl < cpl) || (dpl < rpl)) )
                goto unmap_and_fail;
            break;
        }
    } while ( !(desc.b & 0x100) && /* Ensure Accessed flag is set */
              (cmpxchg(&pdesc->b, desc.b, desc.b | 0x100) != desc.b) );

    /* Force the Accessed flag in our local copy. */
    desc.b |= 0x100;

 skip_accessed_flag:
    hvm_unmap_entry(pdesc);

    segr.base = (((desc.b <<  0) & 0xff000000u) |
                 ((desc.b << 16) & 0x00ff0000u) |
                 ((desc.a >> 16) & 0x0000ffffu));
    segr.attr.bytes = (((desc.b >>  8) & 0x00ffu) |
                       ((desc.b >> 12) & 0x0f00u));
    segr.limit = (desc.b & 0x000f0000u) | (desc.a & 0x0000ffffu);
    if ( segr.attr.fields.g )
        segr.limit = (segr.limit << 12) | 0xfffu;
    segr.sel = sel;
    hvm_set_segment_register(v, seg, &segr);

    return 0;

 unmap_and_fail:
    hvm_unmap_entry(pdesc);
 fail:
    hvm_inject_exception(fault_type, sel & 0xfffc, 0);
 hvm_map_fail:
    return 1;
}

void hvm_task_switch(
    uint16_t tss_sel, enum hvm_task_switch_reason taskswitch_reason,
    int32_t errcode)
{
    struct vcpu *v = current;
    struct cpu_user_regs *regs = guest_cpu_user_regs();
    struct segment_register gdt, tr, prev_tr, segr;
    struct desc_struct *optss_desc = NULL, *nptss_desc = NULL, tss_desc;
    unsigned long eflags;
    int exn_raised, rc;
    struct {
        u16 back_link,__blh;
        u32 esp0;
        u16 ss0, _0;
        u32 esp1;
        u16 ss1, _1;
        u32 esp2;
        u16 ss2, _2;
        u32 cr3, eip, eflags, eax, ecx, edx, ebx, esp, ebp, esi, edi;
        u16 es, _3, cs, _4, ss, _5, ds, _6, fs, _7, gs, _8, ldt, _9;
        u16 trace, iomap;
    } tss = { 0 };

    hvm_get_segment_register(v, x86_seg_gdtr, &gdt);
    hvm_get_segment_register(v, x86_seg_tr, &prev_tr);

    if ( ((tss_sel & 0xfff8) + 7) > gdt.limit )
    {
        hvm_inject_exception((taskswitch_reason == TSW_iret) ?
                             TRAP_invalid_tss : TRAP_gp_fault,
                             tss_sel & 0xfff8, 0);
        goto out;
    }

    optss_desc = hvm_map_entry(gdt.base + (prev_tr.sel & 0xfff8));
    if ( optss_desc == NULL )
        goto out;

    nptss_desc = hvm_map_entry(gdt.base + (tss_sel & 0xfff8));
    if ( nptss_desc == NULL )
        goto out;

    tss_desc = *nptss_desc;
    tr.sel = tss_sel;
    tr.base = (((tss_desc.b <<  0) & 0xff000000u) |
               ((tss_desc.b << 16) & 0x00ff0000u) |
               ((tss_desc.a >> 16) & 0x0000ffffu));
    tr.attr.bytes = (((tss_desc.b >>  8) & 0x00ffu) |
                     ((tss_desc.b >> 12) & 0x0f00u));
    tr.limit = (tss_desc.b & 0x000f0000u) | (tss_desc.a & 0x0000ffffu);
    if ( tr.attr.fields.g )
        tr.limit = (tr.limit << 12) | 0xfffu;

    if ( !tr.attr.fields.p )
    {
        hvm_inject_exception(TRAP_no_segment, tss_sel & 0xfff8, 0);
        goto out;
    }

    if ( tr.attr.fields.type != ((taskswitch_reason == TSW_iret) ? 0xb : 0x9) )
    {
        hvm_inject_exception(
            (taskswitch_reason == TSW_iret) ? TRAP_invalid_tss : TRAP_gp_fault,
            tss_sel & 0xfff8, 0);
        goto out;
    }

    if ( !tr.attr.fields.g && (tr.limit < (sizeof(tss)-1)) )
    {
        hvm_inject_exception(TRAP_invalid_tss, tss_sel & 0xfff8, 0);
        goto out;
    }

    rc = hvm_copy_from_guest_virt(&tss, prev_tr.base, sizeof(tss));
    if ( rc == HVMCOPY_bad_gva_to_gfn )
        goto out;

    eflags = regs->eflags;
    if ( taskswitch_reason == TSW_iret )
        eflags &= ~X86_EFLAGS_NT;

    tss.cr3    = v->arch.hvm_vcpu.guest_cr[3];
    tss.eip    = regs->eip;
    tss.eflags = eflags;
    tss.eax    = regs->eax;
    tss.ecx    = regs->ecx;
    tss.edx    = regs->edx;
    tss.ebx    = regs->ebx;
    tss.esp    = regs->esp;
    tss.ebp    = regs->ebp;
    tss.esi    = regs->esi;
    tss.edi    = regs->edi;

    hvm_get_segment_register(v, x86_seg_es, &segr);
    tss.es = segr.sel;
    hvm_get_segment_register(v, x86_seg_cs, &segr);
    tss.cs = segr.sel;
    hvm_get_segment_register(v, x86_seg_ss, &segr);
    tss.ss = segr.sel;
    hvm_get_segment_register(v, x86_seg_ds, &segr);
    tss.ds = segr.sel;
    hvm_get_segment_register(v, x86_seg_fs, &segr);
    tss.fs = segr.sel;
    hvm_get_segment_register(v, x86_seg_gs, &segr);
    tss.gs = segr.sel;
    hvm_get_segment_register(v, x86_seg_ldtr, &segr);
    tss.ldt = segr.sel;

    rc = hvm_copy_to_guest_virt(prev_tr.base, &tss, sizeof(tss));
    if ( rc == HVMCOPY_bad_gva_to_gfn )
        goto out;

    rc = hvm_copy_from_guest_virt(&tss, tr.base, sizeof(tss));
    if ( rc == HVMCOPY_bad_gva_to_gfn )
        goto out;

    if ( !hvm_set_cr3(tss.cr3) )
        goto out;

    regs->eip    = tss.eip;
    regs->eflags = tss.eflags | 2;
    regs->eax    = tss.eax;
    regs->ecx    = tss.ecx;
    regs->edx    = tss.edx;
    regs->ebx    = tss.ebx;
    regs->esp    = tss.esp;
    regs->ebp    = tss.ebp;
    regs->esi    = tss.esi;
    regs->edi    = tss.edi;

    if ( (taskswitch_reason == TSW_call_or_int) )
    {
        regs->eflags |= X86_EFLAGS_NT;
        tss.back_link = prev_tr.sel;
    }

    exn_raised = 0;
    if ( hvm_load_segment_selector(v, x86_seg_es, tss.es) ||
         hvm_load_segment_selector(v, x86_seg_cs, tss.cs) ||
         hvm_load_segment_selector(v, x86_seg_ss, tss.ss) ||
         hvm_load_segment_selector(v, x86_seg_ds, tss.ds) ||
         hvm_load_segment_selector(v, x86_seg_fs, tss.fs) ||
         hvm_load_segment_selector(v, x86_seg_gs, tss.gs) ||
         hvm_load_segment_selector(v, x86_seg_ldtr, tss.ldt) )
        exn_raised = 1;

    rc = hvm_copy_to_guest_virt(tr.base, &tss, sizeof(tss));
    if ( rc == HVMCOPY_bad_gva_to_gfn )
        exn_raised = 1;

    if ( (tss.trace & 1) && !exn_raised )
        hvm_inject_exception(TRAP_debug, tss_sel & 0xfff8, 0);

    tr.attr.fields.type = 0xb; /* busy 32-bit tss */
    hvm_set_segment_register(v, x86_seg_tr, &tr);

    v->arch.hvm_vcpu.guest_cr[0] |= X86_CR0_TS;
    hvm_update_guest_cr(v, 0);

    if ( (taskswitch_reason == TSW_iret) ||
         (taskswitch_reason == TSW_jmp) )
        clear_bit(41, optss_desc); /* clear B flag of old task */

    if ( taskswitch_reason != TSW_iret )
        set_bit(41, nptss_desc); /* set B flag of new task */

    if ( errcode >= 0 )
    {
        struct segment_register reg;
        unsigned long linear_addr;
        regs->esp -= 4;
        hvm_get_segment_register(current, x86_seg_ss, &reg);
        /* Todo: do not ignore access faults here. */
        if ( hvm_virtual_to_linear_addr(x86_seg_ss, &reg, regs->esp,
                                        4, hvm_access_write, 32,
                                        &linear_addr) )
            hvm_copy_to_guest_virt_nofault(linear_addr, &errcode, 4);
    }

 out:
    hvm_unmap_entry(optss_desc);
    hvm_unmap_entry(nptss_desc);
}

/*
 * __hvm_copy():
 *  @buf  = hypervisor buffer
 *  @addr = guest address to copy to/from
 *  @size = number of bytes to copy
 *  @dir  = copy *to* guest (TRUE) or *from* guest (FALSE)?
 *  @virt = addr is *virtual* (TRUE) or *guest physical* (FALSE)?
 *  @fetch = copy is an instruction fetch?
 * Returns number of bytes failed to copy (0 == complete success).
 */
static enum hvm_copy_result __hvm_copy(
    void *buf, paddr_t addr, int size, int dir, int virt, int fetch)
{
    struct vcpu *curr = current;
    unsigned long gfn, mfn;
    p2m_type_t p2mt;
    char *p;
    int count, todo;
    uint32_t pfec = PFEC_page_present;

    /*
     * We cannot use hvm_get_segment_register() while executing in
     * vmx_realmode() as segment register state is cached. Furthermore,
     * VMREADs on every data access hurts emulation performance.
     * Hence we do not gather extra PFEC flags if CR0.PG == 0.
     */
    if ( virt && (curr->arch.hvm_vcpu.guest_cr[0] & X86_CR0_PG) )
    {
        struct segment_register sreg;
        hvm_get_segment_register(curr, x86_seg_ss, &sreg);
        if ( sreg.attr.fields.dpl == 3 )
            pfec |= PFEC_user_mode;

        if ( dir ) 
            pfec |= PFEC_write_access;

        if ( fetch ) 
            pfec |= PFEC_insn_fetch;
    }

    todo = size;
    while ( todo > 0 )
    {
        count = min_t(int, PAGE_SIZE - (addr & ~PAGE_MASK), todo);

        if ( virt )
        {
            gfn = paging_gva_to_gfn(curr, addr, &pfec);
            if ( gfn == INVALID_GFN )
            {
                if ( virt == 2 ) /* 2 means generate a fault */
                    hvm_inject_exception(TRAP_page_fault, pfec, addr);
                return HVMCOPY_bad_gva_to_gfn;
            }
        }
        else
        {
            gfn = addr >> PAGE_SHIFT;
        }

        mfn = mfn_x(gfn_to_mfn_current(gfn, &p2mt));

        if ( !p2m_is_ram(p2mt) )
            return HVMCOPY_bad_gfn_to_mfn;
        ASSERT(mfn_valid(mfn));

        p = (char *)map_domain_page(mfn) + (addr & ~PAGE_MASK);

        if ( dir )
        {
            memcpy(p, buf, count); /* dir == TRUE:  *to* guest */
            paging_mark_dirty(curr->domain, mfn);
        }
        else
            memcpy(buf, p, count); /* dir == FALSE: *from guest */

        unmap_domain_page(p);
        
        addr += count;
        buf  += count;
        todo -= count;
    }

    return HVMCOPY_okay;
}

enum hvm_copy_result hvm_copy_to_guest_phys(
    paddr_t paddr, void *buf, int size)
{
    return __hvm_copy(buf, paddr, size, 1, 0, 0);
}

enum hvm_copy_result hvm_copy_from_guest_phys(
    void *buf, paddr_t paddr, int size)
{
    return __hvm_copy(buf, paddr, size, 0, 0, 0);
}

enum hvm_copy_result hvm_copy_to_guest_virt(
    unsigned long vaddr, void *buf, int size)
{
    return __hvm_copy(buf, vaddr, size, 1, 2, 0);
}

enum hvm_copy_result hvm_copy_from_guest_virt(
    void *buf, unsigned long vaddr, int size)
{
    return __hvm_copy(buf, vaddr, size, 0, 2, 0);
}

enum hvm_copy_result hvm_fetch_from_guest_virt(
    void *buf, unsigned long vaddr, int size)
{
    return __hvm_copy(buf, vaddr, size, 0, 2, hvm_nx_enabled(current));
}

enum hvm_copy_result hvm_copy_to_guest_virt_nofault(
    unsigned long vaddr, void *buf, int size)
{
    return __hvm_copy(buf, vaddr, size, 1, 1, 0);
}

enum hvm_copy_result hvm_copy_from_guest_virt_nofault(
    void *buf, unsigned long vaddr, int size)
{
    return __hvm_copy(buf, vaddr, size, 0, 1, 0);
}

enum hvm_copy_result hvm_fetch_from_guest_virt_nofault(
    void *buf, unsigned long vaddr, int size)
{
    return __hvm_copy(buf, vaddr, size, 0, 1, hvm_nx_enabled(current));
}


/* HVM specific printbuf. Mostly used for hvmloader chit-chat. */
void hvm_print_line(struct vcpu *v, const char c)
{
    struct hvm_domain *hd = &v->domain->arch.hvm_domain;

    spin_lock(&hd->pbuf_lock);
    hd->pbuf[hd->pbuf_idx++] = c;
    if ( (hd->pbuf_idx == (sizeof(hd->pbuf) - 2)) || (c == '\n') )
    {
        if ( c != '\n' )
            hd->pbuf[hd->pbuf_idx++] = '\n';
        hd->pbuf[hd->pbuf_idx] = '\0';
        printk(XENLOG_G_DEBUG "HVM%u: %s", v->domain->domain_id, hd->pbuf);
        hd->pbuf_idx = 0;
    }
    spin_unlock(&hd->pbuf_lock);
}

#define bitmaskof(idx)  (1U << ((idx) & 31))
void hvm_cpuid(unsigned int input, unsigned int *eax, unsigned int *ebx,
                                   unsigned int *ecx, unsigned int *edx)
{
    struct vcpu *v = current;

    if ( cpuid_hypervisor_leaves(input, eax, ebx, ecx, edx) )
        return;

    cpuid(input, eax, ebx, ecx, edx);

    switch ( input )
    {
    case 0x00000001:
        /* Clear #threads count and poke initial VLAPIC ID. */
        *ebx &= 0x0000FFFFu;
        *ebx |= (current->vcpu_id * 2) << 24;

        *ecx &= (bitmaskof(X86_FEATURE_XMM3) |
                 bitmaskof(X86_FEATURE_SSSE3) |
                 bitmaskof(X86_FEATURE_CX16) |
                 bitmaskof(X86_FEATURE_SSE4_1) |
                 bitmaskof(X86_FEATURE_SSE4_2) |
                 bitmaskof(X86_FEATURE_POPCNT));

        *edx &= (bitmaskof(X86_FEATURE_FPU) |
                 bitmaskof(X86_FEATURE_VME) |
                 bitmaskof(X86_FEATURE_DE) |
                 bitmaskof(X86_FEATURE_PSE) |
                 bitmaskof(X86_FEATURE_TSC) |
                 bitmaskof(X86_FEATURE_MSR) |
                 bitmaskof(X86_FEATURE_PAE) |
                 bitmaskof(X86_FEATURE_MCE) |
                 bitmaskof(X86_FEATURE_CX8) |
                 bitmaskof(X86_FEATURE_APIC) |
                 bitmaskof(X86_FEATURE_SEP) |
                 bitmaskof(X86_FEATURE_MTRR) |
                 bitmaskof(X86_FEATURE_PGE) |
                 bitmaskof(X86_FEATURE_MCA) |
                 bitmaskof(X86_FEATURE_CMOV) |
                 bitmaskof(X86_FEATURE_PAT) |
                 bitmaskof(X86_FEATURE_CLFLSH) |
                 bitmaskof(X86_FEATURE_MMX) |
                 bitmaskof(X86_FEATURE_FXSR) |
                 bitmaskof(X86_FEATURE_XMM) |
                 bitmaskof(X86_FEATURE_XMM2));
        if ( vlapic_hw_disabled(vcpu_vlapic(v)) )
            __clear_bit(X86_FEATURE_APIC & 31, edx);
#if CONFIG_PAGING_LEVELS >= 3
        if ( !v->domain->arch.hvm_domain.params[HVM_PARAM_PAE_ENABLED] )
#endif
            __clear_bit(X86_FEATURE_PAE & 31, edx);
        break;

    case 0x80000001:
#if CONFIG_PAGING_LEVELS >= 3
        if ( !v->domain->arch.hvm_domain.params[HVM_PARAM_PAE_ENABLED] )
#endif
            __clear_bit(X86_FEATURE_NX & 31, edx);
#ifdef __i386__
        /* Mask feature for Intel ia32e or AMD long mode. */
        __clear_bit(X86_FEATURE_LAHF_LM & 31, ecx);
        __clear_bit(X86_FEATURE_LM & 31, edx);
        __clear_bit(X86_FEATURE_SYSCALL & 31, edx);
#endif
        break;
    }
}

enum hvm_intblk hvm_interrupt_blocked(struct vcpu *v, struct hvm_intack intack)
{
    enum hvm_intblk r;
    ASSERT(v == current);

    r = hvm_funcs.interrupt_blocked(v, intack);
    if ( r != hvm_intblk_none )
        return r;

    if ( intack.source == hvm_intsrc_lapic )
    {
        uint32_t tpr = vlapic_get_reg(vcpu_vlapic(v), APIC_TASKPRI) & 0xF0;
        if ( (tpr >> 4) >= (intack.vector >> 4) )
            return hvm_intblk_tpr;
    }

    return r;
}

static long hvm_grant_table_op(
    unsigned int cmd, XEN_GUEST_HANDLE(void) uop, unsigned int count)
{
    if ( (cmd != GNTTABOP_query_size) && (cmd != GNTTABOP_setup_table) )
        return -ENOSYS; /* all other commands need auditing */
    return do_grant_table_op(cmd, uop, count);
}

typedef unsigned long hvm_hypercall_t(
    unsigned long, unsigned long, unsigned long, unsigned long, unsigned long);

#define HYPERCALL(x)                                        \
    [ __HYPERVISOR_ ## x ] = (hvm_hypercall_t *) do_ ## x

#if defined(__i386__)

static hvm_hypercall_t *hvm_hypercall32_table[NR_hypercalls] = {
    HYPERCALL(memory_op),
    [ __HYPERVISOR_grant_table_op ] = (hvm_hypercall_t *)hvm_grant_table_op,
    HYPERCALL(xen_version),
    HYPERCALL(event_channel_op),
    HYPERCALL(sched_op),
    HYPERCALL(hvm_op)
};

#else /* defined(__x86_64__) */

static long do_memory_op_compat32(int cmd, XEN_GUEST_HANDLE(void) arg)
{
    extern long do_add_to_physmap(struct xen_add_to_physmap *xatp);
    long rc;

    switch ( cmd )
    {
    case XENMEM_add_to_physmap:
    {
        struct {
            domid_t domid;
            uint32_t space;
            uint32_t idx;
            uint32_t gpfn;
        } u;
        struct xen_add_to_physmap h;

        if ( copy_from_guest(&u, arg, 1) )
            return -EFAULT;

        h.domid = u.domid;
        h.space = u.space;
        h.idx = u.idx;
        h.gpfn = u.gpfn;

        this_cpu(guest_handles_in_xen_space) = 1;
        rc = do_memory_op(cmd, guest_handle_from_ptr(&h, void));
        this_cpu(guest_handles_in_xen_space) = 0;

        break;
    }

    default:
        gdprintk(XENLOG_WARNING, "memory_op %d.\n", cmd);
        rc = -ENOSYS;
        break;
    }

    return rc;
}

static hvm_hypercall_t *hvm_hypercall64_table[NR_hypercalls] = {
    HYPERCALL(memory_op),
    [ __HYPERVISOR_grant_table_op ] = (hvm_hypercall_t *)hvm_grant_table_op,
    HYPERCALL(xen_version),
    HYPERCALL(event_channel_op),
    HYPERCALL(sched_op),
    HYPERCALL(hvm_op)
};

static hvm_hypercall_t *hvm_hypercall32_table[NR_hypercalls] = {
    [ __HYPERVISOR_memory_op ] = (hvm_hypercall_t *)do_memory_op_compat32,
    [ __HYPERVISOR_grant_table_op ] = (hvm_hypercall_t *)hvm_grant_table_op,
    HYPERCALL(xen_version),
    HYPERCALL(event_channel_op),
    HYPERCALL(sched_op),
    HYPERCALL(hvm_op)
};

#endif /* defined(__x86_64__) */

int hvm_do_hypercall(struct cpu_user_regs *regs)
{
    struct segment_register sreg;
    int flush, mode = hvm_guest_x86_mode(current);
    uint32_t eax = regs->eax;

    switch ( mode )
    {
#ifdef __x86_64__
    case 8:
#endif
    case 4:
    case 2:
        hvm_get_segment_register(current, x86_seg_ss, &sreg);
        if ( unlikely(sreg.attr.fields.dpl == 3) )
        {
    default:
            regs->eax = -EPERM;
            return HVM_HCALL_completed;
        }
    case 0:
        break;
    }

    if ( (eax >= NR_hypercalls) || !hvm_hypercall32_table[eax] )
    {
        regs->eax = -ENOSYS;
        return HVM_HCALL_completed;
    }

    /*
     * NB. In future flush only on decrease_reservation.
     * For now we also need to flush when pages are added, as qemu-dm is not
     * yet capable of faulting pages into an existing valid mapcache bucket.
     */
    flush = ((eax == __HYPERVISOR_memory_op) ||
             (eax == __HYPERVISOR_grant_table_op)); /* needed ? */
    this_cpu(hc_preempted) = 0;

#ifdef __x86_64__
    if ( mode == 8 )
    {
        HVM_DBG_LOG(DBG_LEVEL_HCALL, "hcall%u(%lx, %lx, %lx, %lx, %lx)", eax,
                    regs->rdi, regs->rsi, regs->rdx, regs->r10, regs->r8);

        regs->rax = hvm_hypercall64_table[eax](regs->rdi,
                                               regs->rsi,
                                               regs->rdx,
                                               regs->r10,
                                               regs->r8);
    }
    else
#endif
    {
        HVM_DBG_LOG(DBG_LEVEL_HCALL, "hcall%u(%x, %x, %x, %x, %x)", eax,
                    (uint32_t)regs->ebx, (uint32_t)regs->ecx,
                    (uint32_t)regs->edx, (uint32_t)regs->esi,
                    (uint32_t)regs->edi);

        regs->eax = hvm_hypercall32_table[eax]((uint32_t)regs->ebx,
                                               (uint32_t)regs->ecx,
                                               (uint32_t)regs->edx,
                                               (uint32_t)regs->esi,
                                               (uint32_t)regs->edi);
    }

    HVM_DBG_LOG(DBG_LEVEL_HCALL, "hcall%u -> %lx",
                eax, (unsigned long)regs->eax);

    return (this_cpu(hc_preempted) ? HVM_HCALL_preempted :
            flush ? HVM_HCALL_invalidate : HVM_HCALL_completed);
}

static void hvm_latch_shinfo_size(struct domain *d)
{
    /*
     * Called from operations which are among the very first executed by
     * PV drivers on initialisation or after save/restore. These are sensible
     * points at which to sample the execution mode of the guest and latch
     * 32- or 64-bit format for shared state.
     */
    if ( current->domain == d )
        d->arch.has_32bit_shinfo = (hvm_guest_x86_mode(current) != 8);
}

/* Initialise a hypercall transfer page for a VMX domain using
   paravirtualised drivers. */
void hvm_hypercall_page_initialise(struct domain *d,
                                   void *hypercall_page)
{
    hvm_latch_shinfo_size(d);
    hvm_funcs.init_hypercall_page(d, hypercall_page);
}

int hvm_bringup_ap(int vcpuid, int trampoline_vector)
{
    struct domain *d = current->domain;
    struct vcpu *v;
    struct vcpu_guest_context *ctxt;
    struct segment_register reg;

    ASSERT(is_hvm_domain(d));

    if ( (v = d->vcpu[vcpuid]) == NULL )
        return -ENOENT;

    v->fpu_initialised = 0;
    v->arch.flags |= TF_kernel_mode;
    v->is_initialised = 1;

    ctxt = &v->arch.guest_context;
    memset(ctxt, 0, sizeof(*ctxt));
    ctxt->flags = VGCF_online;
    ctxt->user_regs.eflags = 2;

#ifdef VMXASSIST
    if ( boot_cpu_data.x86_vendor == X86_VENDOR_INTEL )
    {
        ctxt->user_regs.eip = VMXASSIST_BASE;
        ctxt->user_regs.edx = vcpuid;
        ctxt->user_regs.ebx = trampoline_vector;
        goto done;
    }
#endif

    v->arch.hvm_vcpu.guest_cr[0] = X86_CR0_ET;
    hvm_update_guest_cr(v, 0);

    v->arch.hvm_vcpu.guest_cr[2] = 0;
    hvm_update_guest_cr(v, 2);

    v->arch.hvm_vcpu.guest_cr[3] = 0;
    hvm_update_guest_cr(v, 3);

    v->arch.hvm_vcpu.guest_cr[4] = 0;
    hvm_update_guest_cr(v, 4);

    v->arch.hvm_vcpu.guest_efer = 0;
    hvm_update_guest_efer(v);

    reg.sel = trampoline_vector << 8;
    reg.base = (uint32_t)reg.sel << 4;
    reg.limit = 0xffff;
    reg.attr.bytes = 0x89b;
    hvm_set_segment_register(v, x86_seg_cs, &reg);

    reg.sel = reg.base = 0;
    reg.limit = 0xffff;
    reg.attr.bytes = 0x893;
    hvm_set_segment_register(v, x86_seg_ds, &reg);
    hvm_set_segment_register(v, x86_seg_es, &reg);
    hvm_set_segment_register(v, x86_seg_fs, &reg);
    hvm_set_segment_register(v, x86_seg_gs, &reg);
    hvm_set_segment_register(v, x86_seg_ss, &reg);

    reg.attr.bytes = 0x82; /* LDT */
    hvm_set_segment_register(v, x86_seg_ldtr, &reg);

    reg.attr.bytes = 0x8b; /* 32-bit TSS (busy) */
    hvm_set_segment_register(v, x86_seg_tr, &reg);

    reg.attr.bytes = 0;
    hvm_set_segment_register(v, x86_seg_gdtr, &reg);
    hvm_set_segment_register(v, x86_seg_idtr, &reg);

#ifdef VMXASSIST
 done:
#endif
    /* Sync AP's TSC with BSP's. */
    v->arch.hvm_vcpu.cache_tsc_offset =
        v->domain->vcpu[0]->arch.hvm_vcpu.cache_tsc_offset;
    hvm_funcs.set_tsc_offset(v, v->arch.hvm_vcpu.cache_tsc_offset);

    if ( test_and_clear_bit(_VPF_down, &v->pause_flags) )
        vcpu_wake(v);

    gdprintk(XENLOG_INFO, "AP %d bringup succeeded.\n", vcpuid);
    return 0;
}

static int hvmop_set_pci_intx_level(
    XEN_GUEST_HANDLE(xen_hvm_set_pci_intx_level_t) uop)
{
    struct xen_hvm_set_pci_intx_level op;
    struct domain *d;
    int rc;

    if ( copy_from_guest(&op, uop, 1) )
        return -EFAULT;

    if ( !IS_PRIV(current->domain) )
        return -EPERM;

    if ( (op.domain > 0) || (op.bus > 0) || (op.device > 31) || (op.intx > 3) )
        return -EINVAL;

    d = rcu_lock_domain_by_id(op.domid);
    if ( d == NULL )
        return -ESRCH;

    rc = -EINVAL;
    if ( !is_hvm_domain(d) )
        goto out;

    rc = xsm_hvm_set_pci_intx_level(d);
    if ( rc )
        goto out;

    rc = 0;
    switch ( op.level )
    {
    case 0:
        hvm_pci_intx_deassert(d, op.device, op.intx);
        break;
    case 1:
        hvm_pci_intx_assert(d, op.device, op.intx);
        break;
    default:
        rc = -EINVAL;
        break;
    }

 out:
    rcu_unlock_domain(d);
    return rc;
}

static int hvmop_set_isa_irq_level(
    XEN_GUEST_HANDLE(xen_hvm_set_isa_irq_level_t) uop)
{
    struct xen_hvm_set_isa_irq_level op;
    struct domain *d;
    int rc;

    if ( copy_from_guest(&op, uop, 1) )
        return -EFAULT;

    if ( !IS_PRIV(current->domain) )
        return -EPERM;

    if ( op.isa_irq > 15 )
        return -EINVAL;

    d = rcu_lock_domain_by_id(op.domid);
    if ( d == NULL )
        return -ESRCH;

    rc = -EINVAL;
    if ( !is_hvm_domain(d) )
        goto out;

    rc = xsm_hvm_set_isa_irq_level(d);
    if ( rc )
        goto out;

    rc = 0;
    switch ( op.level )
    {
    case 0:
        hvm_isa_irq_deassert(d, op.isa_irq);
        break;
    case 1:
        hvm_isa_irq_assert(d, op.isa_irq);
        break;
    default:
        rc = -EINVAL;
        break;
    }

 out:
    rcu_unlock_domain(d);
    return rc;
}

static int hvmop_set_pci_link_route(
    XEN_GUEST_HANDLE(xen_hvm_set_pci_link_route_t) uop)
{
    struct xen_hvm_set_pci_link_route op;
    struct domain *d;
    int rc;

    if ( copy_from_guest(&op, uop, 1) )
        return -EFAULT;

    if ( !IS_PRIV(current->domain) )
        return -EPERM;

    if ( (op.link > 3) || (op.isa_irq > 15) )
        return -EINVAL;

    d = rcu_lock_domain_by_id(op.domid);
    if ( d == NULL )
        return -ESRCH;

    rc = -EINVAL;
    if ( !is_hvm_domain(d) )
        goto out;

    rc = xsm_hvm_set_pci_link_route(d);
    if ( rc )
        goto out;

    rc = 0;
    hvm_set_pci_link_route(d, op.link, op.isa_irq);

 out:
    rcu_unlock_domain(d);
    return rc;
}

static int hvmop_flush_tlb_all(void)
{
    struct domain *d = current->domain;
    struct vcpu *v;

    /* Avoid deadlock if more than one vcpu tries this at the same time. */
    if ( !spin_trylock(&d->hypercall_deadlock_mutex) )
        return -EAGAIN;

    /* Pause all other vcpus. */
    for_each_vcpu ( d, v )
        if ( v != current )
            vcpu_pause_nosync(v);

    /* Now that all VCPUs are signalled to deschedule, we wait... */
    for_each_vcpu ( d, v )
        if ( v != current )
            while ( !vcpu_runnable(v) && v->is_running )
                cpu_relax();

    /* All other vcpus are paused, safe to unlock now. */
    spin_unlock(&d->hypercall_deadlock_mutex);

    /* Flush paging-mode soft state (e.g., va->gfn cache; PAE PDPE cache). */
    for_each_vcpu ( d, v )
        paging_update_cr3(v);

    /* Flush all dirty TLBs. */
    flush_tlb_mask(d->domain_dirty_cpumask);

    /* Done. */
    for_each_vcpu ( d, v )
        if ( v != current )
            vcpu_unpause(v);

    return 0;
}

long do_hvm_op(unsigned long op, XEN_GUEST_HANDLE(void) arg)

{
    long rc = 0;

    switch ( op )
    {
    case HVMOP_set_param:
    case HVMOP_get_param:
    {
        struct xen_hvm_param a;
        struct hvm_ioreq_page *iorp;
        struct domain *d;
        struct vcpu *v;

        if ( copy_from_guest(&a, arg, 1) )
            return -EFAULT;

        if ( a.index >= HVM_NR_PARAMS )
            return -EINVAL;

        if ( a.domid == DOMID_SELF )
            d = rcu_lock_current_domain();
        else if ( IS_PRIV(current->domain) )
            d = rcu_lock_domain_by_id(a.domid);
        else
            return -EPERM;

        if ( d == NULL )
            return -ESRCH;

        rc = -EINVAL;
        if ( !is_hvm_domain(d) )
            goto param_fail;

        rc = xsm_hvm_param(d, op);
        if ( rc )
            goto param_fail;

        if ( op == HVMOP_set_param )
        {
            switch ( a.index )
            {
            case HVM_PARAM_IOREQ_PFN:
                iorp = &d->arch.hvm_domain.ioreq;
                rc = hvm_set_ioreq_page(d, iorp, a.value);
                spin_lock(&iorp->lock);
                if ( (rc == 0) && (iorp->va != NULL) )
                    /* Initialise evtchn port info if VCPUs already created. */
                    for_each_vcpu ( d, v )
                        get_ioreq(v)->vp_eport = v->arch.hvm_vcpu.xen_port;
                spin_unlock(&iorp->lock);
                break;
            case HVM_PARAM_BUFIOREQ_PFN: 
                iorp = &d->arch.hvm_domain.buf_ioreq;
                rc = hvm_set_ioreq_page(d, iorp, a.value);
                break;
            case HVM_PARAM_CALLBACK_IRQ:
                hvm_set_callback_via(d, a.value);
                hvm_latch_shinfo_size(d);
                break;
            case HVM_PARAM_TIMER_MODE:
                rc = -EINVAL;
                if ( a.value > HVMPTM_one_missed_tick_pending )
                    goto param_fail;
                break;
            }
            d->arch.hvm_domain.params[a.index] = a.value;
            rc = 0;
        }
        else
        {
            a.value = d->arch.hvm_domain.params[a.index];
            rc = copy_to_guest(arg, &a, 1) ? -EFAULT : 0;
        }

        HVM_DBG_LOG(DBG_LEVEL_HCALL, "%s param %u = %"PRIx64,
                    op == HVMOP_set_param ? "set" : "get",
                    a.index, a.value);

    param_fail:
        rcu_unlock_domain(d);
        break;
    }

    case HVMOP_set_pci_intx_level:
        rc = hvmop_set_pci_intx_level(
            guest_handle_cast(arg, xen_hvm_set_pci_intx_level_t));
        break;

    case HVMOP_set_isa_irq_level:
        rc = hvmop_set_isa_irq_level(
            guest_handle_cast(arg, xen_hvm_set_isa_irq_level_t));
        break;

    case HVMOP_set_pci_link_route:
        rc = hvmop_set_pci_link_route(
            guest_handle_cast(arg, xen_hvm_set_pci_link_route_t));
        break;

    case HVMOP_flush_tlbs:
        rc = guest_handle_is_null(arg) ? hvmop_flush_tlb_all() : -ENOSYS;
        break;

    default:
    {
        gdprintk(XENLOG_WARNING, "Bad HVM op %ld.\n", op);
        rc = -ENOSYS;
        break;
    }
    }

    if ( rc == -EAGAIN )
        rc = hypercall_create_continuation(
            __HYPERVISOR_hvm_op, "lh", op, arg);

    return rc;
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

