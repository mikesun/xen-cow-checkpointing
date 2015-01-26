/******************************************************************************
 * arch/x86/mm/shadow/common.c
 *
 * Modifed for CoW by Mike Sun.
 *
 * Shadow code that does not need to be multiply compiled.
 * Parts of this code are Copyright (c) 2006 by XenSource Inc.
 * Parts of this code are Copyright (c) 2006 by Michael A Fetterman
 * Parts based on earlier work by Michael A Fetterman, Ian Pratt et al.
 * 
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 */

#include <xen/config.h>
#include <xen/types.h>
#include <xen/mm.h>
#include <xen/trace.h>
#include <xen/sched.h>
#include <xen/perfc.h>
#include <xen/irq.h>
#include <xen/domain_page.h>
#include <xen/guest_access.h>
#include <xen/keyhandler.h>
#include <public/hvm/e820.h>
#include <asm/event.h>
#include <asm/page.h>
#include <asm/p2m.h>
#include <asm/current.h>
#include <asm/flushtlb.h>
#include <asm/shadow.h>
#include "private.h"

/* CoW Data Structures */
struct cow_data cow;

/* Set up the shadow-specific parts of a domain struct at start of day.
 * Called for every domain from arch_domain_create() */
void shadow_domain_init(struct domain *d)
{
    int i;
    shadow_lock_init(d);
    for ( i = 0; i <= SHADOW_MAX_ORDER; i++ )
        INIT_LIST_HEAD(&d->arch.paging.shadow.freelists[i]);
    INIT_LIST_HEAD(&d->arch.paging.shadow.p2m_freelist);
    INIT_LIST_HEAD(&d->arch.paging.shadow.pinned_shadows);

    /* Use shadow pagetables for log-dirty support */
    paging_log_dirty_init(d, shadow_enable_log_dirty, 
                          shadow_disable_log_dirty, shadow_clean_dirty_bitmap);
}

/* Setup the shadow-specfic parts of a vcpu struct. Note: The most important
 * job is to initialize the update_paging_modes() function pointer, which is
 * used to initialized the rest of resources. Therefore, it really does not
 * matter to have v->arch.paging.mode pointing to any mode, as long as it can
 * be compiled.
 */
void shadow_vcpu_init(struct vcpu *v)
{
#if CONFIG_PAGING_LEVELS == 4
    v->arch.paging.mode = &SHADOW_INTERNAL_NAME(sh_paging_mode,3,3);
#elif CONFIG_PAGING_LEVELS == 3
    v->arch.paging.mode = &SHADOW_INTERNAL_NAME(sh_paging_mode,3,3);
#elif CONFIG_PAGING_LEVELS == 2
    v->arch.paging.mode = &SHADOW_INTERNAL_NAME(sh_paging_mode,2,2);
#endif
}

#if SHADOW_AUDIT
int shadow_audit_enable = 0;

static void shadow_audit_key(unsigned char key)
{
    shadow_audit_enable = !shadow_audit_enable;
    printk("%s shadow_audit_enable=%d\n",
           __func__, shadow_audit_enable);
}

static int __init shadow_audit_key_init(void)
{
    register_keyhandler(
        'O', shadow_audit_key,  "toggle shadow audits");
    return 0;
}
__initcall(shadow_audit_key_init);
#endif /* SHADOW_AUDIT */

int _shadow_mode_refcounts(struct domain *d)
{
    return shadow_mode_refcounts(d);
}


/**************************************************************************/
/* x86 emulator support for the shadow code
 */

struct segment_register *hvm_get_seg_reg(
    enum x86_segment seg, struct sh_emulate_ctxt *sh_ctxt)
{
    struct segment_register *seg_reg = &sh_ctxt->seg_reg[seg];
    if ( !__test_and_set_bit(seg, &sh_ctxt->valid_seg_regs) )
        hvm_get_segment_register(current, seg, seg_reg);
    return seg_reg;
}

static int hvm_translate_linear_addr(
    enum x86_segment seg,
    unsigned long offset,
    unsigned int bytes,
    enum hvm_access_type access_type,
    struct sh_emulate_ctxt *sh_ctxt,
    unsigned long *paddr)
{
    struct segment_register *reg = hvm_get_seg_reg(seg, sh_ctxt);
    int okay;

    okay = hvm_virtual_to_linear_addr(
        seg, reg, offset, bytes, access_type, sh_ctxt->ctxt.addr_size, paddr);

    if ( !okay )
    {
        hvm_inject_exception(TRAP_gp_fault, 0, 0);
        return X86EMUL_EXCEPTION;
    }

    return 0;
}

static int
hvm_read(enum x86_segment seg,
         unsigned long offset,
         unsigned long *val,
         unsigned int bytes,
         enum hvm_access_type access_type,
         struct sh_emulate_ctxt *sh_ctxt)
{
    unsigned long addr;
    int rc;

    rc = hvm_translate_linear_addr(
        seg, offset, bytes, access_type, sh_ctxt, &addr);
    if ( rc )
        return rc;

    *val = 0;

    if ( access_type == hvm_access_insn_fetch )
        rc = hvm_fetch_from_guest_virt(val, addr, bytes);
    else
        rc = hvm_copy_from_guest_virt(val, addr, bytes);

    switch ( rc )
    {
    case HVMCOPY_okay:
        return X86EMUL_OKAY;
    case HVMCOPY_bad_gva_to_gfn:
        return X86EMUL_EXCEPTION;
    default:
        break;
    }

    return X86EMUL_UNHANDLEABLE;
}

static int
hvm_emulate_read(enum x86_segment seg,
                 unsigned long offset,
                 unsigned long *val,
                 unsigned int bytes,
                 struct x86_emulate_ctxt *ctxt)
{
    if ( !is_x86_user_segment(seg) )
        return X86EMUL_UNHANDLEABLE;
    return hvm_read(seg, offset, val, bytes, hvm_access_read,
                    container_of(ctxt, struct sh_emulate_ctxt, ctxt));
}

static int
hvm_emulate_insn_fetch(enum x86_segment seg,
                       unsigned long offset,
                       unsigned long *val,
                       unsigned int bytes,
                       struct x86_emulate_ctxt *ctxt)
{
    struct sh_emulate_ctxt *sh_ctxt =
        container_of(ctxt, struct sh_emulate_ctxt, ctxt);
    unsigned int insn_off = offset - sh_ctxt->insn_buf_eip;

    ASSERT(seg == x86_seg_cs);

    /* Fall back if requested bytes are not in the prefetch cache. */
    if ( unlikely((insn_off + bytes) > sh_ctxt->insn_buf_bytes) )
        return hvm_read(seg, offset, val, bytes,
                        hvm_access_insn_fetch, sh_ctxt);

    /* Hit the cache. Simple memcpy. */
    *val = 0;
    memcpy(val, &sh_ctxt->insn_buf[insn_off], bytes);
    return X86EMUL_OKAY;
}

static int
hvm_emulate_write(enum x86_segment seg,
                  unsigned long offset,
                  unsigned long val,
                  unsigned int bytes,
                  struct x86_emulate_ctxt *ctxt)
{
    struct sh_emulate_ctxt *sh_ctxt =
        container_of(ctxt, struct sh_emulate_ctxt, ctxt);
    struct vcpu *v = current;
    unsigned long addr;
    int rc;

    if ( !is_x86_user_segment(seg) )
        return X86EMUL_UNHANDLEABLE;

    /* How many emulations could we save if we unshadowed on stack writes? */
    if ( seg == x86_seg_ss )
        perfc_incr(shadow_fault_emulate_stack);

    rc = hvm_translate_linear_addr(
        seg, offset, bytes, hvm_access_write, sh_ctxt, &addr);
    if ( rc )
        return rc;

    return v->arch.paging.mode->shadow.x86_emulate_write(
        v, addr, &val, bytes, sh_ctxt);
}

static int 
hvm_emulate_cmpxchg(enum x86_segment seg,
                    unsigned long offset,
                    unsigned long old,
                    unsigned long new,
                    unsigned int bytes,
                    struct x86_emulate_ctxt *ctxt)
{
    struct sh_emulate_ctxt *sh_ctxt =
        container_of(ctxt, struct sh_emulate_ctxt, ctxt);
    struct vcpu *v = current;
    unsigned long addr;
    int rc;

    if ( !is_x86_user_segment(seg) )
        return X86EMUL_UNHANDLEABLE;

    rc = hvm_translate_linear_addr(
        seg, offset, bytes, hvm_access_write, sh_ctxt, &addr);
    if ( rc )
        return rc;

    return v->arch.paging.mode->shadow.x86_emulate_cmpxchg(
        v, addr, old, new, bytes, sh_ctxt);
}

static int 
hvm_emulate_cmpxchg8b(enum x86_segment seg,
                      unsigned long offset,
                      unsigned long old_lo,
                      unsigned long old_hi,
                      unsigned long new_lo,
                      unsigned long new_hi,
                      struct x86_emulate_ctxt *ctxt)
{
    struct sh_emulate_ctxt *sh_ctxt =
        container_of(ctxt, struct sh_emulate_ctxt, ctxt);
    struct vcpu *v = current;
    unsigned long addr;
    int rc;

    if ( !is_x86_user_segment(seg) )
        return X86EMUL_UNHANDLEABLE;

    rc = hvm_translate_linear_addr(
        seg, offset, 8, hvm_access_write, sh_ctxt, &addr);
    if ( rc )
        return rc;

    return v->arch.paging.mode->shadow.x86_emulate_cmpxchg8b(
        v, addr, old_lo, old_hi, new_lo, new_hi, sh_ctxt);
}

static struct x86_emulate_ops hvm_shadow_emulator_ops = {
    .read       = hvm_emulate_read,
    .insn_fetch = hvm_emulate_insn_fetch,
    .write      = hvm_emulate_write,
    .cmpxchg    = hvm_emulate_cmpxchg,
    .cmpxchg8b  = hvm_emulate_cmpxchg8b,
};

static int
pv_emulate_read(enum x86_segment seg,
                unsigned long offset,
                unsigned long *val,
                unsigned int bytes,
                struct x86_emulate_ctxt *ctxt)
{
    unsigned int rc;

    if ( !is_x86_user_segment(seg) )
        return X86EMUL_UNHANDLEABLE;

    *val = 0;
    if ( (rc = copy_from_user((void *)val, (void *)offset, bytes)) != 0 )
    {
        propagate_page_fault(offset + bytes - rc, 0); /* read fault */
        return X86EMUL_EXCEPTION;
    }

    return X86EMUL_OKAY;
}

static int
pv_emulate_write(enum x86_segment seg,
                 unsigned long offset,
                 unsigned long val,
                 unsigned int bytes,
                 struct x86_emulate_ctxt *ctxt)
{
    struct sh_emulate_ctxt *sh_ctxt =
        container_of(ctxt, struct sh_emulate_ctxt, ctxt);
    struct vcpu *v = current;
    if ( !is_x86_user_segment(seg) )
        return X86EMUL_UNHANDLEABLE;
    return v->arch.paging.mode->shadow.x86_emulate_write(
        v, offset, &val, bytes, sh_ctxt);
}

static int 
pv_emulate_cmpxchg(enum x86_segment seg,
                   unsigned long offset,
                   unsigned long old,
                   unsigned long new,
                   unsigned int bytes,
                   struct x86_emulate_ctxt *ctxt)
{
    struct sh_emulate_ctxt *sh_ctxt =
        container_of(ctxt, struct sh_emulate_ctxt, ctxt);
    struct vcpu *v = current;
    if ( !is_x86_user_segment(seg) )
        return X86EMUL_UNHANDLEABLE;
    return v->arch.paging.mode->shadow.x86_emulate_cmpxchg(
        v, offset, old, new, bytes, sh_ctxt);
}

static int 
pv_emulate_cmpxchg8b(enum x86_segment seg,
                     unsigned long offset,
                     unsigned long old_lo,
                     unsigned long old_hi,
                     unsigned long new_lo,
                     unsigned long new_hi,
                     struct x86_emulate_ctxt *ctxt)
{
    struct sh_emulate_ctxt *sh_ctxt =
        container_of(ctxt, struct sh_emulate_ctxt, ctxt);
    struct vcpu *v = current;
    if ( !is_x86_user_segment(seg) )
        return X86EMUL_UNHANDLEABLE;
    return v->arch.paging.mode->shadow.x86_emulate_cmpxchg8b(
        v, offset, old_lo, old_hi, new_lo, new_hi, sh_ctxt);
}

static struct x86_emulate_ops pv_shadow_emulator_ops = {
    .read       = pv_emulate_read,
    .insn_fetch = pv_emulate_read,
    .write      = pv_emulate_write,
    .cmpxchg    = pv_emulate_cmpxchg,
    .cmpxchg8b  = pv_emulate_cmpxchg8b,
};

struct x86_emulate_ops *shadow_init_emulation(
    struct sh_emulate_ctxt *sh_ctxt, struct cpu_user_regs *regs)
{
    struct segment_register *creg, *sreg;
    struct vcpu *v = current;
    unsigned long addr;

    sh_ctxt->ctxt.regs = regs;

    if ( !is_hvm_vcpu(v) )
    {
        sh_ctxt->ctxt.addr_size = sh_ctxt->ctxt.sp_size = BITS_PER_LONG;
        return &pv_shadow_emulator_ops;
    }

    /* Segment cache initialisation. Primed with CS. */
    sh_ctxt->valid_seg_regs = 0;
    creg = hvm_get_seg_reg(x86_seg_cs, sh_ctxt);

    /* Work out the emulation mode. */
    if ( hvm_long_mode_enabled(v) && creg->attr.fields.l )
    {
        sh_ctxt->ctxt.addr_size = sh_ctxt->ctxt.sp_size = 64;
    }
    else if ( regs->eflags & X86_EFLAGS_VM )
    {
        sh_ctxt->ctxt.addr_size = sh_ctxt->ctxt.sp_size = 16;
    }
    else
    {
        sreg = hvm_get_seg_reg(x86_seg_ss, sh_ctxt);
        sh_ctxt->ctxt.addr_size = creg->attr.fields.db ? 32 : 16;
        sh_ctxt->ctxt.sp_size   = sreg->attr.fields.db ? 32 : 16;
    }

    /* Attempt to prefetch whole instruction. */
    sh_ctxt->insn_buf_eip = regs->eip;
    sh_ctxt->insn_buf_bytes =
        (!hvm_translate_linear_addr(
            x86_seg_cs, regs->eip, sizeof(sh_ctxt->insn_buf),
            hvm_access_insn_fetch, sh_ctxt, &addr) &&
         !hvm_fetch_from_guest_virt_nofault(
             sh_ctxt->insn_buf, addr, sizeof(sh_ctxt->insn_buf)))
        ? sizeof(sh_ctxt->insn_buf) : 0;

    return &hvm_shadow_emulator_ops;
}

/* Update an initialized emulation context to prepare for the next 
 * instruction */
void shadow_continue_emulation(struct sh_emulate_ctxt *sh_ctxt, 
                               struct cpu_user_regs *regs)
{
    struct vcpu *v = current;
    unsigned long addr, diff;

    /* We don't refetch the segment bases, because we don't emulate
     * writes to segment registers */

    if ( is_hvm_vcpu(v) )
    {
        diff = regs->eip - sh_ctxt->insn_buf_eip;
        if ( diff > sh_ctxt->insn_buf_bytes )
        {
            /* Prefetch more bytes. */
            sh_ctxt->insn_buf_bytes =
                (!hvm_translate_linear_addr(
                    x86_seg_cs, regs->eip, sizeof(sh_ctxt->insn_buf),
                    hvm_access_insn_fetch, sh_ctxt, &addr) &&
                 !hvm_fetch_from_guest_virt_nofault(
                     sh_ctxt->insn_buf, addr, sizeof(sh_ctxt->insn_buf)))
                ? sizeof(sh_ctxt->insn_buf) : 0;
            sh_ctxt->insn_buf_eip = regs->eip;
        }
    }
}

/**************************************************************************/
/* Code for "promoting" a guest page to the point where the shadow code is
 * willing to let it be treated as a guest page table.  This generally
 * involves making sure there are no writable mappings available to the guest
 * for this page.
 */
void shadow_promote(struct vcpu *v, mfn_t gmfn, unsigned int type)
{
    struct page_info *page = mfn_to_page(gmfn);

    ASSERT(mfn_valid(gmfn));

    /* We should never try to promote a gmfn that has writeable mappings */
    ASSERT((page->u.inuse.type_info & PGT_type_mask) != PGT_writable_page
           || (page->u.inuse.type_info & PGT_count_mask) == 0
           || v->domain->is_shutting_down);

    /* Is the page already shadowed? */
    if ( !test_and_set_bit(_PGC_page_table, &page->count_info) )
        page->shadow_flags = 0;

    ASSERT(!test_bit(type, &page->shadow_flags));
    set_bit(type, &page->shadow_flags);
}

void shadow_demote(struct vcpu *v, mfn_t gmfn, u32 type)
{
    struct page_info *page = mfn_to_page(gmfn);

    ASSERT(test_bit(_PGC_page_table, &page->count_info));
    ASSERT(test_bit(type, &page->shadow_flags));

    clear_bit(type, &page->shadow_flags);

    if ( (page->shadow_flags & SHF_page_type_mask) == 0 )
    {
        /* tlbflush timestamp field is valid again */
        page->tlbflush_timestamp = tlbflush_current_time();
        clear_bit(_PGC_page_table, &page->count_info);
    }
}

/**************************************************************************/
/* Validate a pagetable change from the guest and update the shadows.
 * Returns a bitmask of SHADOW_SET_* flags. */

int
sh_validate_guest_entry(struct vcpu *v, mfn_t gmfn, void *entry, u32 size)
{
    int result = 0;
    struct page_info *page = mfn_to_page(gmfn);

    paging_mark_dirty(v->domain, mfn_x(gmfn));
    
    // Determine which types of shadows are affected, and update each.
    //
    // Always validate L1s before L2s to prevent another cpu with a linear
    // mapping of this gmfn from seeing a walk that results from 
    // using the new L2 value and the old L1 value.  (It is OK for such a
    // guest to see a walk that uses the old L2 value with the new L1 value,
    // as hardware could behave this way if one level of the pagewalk occurs
    // before the store, and the next level of the pagewalk occurs after the
    // store.
    //
    // Ditto for L2s before L3s, etc.
    //

    if ( !(page->count_info & PGC_page_table) )
        return 0;  /* Not shadowed at all */

#if CONFIG_PAGING_LEVELS == 2
    if ( page->shadow_flags & SHF_L1_32 ) 
        result |= SHADOW_INTERNAL_NAME(sh_map_and_validate_gl1e, 2, 2)
            (v, gmfn, entry, size);
#else 
    if ( page->shadow_flags & SHF_L1_32 ) 
        result |= SHADOW_INTERNAL_NAME(sh_map_and_validate_gl1e, 3, 2)
            (v, gmfn, entry, size);
#endif

#if CONFIG_PAGING_LEVELS == 2
    if ( page->shadow_flags & SHF_L2_32 ) 
        result |= SHADOW_INTERNAL_NAME(sh_map_and_validate_gl2e, 2, 2)
            (v, gmfn, entry, size);
#else 
    if ( page->shadow_flags & SHF_L2_32 ) 
        result |= SHADOW_INTERNAL_NAME(sh_map_and_validate_gl2e, 3, 2)
            (v, gmfn, entry, size);
#endif

#if CONFIG_PAGING_LEVELS >= 3 
    if ( page->shadow_flags & SHF_L1_PAE ) 
        result |= SHADOW_INTERNAL_NAME(sh_map_and_validate_gl1e, 3, 3)
            (v, gmfn, entry, size);
    if ( page->shadow_flags & SHF_L2_PAE ) 
        result |= SHADOW_INTERNAL_NAME(sh_map_and_validate_gl2e, 3, 3)
            (v, gmfn, entry, size);
    if ( page->shadow_flags & SHF_L2H_PAE ) 
        result |= SHADOW_INTERNAL_NAME(sh_map_and_validate_gl2he, 3, 3)
            (v, gmfn, entry, size);
#else /* 32-bit non-PAE hypervisor does not support PAE guests */
    ASSERT((page->shadow_flags & (SHF_L2H_PAE|SHF_L2_PAE|SHF_L1_PAE)) == 0);
#endif

#if CONFIG_PAGING_LEVELS >= 4 
    if ( page->shadow_flags & SHF_L1_64 ) 
        result |= SHADOW_INTERNAL_NAME(sh_map_and_validate_gl1e, 4, 4)
            (v, gmfn, entry, size);
    if ( page->shadow_flags & SHF_L2_64 ) 
        result |= SHADOW_INTERNAL_NAME(sh_map_and_validate_gl2e, 4, 4)
            (v, gmfn, entry, size);
    if ( page->shadow_flags & SHF_L2H_64 ) 
        result |= SHADOW_INTERNAL_NAME(sh_map_and_validate_gl2he, 4, 4)
            (v, gmfn, entry, size);
    if ( page->shadow_flags & SHF_L3_64 ) 
        result |= SHADOW_INTERNAL_NAME(sh_map_and_validate_gl3e, 4, 4)
            (v, gmfn, entry, size);
    if ( page->shadow_flags & SHF_L4_64 ) 
        result |= SHADOW_INTERNAL_NAME(sh_map_and_validate_gl4e, 4, 4)
            (v, gmfn, entry, size);
#else /* 32-bit/PAE hypervisor does not support 64-bit guests */
    ASSERT((page->shadow_flags 
            & (SHF_L4_64|SHF_L3_64|SHF_L2H_64|SHF_L2_64|SHF_L1_64)) == 0);
#endif

    return result;
}


void
sh_validate_guest_pt_write(struct vcpu *v, mfn_t gmfn,
                           void *entry, u32 size)
/* This is the entry point for emulated writes to pagetables in HVM guests and
 * PV translated guests.
 */
{
    struct domain *d = v->domain;
    int rc;

    ASSERT(shadow_locked_by_me(v->domain));
    rc = sh_validate_guest_entry(v, gmfn, entry, size);
    if ( rc & SHADOW_SET_FLUSH )
        /* Need to flush TLBs to pick up shadow PT changes */
        flush_tlb_mask(d->domain_dirty_cpumask);
    if ( rc & SHADOW_SET_ERROR ) 
    {
        /* This page is probably not a pagetable any more: tear it out of the 
         * shadows, along with any tables that reference it.  
         * Since the validate call above will have made a "safe" (i.e. zero) 
         * shadow entry, we can let the domain live even if we can't fully 
         * unshadow the page. */
        sh_remove_shadows(v, gmfn, 0, 0);
    }
}

int shadow_write_guest_entry(struct vcpu *v, intpte_t *p,
                             intpte_t new, mfn_t gmfn)
/* Write a new value into the guest pagetable, and update the shadows 
 * appropriately.  Returns 0 if we page-faulted, 1 for success. */
{
    int failed;
    shadow_lock(v->domain);

    /* Do CoW before write occurs */
    cow_copy_page(v->domain, gmfn);

    failed = __copy_to_user(p, &new, sizeof(new));
    if ( failed != sizeof(new) )
        sh_validate_guest_entry(v, gmfn, p, sizeof(new));
    shadow_unlock(v->domain);
    return (failed == 0);
}

int shadow_cmpxchg_guest_entry(struct vcpu *v, intpte_t *p,
                               intpte_t *old, intpte_t new, mfn_t gmfn)
/* Cmpxchg a new value into the guest pagetable, and update the shadows 
 * appropriately. Returns 0 if we page-faulted, 1 if not.
 * N.B. caller should check the value of "old" to see if the
 * cmpxchg itself was successful. */
{
    int failed;
    intpte_t t = *old;
    shadow_lock(v->domain);

    /* Do CoW before write occurs */
    cow_copy_page(v->domain, gmfn);

    failed = cmpxchg_user(p, t, new);
    if ( t == *old )
        sh_validate_guest_entry(v, gmfn, p, sizeof(new));
    *old = t;
    shadow_unlock(v->domain);
    return (failed == 0);
}


/**************************************************************************/
/* Memory management for shadow pages. */ 

/* Allocating shadow pages
 * -----------------------
 *
 * Most shadow pages are allocated singly, but there is one case where
 * we need to allocate multiple pages together: shadowing 32-bit guest
 * tables on PAE or 64-bit shadows.  A 32-bit guest l1 table covers 4MB
 * of virtuial address space, and needs to be shadowed by two PAE/64-bit
 * l1 tables (covering 2MB of virtual address space each).  Similarly, a
 * 32-bit guest l2 table (4GB va) needs to be shadowed by four
 * PAE/64-bit l2 tables (1GB va each).  These multi-page shadows are
 * contiguous and aligned; functions for handling offsets into them are
 * defined in shadow.c (shadow_l1_index() etc.)
 *    
 * This table shows the allocation behaviour of the different modes:
 *
 * Xen paging      32b  pae  pae  64b  64b  64b
 * Guest paging    32b  32b  pae  32b  pae  64b
 * PV or HVM        *   HVM   *   HVM  HVM   * 
 * Shadow paging   32b  pae  pae  pae  pae  64b
 *
 * sl1 size         4k   8k   4k   8k   4k   4k
 * sl2 size         4k  16k   4k  16k   4k   4k
 * sl3 size         -    -    -    -    -    4k
 * sl4 size         -    -    -    -    -    4k
 *
 * We allocate memory from xen in four-page units and break them down
 * with a simple buddy allocator.  Can't use the xen allocator to handle
 * this as it only works for contiguous zones, and a domain's shadow
 * pool is made of fragments.
 *
 * In HVM guests, the p2m table is built out of shadow pages, and we provide 
 * a function for the p2m management to steal pages, in max-order chunks, from 
 * the free pool.  We don't provide for giving them back, yet.
 */

/* Figure out the least acceptable quantity of shadow memory.
 * The minimum memory requirement for always being able to free up a
 * chunk of memory is very small -- only three max-order chunks per
 * vcpu to hold the top level shadows and pages with Xen mappings in them.  
 *
 * But for a guest to be guaranteed to successfully execute a single
 * instruction, we must be able to map a large number (about thirty) VAs
 * at the same time, which means that to guarantee progress, we must
 * allow for more than ninety allocated pages per vcpu.  We round that
 * up to 128 pages, or half a megabyte per vcpu. */
static unsigned int shadow_min_acceptable_pages(struct domain *d) 
{
    u32 vcpu_count = 0;
    struct vcpu *v;

    for_each_vcpu(d, v)
        vcpu_count++;

    return (vcpu_count * 128);
} 

/* Figure out the order of allocation needed for a given shadow type */
static inline u32
shadow_order(unsigned int shadow_type) 
{
#if CONFIG_PAGING_LEVELS > 2
    static const u32 type_to_order[SH_type_unused] = {
        0, /* SH_type_none           */
        1, /* SH_type_l1_32_shadow   */
        1, /* SH_type_fl1_32_shadow  */
        2, /* SH_type_l2_32_shadow   */
        0, /* SH_type_l1_pae_shadow  */
        0, /* SH_type_fl1_pae_shadow */
        0, /* SH_type_l2_pae_shadow  */
        0, /* SH_type_l2h_pae_shadow */
        0, /* SH_type_l1_64_shadow   */
        0, /* SH_type_fl1_64_shadow  */
        0, /* SH_type_l2_64_shadow   */
        0, /* SH_type_l2h_64_shadow  */
        0, /* SH_type_l3_64_shadow   */
        0, /* SH_type_l4_64_shadow   */
        2, /* SH_type_p2m_table      */
        0  /* SH_type_monitor_table  */
        };
    ASSERT(shadow_type < SH_type_unused);
    return type_to_order[shadow_type];
#else  /* 32-bit Xen only ever shadows 32-bit guests on 32-bit shadows. */
    return 0;
#endif
}

static inline unsigned int
shadow_max_order(struct domain *d)
{
    return is_hvm_domain(d) ? SHADOW_MAX_ORDER : 0;
}

/* Do we have at total of count pages of the requested order free? */
static inline int space_is_available(
    struct domain *d,
    unsigned int order,
    unsigned int count)
{
    for ( ; order <= shadow_max_order(d); ++order )
    {
        unsigned int n = count;
        const struct list_head *p;

        list_for_each ( p, &d->arch.paging.shadow.freelists[order] )
            if ( --n == 0 )
                return 1;
        count = (count + 1) >> 1;
    }

    return 0;
}

/* Dispatcher function: call the per-mode function that will unhook the
 * non-Xen mappings in this top-level shadow mfn */
static void shadow_unhook_mappings(struct vcpu *v, mfn_t smfn)
{
    struct shadow_page_info *sp = mfn_to_shadow_page(smfn);
    switch ( sp->type )
    {
    case SH_type_l2_32_shadow:
#if CONFIG_PAGING_LEVELS == 2
        SHADOW_INTERNAL_NAME(sh_unhook_32b_mappings,2,2)(v,smfn);
#else
        SHADOW_INTERNAL_NAME(sh_unhook_32b_mappings,3,2)(v,smfn);
#endif
        break;
#if CONFIG_PAGING_LEVELS >= 3
    case SH_type_l2_pae_shadow:
    case SH_type_l2h_pae_shadow:
        SHADOW_INTERNAL_NAME(sh_unhook_pae_mappings,3,3)(v,smfn);
        break;
#endif
#if CONFIG_PAGING_LEVELS >= 4
    case SH_type_l4_64_shadow:
        SHADOW_INTERNAL_NAME(sh_unhook_64b_mappings,4,4)(v,smfn);
        break;
#endif
    default:
        SHADOW_ERROR("top-level shadow has bad type %08x\n", sp->type);
        BUG();
    }
}


/* Make sure there are at least count order-sized pages
 * available in the shadow page pool. */
static void _shadow_prealloc(
    struct domain *d,
    unsigned int order,
    unsigned int count)
{
    /* Need a vpcu for calling unpins; for now, since we don't have
     * per-vcpu shadows, any will do */
    struct vcpu *v, *v2;
    struct list_head *l, *t;
    struct shadow_page_info *sp;
    mfn_t smfn;
    int i;

    ASSERT(order <= shadow_max_order(d));
    if ( space_is_available(d, order, count) ) return;
    
    v = current;
    if ( v->domain != d )
        v = d->vcpu[0];
    ASSERT(v != NULL); /* Shouldn't have enabled shadows if we've no vcpus  */

    /* Stage one: walk the list of pinned pages, unpinning them */
    perfc_incr(shadow_prealloc_1);
    list_for_each_backwards_safe(l, t, &d->arch.paging.shadow.pinned_shadows)
    {
        sp = list_entry(l, struct shadow_page_info, list);
        smfn = shadow_page_to_mfn(sp);

        /* Unpin this top-level shadow */
        sh_unpin(v, smfn);

        /* See if that freed up enough space */
        if ( space_is_available(d, order, count) ) return;
    }

    /* Stage two: all shadow pages are in use in hierarchies that are
     * loaded in cr3 on some vcpu.  Walk them, unhooking the non-Xen
     * mappings. */
    perfc_incr(shadow_prealloc_2);

    for_each_vcpu(d, v2) 
        for ( i = 0 ; i < 4 ; i++ )
        {
            if ( !pagetable_is_null(v2->arch.shadow_table[i]) )
            {
                shadow_unhook_mappings(v, 
                               pagetable_get_mfn(v2->arch.shadow_table[i]));

                /* See if that freed up enough space */
                if ( space_is_available(d, order, count) )
                {
                    flush_tlb_mask(d->domain_dirty_cpumask);
                    return;
                }
            }
        }
    
    /* Nothing more we can do: all remaining shadows are of pages that
     * hold Xen mappings for some vcpu.  This can never happen. */
    SHADOW_ERROR("Can't pre-allocate %u order-%u shadow pages!\n"
                 "  shadow pages total = %u, free = %u, p2m=%u\n",
                 count, order,
                 d->arch.paging.shadow.total_pages,
                 d->arch.paging.shadow.free_pages,
                 d->arch.paging.shadow.p2m_pages);
    BUG();
}

/* Make sure there are at least count pages of the order according to
 * type available in the shadow page pool.
 * This must be called before any calls to shadow_alloc().  Since this
 * will free existing shadows to make room, it must be called early enough
 * to avoid freeing shadows that the caller is currently working on. */
void shadow_prealloc(struct domain *d, u32 type, unsigned int count)
{
    ASSERT(type != SH_type_p2m_table);
    return _shadow_prealloc(d, shadow_order(type), count);
}

/* Deliberately free all the memory we can: this will tear down all of
 * this domain's shadows */
static void shadow_blow_tables(struct domain *d) 
{
    struct list_head *l, *t;
    struct shadow_page_info *sp;
    struct vcpu *v = d->vcpu[0];
    mfn_t smfn;
    int i;

    ASSERT(v != NULL);

    /* Pass one: unpin all pinned pages */
    list_for_each_backwards_safe(l,t, &d->arch.paging.shadow.pinned_shadows)
    {
        sp = list_entry(l, struct shadow_page_info, list);
        smfn = shadow_page_to_mfn(sp);
        sh_unpin(v, smfn);
    }
        
    /* Second pass: unhook entries of in-use shadows */
    for_each_vcpu(d, v) 
        for ( i = 0 ; i < 4 ; i++ )
            if ( !pagetable_is_null(v->arch.shadow_table[i]) )
                shadow_unhook_mappings(v, 
                               pagetable_get_mfn(v->arch.shadow_table[i]));

    /* Make sure everyone sees the unshadowings */
    flush_tlb_mask(d->domain_dirty_cpumask);
}

void shadow_blow_tables_per_domain(struct domain *d)
{
    if ( shadow_mode_enabled(d) && d->vcpu[0] != NULL ) {
        shadow_lock(d);
        shadow_blow_tables(d);
        shadow_unlock(d);
    }
}

#ifndef NDEBUG
/* Blow all shadows of all shadowed domains: this can be used to cause the
 * guest's pagetables to be re-shadowed if we suspect that the shadows
 * have somehow got out of sync */
static void shadow_blow_all_tables(unsigned char c)
{
    struct domain *d;
    printk("'%c' pressed -> blowing all shadow tables\n", c);
    rcu_read_lock(&domlist_read_lock);
    for_each_domain(d)
    {
        if ( shadow_mode_enabled(d) && d->vcpu[0] != NULL )
        {
            shadow_lock(d);
            shadow_blow_tables(d);
            shadow_unlock(d);
        }
    }
    rcu_read_unlock(&domlist_read_lock);
}

/* Register this function in the Xen console keypress table */
static __init int shadow_blow_tables_keyhandler_init(void)
{
    register_keyhandler('S', shadow_blow_all_tables,"reset shadow pagetables");
    return 0;
}
__initcall(shadow_blow_tables_keyhandler_init);
#endif /* !NDEBUG */

/* Allocate another shadow's worth of (contiguous, aligned) pages,
 * and fill in the type and backpointer fields of their page_infos. 
 * Never fails to allocate. */
mfn_t shadow_alloc(struct domain *d,  
                    u32 shadow_type,
                    unsigned long backpointer)
{
    struct shadow_page_info *sp = NULL;
    unsigned int order = shadow_order(shadow_type);
    cpumask_t mask;
    void *p;
    int i;

    ASSERT(shadow_locked_by_me(d));
    if (shadow_type == SH_type_p2m_table && order > shadow_max_order(d))
        order = shadow_max_order(d);
    ASSERT(order <= shadow_max_order(d));
    ASSERT(shadow_type != SH_type_none);
    perfc_incr(shadow_alloc);

    /* Find smallest order which can satisfy the request. */
    for ( i = order; i <= SHADOW_MAX_ORDER; i++ )
        if ( !list_empty(&d->arch.paging.shadow.freelists[i]) )
            goto found;
    
    /* If we get here, we failed to allocate. This should never happen.
     * It means that we didn't call shadow_prealloc() correctly before
     * we allocated.  We can't recover by calling prealloc here, because
     * we might free up higher-level pages that the caller is working on. */
    SHADOW_ERROR("Can't allocate %i shadow pages!\n", 1 << order);
    BUG();

 found:
    sp = list_entry(d->arch.paging.shadow.freelists[i].next, 
                    struct shadow_page_info, list);
    list_del(&sp->list);
            
    /* We may have to halve the chunk a number of times. */
    while ( i != order )
    {
        i--;
        sp->order = i;
        list_add_tail(&sp->list, &d->arch.paging.shadow.freelists[i]);
        sp += 1 << i;
    }
    d->arch.paging.shadow.free_pages -= 1 << order;

    /* Init page info fields and clear the pages */
    for ( i = 0; i < 1<<order ; i++ ) 
    {
        /* Before we overwrite the old contents of this page, 
         * we need to be sure that no TLB holds a pointer to it. */
        mask = d->domain_dirty_cpumask;
        tlbflush_filter(mask, sp[i].tlbflush_timestamp);
        if ( unlikely(!cpus_empty(mask)) )
        {
            perfc_incr(shadow_alloc_tlbflush);
            flush_tlb_mask(mask);
        }
        /* Now safe to clear the page for reuse */
        p = sh_map_domain_page(shadow_page_to_mfn(sp+i));
        ASSERT(p != NULL);
        clear_page(p);
        sh_unmap_domain_page(p);
        INIT_LIST_HEAD(&sp[i].list);
        sp[i].type = shadow_type;
        sp[i].pinned = 0;
        sp[i].count = 0;
        sp[i].backpointer = backpointer;
        sp[i].next_shadow = NULL;
        perfc_incr(shadow_alloc_count);
    }
    return shadow_page_to_mfn(sp);
}


/* Return some shadow pages to the pool. */
void shadow_free(struct domain *d, mfn_t smfn)
{
    struct shadow_page_info *sp = mfn_to_shadow_page(smfn); 
    u32 shadow_type;
    unsigned long order;
    unsigned long mask;
    int i;

    ASSERT(shadow_locked_by_me(d));
    perfc_incr(shadow_free);

    shadow_type = sp->type;
    ASSERT(shadow_type != SH_type_none);
    ASSERT(shadow_type != SH_type_p2m_table);
    order = shadow_order(shadow_type);

    d->arch.paging.shadow.free_pages += 1 << order;

    for ( i = 0; i < 1<<order; i++ ) 
    {
#if SHADOW_OPTIMIZATIONS & SHOPT_WRITABLE_HEURISTIC
        struct vcpu *v;
        for_each_vcpu(d, v) 
        {
            /* No longer safe to look for a writeable mapping in this shadow */
            if ( v->arch.paging.shadow.last_writeable_pte_smfn == mfn_x(smfn) + i ) 
                v->arch.paging.shadow.last_writeable_pte_smfn = 0;
        }
#endif
        /* Strip out the type: this is now a free shadow page */
        sp[i].type = 0;
        /* Remember the TLB timestamp so we will know whether to flush 
         * TLBs when we reuse the page.  Because the destructors leave the
         * contents of the pages in place, we can delay TLB flushes until
         * just before the allocator hands the page out again. */
        sp[i].tlbflush_timestamp = tlbflush_current_time();
        perfc_decr(shadow_alloc_count);
    }

    /* Merge chunks as far as possible. */
    for ( ; order < shadow_max_order(d); ++order )
    {
        mask = 1 << order;
        if ( (mfn_x(shadow_page_to_mfn(sp)) & mask) ) {
            /* Merge with predecessor block? */
            if ( ((sp-mask)->type != PGT_none) || ((sp-mask)->order != order) )
                break;
            list_del(&(sp-mask)->list);
            sp -= mask;
        } else {
            /* Merge with successor block? */
            if ( ((sp+mask)->type != PGT_none) || ((sp+mask)->order != order) )
                break;
            list_del(&(sp+mask)->list);
        }
    }

    sp->order = order;
    list_add_tail(&sp->list, &d->arch.paging.shadow.freelists[order]);
}

/* Divert some memory from the pool to be used by the p2m mapping.
 * This action is irreversible: the p2m mapping only ever grows.
 * That's OK because the p2m table only exists for translated domains,
 * and those domains can't ever turn off shadow mode.
 * Also, we only ever allocate a max-order chunk, so as to preserve
 * the invariant that shadow_prealloc() always works.
 * Returns 0 iff it can't get a chunk (the caller should then
 * free up some pages in domheap and call sh_set_allocation);
 * returns non-zero on success.
 */
static int
sh_alloc_p2m_pages(struct domain *d)
{
    struct page_info *pg;
    u32 i;
    unsigned int order = shadow_max_order(d);

    ASSERT(shadow_locked_by_me(d));
    
    if ( d->arch.paging.shadow.total_pages 
         < (shadow_min_acceptable_pages(d) + (1 << order)) )
        return 0; /* Not enough shadow memory: need to increase it first */
    
    pg = mfn_to_page(shadow_alloc(d, SH_type_p2m_table, 0));
    d->arch.paging.shadow.p2m_pages += (1 << order);
    d->arch.paging.shadow.total_pages -= (1 << order);
    for (i = 0; i < (1U << order); i++)
    {
        /* Unlike shadow pages, mark p2m pages as owned by the domain.
         * Marking the domain as the owner would normally allow the guest to
         * create mappings of these pages, but these p2m pages will never be
         * in the domain's guest-physical address space, and so that is not
         * believed to be a concern.
         */
        page_set_owner(&pg[i], d);
        pg[i].count_info = 1;
        list_add_tail(&pg[i].list, &d->arch.paging.shadow.p2m_freelist);
    }
    return 1;
}

// Returns 0 if no memory is available...
static struct page_info *
shadow_alloc_p2m_page(struct domain *d)
{
    struct list_head *entry;
    struct page_info *pg;
    mfn_t mfn;
    void *p;
    
    shadow_lock(d);

    if ( list_empty(&d->arch.paging.shadow.p2m_freelist) &&
         !sh_alloc_p2m_pages(d) )
    {
        shadow_unlock(d);
        return NULL;
    }
    entry = d->arch.paging.shadow.p2m_freelist.next;
    list_del(entry);

    shadow_unlock(d);

    pg = list_entry(entry, struct page_info, list);
    mfn = page_to_mfn(pg);
    p = sh_map_domain_page(mfn);
    clear_page(p);
    sh_unmap_domain_page(p);

    return pg;
}

static void
shadow_free_p2m_page(struct domain *d, struct page_info *pg)
{
    ASSERT(page_get_owner(pg) == d);
    /* Should have just the one ref we gave it in alloc_p2m_page() */
    if ( (pg->count_info & PGC_count_mask) != 1 )
    {
        SHADOW_ERROR("Odd p2m page count c=%#x t=%"PRtype_info"\n",
                     pg->count_info, pg->u.inuse.type_info);
    }
    pg->count_info = 0;
    /* Free should not decrement domain's total allocation, since 
     * these pages were allocated without an owner. */
    page_set_owner(pg, NULL); 
    free_domheap_pages(pg, 0);
    d->arch.paging.shadow.p2m_pages--;
    perfc_decr(shadow_alloc_count);
}

#if CONFIG_PAGING_LEVELS == 3
static void p2m_install_entry_in_monitors(struct domain *d, 
                                          l3_pgentry_t *l3e) 
/* Special case, only used for external-mode domains on PAE hosts:
 * update the mapping of the p2m table.  Once again, this is trivial in
 * other paging modes (one top-level entry points to the top-level p2m,
 * no maintenance needed), but PAE makes life difficult by needing a
 * copy the eight l3es of the p2m table in eight l2h slots in the
 * monitor table.  This function makes fresh copies when a p2m l3e
 * changes. */
{
    l2_pgentry_t *ml2e;
    struct vcpu *v;
    unsigned int index;

    index = ((unsigned long)l3e & ~PAGE_MASK) / sizeof(l3_pgentry_t);
    ASSERT(index < MACHPHYS_MBYTES>>1);

    for_each_vcpu(d, v) 
    {
        if ( pagetable_get_pfn(v->arch.monitor_table) == 0 ) 
            continue;
        ASSERT(shadow_mode_external(v->domain));

        SHADOW_DEBUG(P2M, "d=%u v=%u index=%u mfn=%#lx\n",
                      d->domain_id, v->vcpu_id, index, l3e_get_pfn(*l3e));

        if ( v == current ) /* OK to use linear map of monitor_table */
            ml2e = __linear_l2_table + l2_linear_offset(RO_MPT_VIRT_START);
        else 
        {
            l3_pgentry_t *ml3e;
            ml3e = sh_map_domain_page(pagetable_get_mfn(v->arch.monitor_table));
            ASSERT(l3e_get_flags(ml3e[3]) & _PAGE_PRESENT);
            ml2e = sh_map_domain_page(_mfn(l3e_get_pfn(ml3e[3])));
            ml2e += l2_table_offset(RO_MPT_VIRT_START);
            sh_unmap_domain_page(ml3e);
        }
        ml2e[index] = l2e_from_pfn(l3e_get_pfn(*l3e), __PAGE_HYPERVISOR);
        if ( v != current )
            sh_unmap_domain_page(ml2e);
    }
}
#endif

/* Set the pool of shadow pages to the required number of pages.
 * Input will be rounded up to at least shadow_min_acceptable_pages(),
 * plus space for the p2m table.
 * Returns 0 for success, non-zero for failure. */
static unsigned int sh_set_allocation(struct domain *d, 
                                      unsigned int pages,
                                      int *preempted)
{
    struct shadow_page_info *sp;
    unsigned int lower_bound;
    unsigned int j, order = shadow_max_order(d);

    ASSERT(shadow_locked_by_me(d));
    
    /* Don't allocate less than the minimum acceptable, plus one page per
     * megabyte of RAM (for the p2m table) */
    lower_bound = shadow_min_acceptable_pages(d) + (d->tot_pages / 256);
    if ( pages > 0 && pages < lower_bound )
        pages = lower_bound;
    /* Round up to largest block size */
    pages = (pages + ((1<<SHADOW_MAX_ORDER)-1)) & ~((1<<SHADOW_MAX_ORDER)-1);

    SHADOW_PRINTK("current %i target %i\n", 
                   d->arch.paging.shadow.total_pages, pages);

    while ( d->arch.paging.shadow.total_pages != pages ) 
    {
        if ( d->arch.paging.shadow.total_pages < pages ) 
        {
            /* Need to allocate more memory from domheap */
            sp = (struct shadow_page_info *)
                alloc_domheap_pages(NULL, order, 0);
            if ( sp == NULL ) 
            { 
                SHADOW_PRINTK("failed to allocate shadow pages.\n");
                return -ENOMEM;
            }
            d->arch.paging.shadow.free_pages += 1 << order;
            d->arch.paging.shadow.total_pages += 1 << order;
            for ( j = 0; j < 1U << order; j++ )
            {
                sp[j].type = 0;  
                sp[j].pinned = 0;
                sp[j].count = 0;
                sp[j].mbz = 0;
                sp[j].tlbflush_timestamp = 0; /* Not in any TLB */
            }
            sp->order = order;
            list_add_tail(&sp->list, &d->arch.paging.shadow.freelists[order]);
        } 
        else if ( d->arch.paging.shadow.total_pages > pages ) 
        {
            /* Need to return memory to domheap */
            _shadow_prealloc(d, order, 1);
            ASSERT(!list_empty(&d->arch.paging.shadow.freelists[order]));
            sp = list_entry(d->arch.paging.shadow.freelists[order].next,
                            struct shadow_page_info, list);
            list_del(&sp->list);
            d->arch.paging.shadow.free_pages -= 1 << order;
            d->arch.paging.shadow.total_pages -= 1 << order;
            free_domheap_pages((struct page_info *)sp, order);
        }

        /* Check to see if we need to yield and try again */
        if ( preempted && hypercall_preempt_check() )
        {
            *preempted = 1;
            return 0;
        }
    }

    return 0;
}

/* Return the size of the shadow pool, rounded up to the nearest MB */
static unsigned int shadow_get_allocation(struct domain *d)
{
    unsigned int pg = d->arch.paging.shadow.total_pages;
    return ((pg >> (20 - PAGE_SHIFT))
            + ((pg & ((1 << (20 - PAGE_SHIFT)) - 1)) ? 1 : 0));
}

/**************************************************************************/
/* Hash table for storing the guest->shadow mappings.
 * The table itself is an array of pointers to shadows; the shadows are then 
 * threaded on a singly-linked list of shadows with the same hash value */

#define SHADOW_HASH_BUCKETS 251
/* Other possibly useful primes are 509, 1021, 2039, 4093, 8191, 16381 */

/* Hash function that takes a gfn or mfn, plus another byte of type info */
typedef u32 key_t;
static inline key_t sh_hash(unsigned long n, unsigned int t) 
{
    unsigned char *p = (unsigned char *)&n;
    key_t k = t;
    int i;
    for ( i = 0; i < sizeof(n) ; i++ ) k = (u32)p[i] + (k<<6) + (k<<16) - k;
    return k % SHADOW_HASH_BUCKETS;
}

#if SHADOW_AUDIT & (SHADOW_AUDIT_HASH|SHADOW_AUDIT_HASH_FULL)

/* Before we get to the mechanism, define a pair of audit functions
 * that sanity-check the contents of the hash table. */
static void sh_hash_audit_bucket(struct domain *d, int bucket)
/* Audit one bucket of the hash table */
{
    struct shadow_page_info *sp, *x;

    if ( !(SHADOW_AUDIT_ENABLE) )
        return;

    sp = d->arch.paging.shadow.hash_table[bucket];
    while ( sp )
    {
        /* Not a shadow? */
        BUG_ON( sp->mbz != 0 );
        /* Bogus type? */
        BUG_ON( sp->type == 0 ); 
        BUG_ON( sp->type > SH_type_max_shadow );
        /* Wrong bucket? */
        BUG_ON( sh_hash(sp->backpointer, sp->type) != bucket ); 
        /* Duplicate entry? */
        for ( x = sp->next_shadow; x; x = x->next_shadow )
            BUG_ON( x->backpointer == sp->backpointer && x->type == sp->type );
        /* Follow the backpointer to the guest pagetable */
        if ( sp->type != SH_type_fl1_32_shadow
             && sp->type != SH_type_fl1_pae_shadow
             && sp->type != SH_type_fl1_64_shadow )
        {
            struct page_info *gpg = mfn_to_page(_mfn(sp->backpointer));
            /* Bad shadow flags on guest page? */
            BUG_ON( !(gpg->shadow_flags & (1<<sp->type)) );
            /* Bad type count on guest page? */
            if ( (gpg->u.inuse.type_info & PGT_type_mask) == PGT_writable_page 
                 && (gpg->u.inuse.type_info & PGT_count_mask) != 0 )
            {
                SHADOW_ERROR("MFN %#lx shadowed (by %#"PRI_mfn")"
                             " but has typecount %#lx\n",
                             sp->backpointer, mfn_x(shadow_page_to_mfn(sp)), 
                             gpg->u.inuse.type_info);
                BUG();
            }
        }
        /* That entry was OK; on we go */
        sp = sp->next_shadow;
    }
}

#else
#define sh_hash_audit_bucket(_d, _b) do {} while(0)
#endif /* Hashtable bucket audit */


#if SHADOW_AUDIT & SHADOW_AUDIT_HASH_FULL

static void sh_hash_audit(struct domain *d)
/* Full audit: audit every bucket in the table */
{
    int i;

    if ( !(SHADOW_AUDIT_ENABLE) )
        return;

    for ( i = 0; i < SHADOW_HASH_BUCKETS; i++ ) 
    {
        sh_hash_audit_bucket(d, i);
    }
}

#else
#define sh_hash_audit(_d) do {} while(0)
#endif /* Hashtable bucket audit */

/* Allocate and initialise the table itself.  
 * Returns 0 for success, 1 for error. */
static int shadow_hash_alloc(struct domain *d)
{
    struct shadow_page_info **table;

    ASSERT(shadow_locked_by_me(d));
    ASSERT(!d->arch.paging.shadow.hash_table);

    table = xmalloc_array(struct shadow_page_info *, SHADOW_HASH_BUCKETS);
    if ( !table ) return 1;
    memset(table, 0, 
           SHADOW_HASH_BUCKETS * sizeof (struct shadow_page_info *));
    d->arch.paging.shadow.hash_table = table;
    return 0;
}

/* Tear down the hash table and return all memory to Xen.
 * This function does not care whether the table is populated. */
static void shadow_hash_teardown(struct domain *d)
{
    ASSERT(shadow_locked_by_me(d));
    ASSERT(d->arch.paging.shadow.hash_table);

    xfree(d->arch.paging.shadow.hash_table);
    d->arch.paging.shadow.hash_table = NULL;
}


mfn_t shadow_hash_lookup(struct vcpu *v, unsigned long n, unsigned int t)
/* Find an entry in the hash table.  Returns the MFN of the shadow,
 * or INVALID_MFN if it doesn't exist */
{
    struct domain *d = v->domain;
    struct shadow_page_info *sp, *prev;
    key_t key;

    ASSERT(shadow_locked_by_me(d));
    ASSERT(d->arch.paging.shadow.hash_table);
    ASSERT(t);

    sh_hash_audit(d);

    perfc_incr(shadow_hash_lookups);
    key = sh_hash(n, t);
    sh_hash_audit_bucket(d, key);

    sp = d->arch.paging.shadow.hash_table[key];
    prev = NULL;
    while(sp)
    {
        if ( sp->backpointer == n && sp->type == t )
        {
            /* Pull-to-front if 'sp' isn't already the head item */
            if ( unlikely(sp != d->arch.paging.shadow.hash_table[key]) )
            {
                if ( unlikely(d->arch.paging.shadow.hash_walking != 0) )
                    /* Can't reorder: someone is walking the hash chains */
                    return shadow_page_to_mfn(sp);
                else 
                {
                    ASSERT(prev);
                    /* Delete sp from the list */
                    prev->next_shadow = sp->next_shadow;                    
                    /* Re-insert it at the head of the list */
                    sp->next_shadow = d->arch.paging.shadow.hash_table[key];
                    d->arch.paging.shadow.hash_table[key] = sp;
                }
            }
            else
            {
                perfc_incr(shadow_hash_lookup_head);
            }
            return shadow_page_to_mfn(sp);
        }
        prev = sp;
        sp = sp->next_shadow;
    }

    perfc_incr(shadow_hash_lookup_miss);
    return _mfn(INVALID_MFN);
}

void shadow_hash_insert(struct vcpu *v, unsigned long n, unsigned int t, 
                        mfn_t smfn)
/* Put a mapping (n,t)->smfn into the hash table */
{
    struct domain *d = v->domain;
    struct shadow_page_info *sp;
    key_t key;
    
    ASSERT(shadow_locked_by_me(d));
    ASSERT(d->arch.paging.shadow.hash_table);
    ASSERT(t);

    sh_hash_audit(d);

    perfc_incr(shadow_hash_inserts);
    key = sh_hash(n, t);
    sh_hash_audit_bucket(d, key);
    
    /* Insert this shadow at the top of the bucket */
    sp = mfn_to_shadow_page(smfn);
    sp->next_shadow = d->arch.paging.shadow.hash_table[key];
    d->arch.paging.shadow.hash_table[key] = sp;
    
    sh_hash_audit_bucket(d, key);
}

void shadow_hash_delete(struct vcpu *v, unsigned long n, unsigned int t, 
                        mfn_t smfn)
/* Excise the mapping (n,t)->smfn from the hash table */
{
    struct domain *d = v->domain;
    struct shadow_page_info *sp, *x;
    key_t key;

    ASSERT(shadow_locked_by_me(d));
    ASSERT(d->arch.paging.shadow.hash_table);
    ASSERT(t);

    sh_hash_audit(d);

    perfc_incr(shadow_hash_deletes);
    key = sh_hash(n, t);
    sh_hash_audit_bucket(d, key);
    
    sp = mfn_to_shadow_page(smfn);
    if ( d->arch.paging.shadow.hash_table[key] == sp ) 
        /* Easy case: we're deleting the head item. */
        d->arch.paging.shadow.hash_table[key] = sp->next_shadow;
    else 
    {
        /* Need to search for the one we want */
        x = d->arch.paging.shadow.hash_table[key];
        while ( 1 )
        {
            ASSERT(x); /* We can't have hit the end, since our target is
                        * still in the chain somehwere... */
            if ( x->next_shadow == sp ) 
            {
                x->next_shadow = sp->next_shadow;
                break;
            }
            x = x->next_shadow;
        }
    }
    sp->next_shadow = NULL;

    sh_hash_audit_bucket(d, key);
}

typedef int (*hash_callback_t)(struct vcpu *v, mfn_t smfn, mfn_t other_mfn);

static void hash_foreach(struct vcpu *v, 
                         unsigned int callback_mask, 
                         hash_callback_t callbacks[], 
                         mfn_t callback_mfn)
/* Walk the hash table looking at the types of the entries and 
 * calling the appropriate callback function for each entry. 
 * The mask determines which shadow types we call back for, and the array
 * of callbacks tells us which function to call.
 * Any callback may return non-zero to let us skip the rest of the scan. 
 *
 * WARNING: Callbacks MUST NOT add or remove hash entries unless they 
 * then return non-zero to terminate the scan. */
{
    int i, done = 0;
    struct domain *d = v->domain;
    struct shadow_page_info *x;

    /* Say we're here, to stop hash-lookups reordering the chains */
    ASSERT(shadow_locked_by_me(d));
    ASSERT(d->arch.paging.shadow.hash_walking == 0);
    d->arch.paging.shadow.hash_walking = 1;

    for ( i = 0; i < SHADOW_HASH_BUCKETS; i++ ) 
    {
        /* WARNING: This is not safe against changes to the hash table.
         * The callback *must* return non-zero if it has inserted or
         * deleted anything from the hash (lookups are OK, though). */
        for ( x = d->arch.paging.shadow.hash_table[i]; x; x = x->next_shadow )
        {
            if ( callback_mask & (1 << x->type) ) 
            {
                ASSERT(x->type <= 15);
                ASSERT(callbacks[x->type] != NULL);
                done = callbacks[x->type](v, shadow_page_to_mfn(x), 
                                          callback_mfn);
                if ( done ) break;
            }
        }
        if ( done ) break; 
    }
    d->arch.paging.shadow.hash_walking = 0; 
}


/**************************************************************************/
/* Inverted shadow hash table
 * Hash table for storing the mfn -> shadow L1 PTEs mappings. */
/*
static inline key_t invert_sh_hash(mfn_t mfn) 
{
    unsigned char *p = (unsigned char *) &mfn;
    key_t k = 1;
    int i;
    for (i = 0; i < sizeof(mfn); i++ ) 
        k = (u32)p[i] + (k<<6) + (k<<16) - k;
    return k % SHADOW_HASH_BUCKETS;
}

int invert_sh_table_alloc()
{
    struct invert_sh_entry **table;

    table = xmalloc_array(struct invert_sh_entry *, 
                          SHADOW_HASH_BUCKETS);
    if (!table) 
        return 1;
    memset(table, 0, 
           SHADOW_HASH_BUCKETS * sizeof(struct invert_sh_entry *));
    cow.invert_sh_table = table;

    printk("invert_sh_table allocated\n");

    return 0;
}

void invert_sh_table_teardown()
{
    printk("invert_sh_table_teardown()\n");
    if (cow.invert_sh_table != NULL)
    {
        int i;
        for (i = 0; i < SHADOW_HASH_BUCKETS; i++)
        {
            while (cow.invert_sh_table[i] != NULL)
            {
                struct invert_sh_entry *entry = cow.invert_sh_table[i];
                cow.invert_sh_table[i] = entry->next_entry;
                xfree(entry);
            }
        }
        xfree(cow.invert_sh_table);
    }
    cow.invert_sh_table = NULL;
}

struct invert_sh_entry * invert_sh_table_lookup(mfn_t mfn)
{
    struct invert_sh_entry *cur, *prev;
    key_t key;
    key = invert_sh_hash(mfn);

    if (cow.invert_sh_table == NULL)
        return NULL;

    cur = cow.invert_sh_table[key];
    prev = NULL;
    while (cur)
    {
        if (cur->mfn == mfn)
        {
            if (unlikely(cur != cow.invert_sh_table[key]) )
            {
                ASSERT(prev);
                prev->next_entry = cur->next_entry;                    
                cur->next_entry = cow.invert_sh_table[key];
                cow.invert_sh_table[key] = cur;
            }
            return cur;
        }
        prev = cur;
        cur = cur->next_entry;
    }
    return NULL;
}

void invert_sh_table_add_entry(mfn_t mfn, struct invert_sh_entry *entry)
{   
    key_t key = invert_sh_hash(mfn);

    ASSERT(cow.invert_sh_table != NULL);
    ASSERT(entry != NULL);
   
    entry->next_entry = cow.invert_sh_table[key];
    cow.invert_sh_table[key] = entry;
}

void invert_sh_table_insert(mfn_t mfn, mfn_t sl1mfn)
{
    struct invert_sh_entry *entry = NULL;

    if (!cow.invert_sh_table)
        invert_sh_table_alloc();
    else
        entry = invert_sh_table_lookup(mfn);
        
    if (!entry)
    {
        entry = (struct invert_sh_entry *) 
            xmalloc(struct invert_sh_entry);
                if (unlikely(!entry))
        {
            SHADOW_ERROR("Could not allocate invert_sh_entry\n");
            return;
        }
        entry->next_entry = NULL;
        entry->sl1_list = NULL;
        entry->mfn = mfn;
        invert_sh_table_add_entry(mfn, entry);
    }
    entry->sl1_list = sl1_list_insert(entry->sl1_list, sl1mfn);
}

void invert_sh_table_remove(mfn_t mfn, mfn_t sl1mfn)
{
    key_t key;
    struct invert_sh_entry *cur = NULL;
    struct invert_sh_entry *prev = NULL;

    if (cow.invert_sh_table == NULL)
        return;
    
        key = invert_sh_hash(mfn);
        cur = cow.invert_sh_table[key];
        prev = cur;
        while (cur != NULL)
        {
            if (cur->mfn == mfn)
            {
                cur->sl1_list = sl1_list_remove(cur->sl1_list, sl1mfn);
                if (cur->sl1_list == NULL)
                {
                    if (cur == cow.invert_sh_table[key])                
                        cow.invert_sh_table[key] = cur->next_entry;
                    else
                        prev->next_entry = cur->next_entry;
                    xfree(cur);
                }
                return;
            }
            prev = cur;
            cur = cur->next_entry;
        }
}
*/

/**************************************************************************/
/* Destroy a shadow page: simple dispatcher to call the per-type destructor
 * which will decrement refcounts appropriately and return memory to the 
 * free pool. */

void sh_destroy_shadow(struct vcpu *v, mfn_t smfn)
{
    struct shadow_page_info *sp = mfn_to_shadow_page(smfn);
    unsigned int t = sp->type;


    SHADOW_PRINTK("smfn=%#lx\n", mfn_x(smfn));

    /* Double-check, if we can, that the shadowed page belongs to this
     * domain, (by following the back-pointer). */
    ASSERT(t == SH_type_fl1_32_shadow  ||  
           t == SH_type_fl1_pae_shadow ||  
           t == SH_type_fl1_64_shadow  || 
           t == SH_type_monitor_table  || 
           (is_pv_32on64_vcpu(v) && t == SH_type_l4_64_shadow) ||
           (page_get_owner(mfn_to_page(_mfn(sp->backpointer))) 
            == v->domain)); 

    /* The down-shifts here are so that the switch statement is on nice
     * small numbers that the compiler will enjoy */
    switch ( t )
    {
#if CONFIG_PAGING_LEVELS == 2
    case SH_type_l1_32_shadow:
    case SH_type_fl1_32_shadow:
        SHADOW_INTERNAL_NAME(sh_destroy_l1_shadow, 2, 2)(v, smfn); 
        break;
    case SH_type_l2_32_shadow:
        SHADOW_INTERNAL_NAME(sh_destroy_l2_shadow, 2, 2)(v, smfn);
        break;
#else /* PAE or 64bit */
    case SH_type_l1_32_shadow:
    case SH_type_fl1_32_shadow:
        SHADOW_INTERNAL_NAME(sh_destroy_l1_shadow, 3, 2)(v, smfn);
        break;
    case SH_type_l2_32_shadow:
        SHADOW_INTERNAL_NAME(sh_destroy_l2_shadow, 3, 2)(v, smfn);
        break;
#endif

#if CONFIG_PAGING_LEVELS >= 3
    case SH_type_l1_pae_shadow:
    case SH_type_fl1_pae_shadow:
        SHADOW_INTERNAL_NAME(sh_destroy_l1_shadow, 3, 3)(v, smfn);
        break;
    case SH_type_l2_pae_shadow:
    case SH_type_l2h_pae_shadow:
        SHADOW_INTERNAL_NAME(sh_destroy_l2_shadow, 3, 3)(v, smfn);
        break;
#endif

#if CONFIG_PAGING_LEVELS >= 4
    case SH_type_l1_64_shadow:
    case SH_type_fl1_64_shadow:
        SHADOW_INTERNAL_NAME(sh_destroy_l1_shadow, 4, 4)(v, smfn);
        break;
    case SH_type_l2h_64_shadow:
        ASSERT(is_pv_32on64_vcpu(v));
        /* Fall through... */
    case SH_type_l2_64_shadow:
        SHADOW_INTERNAL_NAME(sh_destroy_l2_shadow, 4, 4)(v, smfn);
        break;
    case SH_type_l3_64_shadow:
        SHADOW_INTERNAL_NAME(sh_destroy_l3_shadow, 4, 4)(v, smfn);
        break;
    case SH_type_l4_64_shadow:
        SHADOW_INTERNAL_NAME(sh_destroy_l4_shadow, 4, 4)(v, smfn);
        break;
#endif
    default:
        SHADOW_ERROR("tried to destroy shadow of bad type %08lx\n",
                     (unsigned long)t);
        BUG();
    }    
}

/**************************************************************************/
/* Remove all writeable mappings of a guest frame from the shadow tables 
 * Returns non-zero if we need to flush TLBs. 
 * level and fault_addr desribe how we found this to be a pagetable;
 * level==0 means we have some other reason for revoking write access.*/

int sh_remove_write_access(struct vcpu *v, mfn_t gmfn, 
                           unsigned int level,
                           unsigned long fault_addr)
{
    /* Dispatch table for getting per-type functions */
    static hash_callback_t callbacks[SH_type_unused] = {
        NULL, /* none    */
#if CONFIG_PAGING_LEVELS == 2
        SHADOW_INTERNAL_NAME(sh_rm_write_access_from_l1,2,2), /* l1_32   */
        SHADOW_INTERNAL_NAME(sh_rm_write_access_from_l1,2,2), /* fl1_32  */
#else 
        SHADOW_INTERNAL_NAME(sh_rm_write_access_from_l1,3,2), /* l1_32   */
        SHADOW_INTERNAL_NAME(sh_rm_write_access_from_l1,3,2), /* fl1_32  */
#endif
        NULL, /* l2_32   */
#if CONFIG_PAGING_LEVELS >= 3
        SHADOW_INTERNAL_NAME(sh_rm_write_access_from_l1,3,3), /* l1_pae  */
        SHADOW_INTERNAL_NAME(sh_rm_write_access_from_l1,3,3), /* fl1_pae */
#else 
        NULL, /* l1_pae  */
        NULL, /* fl1_pae */
#endif
        NULL, /* l2_pae  */
        NULL, /* l2h_pae */
#if CONFIG_PAGING_LEVELS >= 4
        SHADOW_INTERNAL_NAME(sh_rm_write_access_from_l1,4,4), /* l1_64   */
        SHADOW_INTERNAL_NAME(sh_rm_write_access_from_l1,4,4), /* fl1_64  */
#else
        NULL, /* l1_64   */
        NULL, /* fl1_64  */
#endif
        NULL, /* l2_64   */
        NULL, /* l2h_64  */
        NULL, /* l3_64   */
        NULL, /* l4_64   */
        NULL, /* p2m     */
        NULL  /* unused  */
    };

    static unsigned int callback_mask = 
          1 << SH_type_l1_32_shadow
        | 1 << SH_type_fl1_32_shadow
        | 1 << SH_type_l1_pae_shadow
        | 1 << SH_type_fl1_pae_shadow
        | 1 << SH_type_l1_64_shadow
        | 1 << SH_type_fl1_64_shadow
        ;
    struct page_info *pg = mfn_to_page(gmfn);

    ASSERT(shadow_locked_by_me(v->domain));

    /* Only remove writable mappings if we are doing shadow refcounts.
     * In guest refcounting, we trust Xen to already be restricting
     * all the writes to the guest page tables, so we do not need to
     * do more. */
    if ( !shadow_mode_refcounts(v->domain) )
        return 0;

    /* Early exit if it's already a pagetable, or otherwise not writeable */
    if ( sh_mfn_is_a_page_table(gmfn) 
         || (pg->u.inuse.type_info & PGT_count_mask) == 0 )
        return 0;

    perfc_incr(shadow_writeable);

    /* If this isn't a "normal" writeable page, the domain is trying to 
     * put pagetables in special memory of some kind.  We can't allow that. */
    if ( (pg->u.inuse.type_info & PGT_type_mask) != PGT_writable_page )
    {
        SHADOW_ERROR("can't remove write access to mfn %lx, type_info is %" 
                      PRtype_info "\n",
                      mfn_x(gmfn), mfn_to_page(gmfn)->u.inuse.type_info);
        domain_crash(v->domain);
    }

#if SHADOW_OPTIMIZATIONS & SHOPT_WRITABLE_HEURISTIC
    if ( v == current && level != 0 )
    {
        unsigned long gfn;
        /* Heuristic: there is likely to be only one writeable mapping,
         * and that mapping is likely to be in the current pagetable,
         * in the guest's linear map (on non-HIGHPTE linux and windows)*/

#define GUESS(_a, _h) do {                                                \
            if ( v->arch.paging.mode->shadow.guess_wrmap(v, (_a), gmfn) ) \
                perfc_incr(shadow_writeable_h_ ## _h);                   \
            if ( (pg->u.inuse.type_info & PGT_count_mask) == 0 )          \
                return 1;                                                 \
        } while (0)

        
        if ( v->arch.paging.mode->guest_levels == 2 )
        {
            if ( level == 1 )
                /* 32bit non-PAE w2k3: linear map at 0xC0000000 */
                GUESS(0xC0000000UL + (fault_addr >> 10), 1);

            /* Linux lowmem: first 896MB is mapped 1-to-1 above 0xC0000000 */
            if ((gfn = mfn_to_gfn(v->domain, gmfn)) < 0x38000 ) 
                GUESS(0xC0000000UL + (gfn << PAGE_SHIFT), 4);

        }
#if CONFIG_PAGING_LEVELS >= 3
        else if ( v->arch.paging.mode->guest_levels == 3 )
        {
            /* 32bit PAE w2k3: linear map at 0xC0000000 */
            switch ( level ) 
            {
            case 1: GUESS(0xC0000000UL + (fault_addr >> 9), 2); break;
            case 2: GUESS(0xC0600000UL + (fault_addr >> 18), 2); break;
            }

            /* Linux lowmem: first 896MB is mapped 1-to-1 above 0xC0000000 */
            if ((gfn = mfn_to_gfn(v->domain, gmfn)) < 0x38000 ) 
                GUESS(0xC0000000UL + (gfn << PAGE_SHIFT), 4);
        }
#if CONFIG_PAGING_LEVELS >= 4
        else if ( v->arch.paging.mode->guest_levels == 4 )
        {
            /* 64bit w2k3: linear map at 0xfffff68000000000 */
            switch ( level ) 
            {
            case 1: GUESS(0xfffff68000000000UL 
                          + ((fault_addr & VADDR_MASK) >> 9), 3); break;
            case 2: GUESS(0xfffff6fb40000000UL
                          + ((fault_addr & VADDR_MASK) >> 18), 3); break;
            case 3: GUESS(0xfffff6fb7da00000UL 
                          + ((fault_addr & VADDR_MASK) >> 27), 3); break;
            }

            /* 64bit Linux direct map at 0xffff810000000000; older kernels 
             * had it at 0x0000010000000000UL */
            gfn = mfn_to_gfn(v->domain, gmfn); 
            GUESS(0xffff810000000000UL + (gfn << PAGE_SHIFT), 4); 
            GUESS(0x0000010000000000UL + (gfn << PAGE_SHIFT), 4); 
        }
#endif /* CONFIG_PAGING_LEVELS >= 4 */
#endif /* CONFIG_PAGING_LEVELS >= 3 */

#undef GUESS
    }

    if ( (pg->u.inuse.type_info & PGT_count_mask) == 0 )
        return 1;

    /* Second heuristic: on HIGHPTE linux, there are two particular PTEs
     * (entries in the fixmap) where linux maps its pagetables.  Since
     * we expect to hit them most of the time, we start the search for
     * the writeable mapping by looking at the same MFN where the last
     * brute-force search succeeded. */

    if ( v->arch.paging.shadow.last_writeable_pte_smfn != 0 )
    {
        unsigned long old_count = (pg->u.inuse.type_info & PGT_count_mask);
        mfn_t last_smfn = _mfn(v->arch.paging.shadow.last_writeable_pte_smfn);
        int shtype = mfn_to_shadow_page(last_smfn)->type;

        if ( callbacks[shtype] ) 
            callbacks[shtype](v, last_smfn, gmfn);

        if ( (pg->u.inuse.type_info & PGT_count_mask) != old_count )
            perfc_incr(shadow_writeable_h_5);
    }

    if ( (pg->u.inuse.type_info & PGT_count_mask) == 0 )
        return 1;

#endif /* SHADOW_OPTIMIZATIONS & SHOPT_WRITABLE_HEURISTIC */
    
    /* Brute-force search of all the shadows, by walking the hash */
    perfc_incr(shadow_writeable_bf);
    hash_foreach(v, callback_mask, callbacks, gmfn);

    /* If that didn't catch the mapping, then there's some non-pagetable
     * mapping -- ioreq page, grant mapping, &c. */
    if ( (mfn_to_page(gmfn)->u.inuse.type_info & PGT_count_mask) != 0 )
    {
        SHADOW_ERROR("can't remove write access to mfn %lx: guest has "
                      "%lu special-use mappings of it\n", mfn_x(gmfn),
                      (mfn_to_page(gmfn)->u.inuse.type_info&PGT_count_mask));
        domain_crash(v->domain);
    }
    
    /* We killed at least one writeable mapping, so must flush TLBs. */
    return 1;
}



/**************************************************************************/
/* Remove all mappings of a guest frame from the shadow tables.
 * Returns non-zero if we need to flush TLBs. */

int sh_remove_all_mappings(struct vcpu *v, mfn_t gmfn)
{
    struct page_info *page = mfn_to_page(gmfn);
    int expected_count, do_locking;

    /* Dispatch table for getting per-type functions */
    static hash_callback_t callbacks[SH_type_unused] = {
        NULL, /* none    */
#if CONFIG_PAGING_LEVELS == 2
        SHADOW_INTERNAL_NAME(sh_rm_mappings_from_l1,2,2), /* l1_32   */
        SHADOW_INTERNAL_NAME(sh_rm_mappings_from_l1,2,2), /* fl1_32  */
#else 
        SHADOW_INTERNAL_NAME(sh_rm_mappings_from_l1,3,2), /* l1_32   */
        SHADOW_INTERNAL_NAME(sh_rm_mappings_from_l1,3,2), /* fl1_32  */
#endif
        NULL, /* l2_32   */
#if CONFIG_PAGING_LEVELS >= 3
        SHADOW_INTERNAL_NAME(sh_rm_mappings_from_l1,3,3), /* l1_pae  */
        SHADOW_INTERNAL_NAME(sh_rm_mappings_from_l1,3,3), /* fl1_pae */
#else 
        NULL, /* l1_pae  */
        NULL, /* fl1_pae */
#endif
        NULL, /* l2_pae  */
        NULL, /* l2h_pae */
#if CONFIG_PAGING_LEVELS >= 4
        SHADOW_INTERNAL_NAME(sh_rm_mappings_from_l1,4,4), /* l1_64   */
        SHADOW_INTERNAL_NAME(sh_rm_mappings_from_l1,4,4), /* fl1_64  */
#else
        NULL, /* l1_64   */
        NULL, /* fl1_64  */
#endif
        NULL, /* l2_64   */
        NULL, /* l2h_64  */
        NULL, /* l3_64   */
        NULL, /* l4_64   */
        NULL, /* p2m     */
        NULL  /* unused  */
    };

    static unsigned int callback_mask = 
          1 << SH_type_l1_32_shadow
        | 1 << SH_type_fl1_32_shadow
        | 1 << SH_type_l1_pae_shadow
        | 1 << SH_type_fl1_pae_shadow
        | 1 << SH_type_l1_64_shadow
        | 1 << SH_type_fl1_64_shadow
        ;

    perfc_incr(shadow_mappings);
    if ( (page->count_info & PGC_count_mask) == 0 )
        return 0;

    /* Although this is an externally visible function, we do not know
     * whether the shadow lock will be held when it is called (since it
     * can be called via put_page_type when we clear a shadow l1e).
     * If the lock isn't held, take it for the duration of the call. */
    do_locking = !shadow_locked_by_me(v->domain);
    if ( do_locking ) shadow_lock(v->domain);

    /* XXX TODO: 
     * Heuristics for finding the (probably) single mapping of this gmfn */
    
    /* Brute-force search of all the shadows, by walking the hash */
    perfc_incr(shadow_mappings_bf);
    hash_foreach(v, callback_mask, callbacks, gmfn);

    /* If that didn't catch the mapping, something is very wrong */
    expected_count = (page->count_info & PGC_allocated) ? 1 : 0;
    if ( (page->count_info & PGC_count_mask) != expected_count )
    {
        /* Don't complain if we're in HVM and there are some extra mappings: 
         * The qemu helper process has an untyped mapping of this dom's RAM 
         * and the HVM restore program takes another. */
        if ( !(shadow_mode_external(v->domain)
               && (page->count_info & PGC_count_mask) <= 3
               && (page->u.inuse.type_info & PGT_count_mask) == 0) )
        {
            SHADOW_ERROR("can't find all mappings of mfn %lx: "
                          "c=%08x t=%08lx\n", mfn_x(gmfn), 
                          page->count_info, page->u.inuse.type_info);
        }
    }

    if ( do_locking ) shadow_unlock(v->domain);

    /* We killed at least one mapping, so must flush TLBs. */
    return 1;
}


/**************************************************************************/
/* Remove all shadows of a guest frame from the shadow tables */

static int sh_remove_shadow_via_pointer(struct vcpu *v, mfn_t smfn)
/* Follow this shadow's up-pointer, if it has one, and remove the reference
 * found there.  Returns 1 if that was the only reference to this shadow */
{
    struct shadow_page_info *sp = mfn_to_shadow_page(smfn);
    mfn_t pmfn;
    void *vaddr;
    int rc;

    ASSERT(sp->type > 0);
    ASSERT(sp->type < SH_type_max_shadow);
    ASSERT(sp->type != SH_type_l2_32_shadow);
    ASSERT(sp->type != SH_type_l2_pae_shadow);
    ASSERT(sp->type != SH_type_l2h_pae_shadow);
    ASSERT(sp->type != SH_type_l4_64_shadow);
    
    if (sp->up == 0) return 0;
    pmfn = _mfn(sp->up >> PAGE_SHIFT);
    ASSERT(mfn_valid(pmfn));
    vaddr = sh_map_domain_page(pmfn);
    ASSERT(vaddr);
    vaddr += sp->up & (PAGE_SIZE-1);
    ASSERT(l1e_get_pfn(*(l1_pgentry_t *)vaddr) == mfn_x(smfn));
    
    /* Is this the only reference to this shadow? */
    rc = (sp->count == 1) ? 1 : 0;

    /* Blank the offending entry */
    switch (sp->type) 
    {
    case SH_type_l1_32_shadow:
    case SH_type_l2_32_shadow:
#if CONFIG_PAGING_LEVELS == 2
        SHADOW_INTERNAL_NAME(sh_clear_shadow_entry,2,2)(v, vaddr, pmfn);
#else
        SHADOW_INTERNAL_NAME(sh_clear_shadow_entry,3,2)(v, vaddr, pmfn);
#endif
        break;
#if CONFIG_PAGING_LEVELS >=3
    case SH_type_l1_pae_shadow:
    case SH_type_l2_pae_shadow:
    case SH_type_l2h_pae_shadow:
        SHADOW_INTERNAL_NAME(sh_clear_shadow_entry,3,3)(v, vaddr, pmfn);
        break;
#if CONFIG_PAGING_LEVELS >= 4
    case SH_type_l1_64_shadow:
    case SH_type_l2_64_shadow:
    case SH_type_l2h_64_shadow:
    case SH_type_l3_64_shadow:
    case SH_type_l4_64_shadow:
        SHADOW_INTERNAL_NAME(sh_clear_shadow_entry,4,4)(v, vaddr, pmfn);
        break;
#endif
#endif
    default: BUG(); /* Some wierd unknown shadow type */
    }
    
    sh_unmap_domain_page(vaddr);
    if ( rc )
        perfc_incr(shadow_up_pointer);
    else
        perfc_incr(shadow_unshadow_bf);

    return rc;
}

void sh_remove_shadows(struct vcpu *v, mfn_t gmfn, int fast, int all)
/* Remove the shadows of this guest page.  
 * If fast != 0, just try the quick heuristic, which will remove 
 * at most one reference to each shadow of the page.  Otherwise, walk
 * all the shadow tables looking for refs to shadows of this gmfn.
 * If all != 0, kill the domain if we can't find all the shadows.
 * (all != 0 implies fast == 0)
 */
{
    struct page_info *pg = mfn_to_page(gmfn);
    mfn_t smfn;
    int do_locking;
    unsigned char t;
    
    /* Dispatch table for getting per-type functions: each level must
     * be called with the function to remove a lower-level shadow. */
    static hash_callback_t callbacks[SH_type_unused] = {
        NULL, /* none    */
        NULL, /* l1_32   */
        NULL, /* fl1_32  */
#if CONFIG_PAGING_LEVELS == 2
        SHADOW_INTERNAL_NAME(sh_remove_l1_shadow,2,2), /* l2_32   */
#else 
        SHADOW_INTERNAL_NAME(sh_remove_l1_shadow,3,2), /* l2_32   */
#endif
        NULL, /* l1_pae  */
        NULL, /* fl1_pae */
#if CONFIG_PAGING_LEVELS >= 3
        SHADOW_INTERNAL_NAME(sh_remove_l1_shadow,3,3), /* l2_pae  */
        SHADOW_INTERNAL_NAME(sh_remove_l1_shadow,3,3), /* l2h_pae */
#else 
        NULL, /* l2_pae  */
        NULL, /* l2h_pae */
#endif
        NULL, /* l1_64   */
        NULL, /* fl1_64  */
#if CONFIG_PAGING_LEVELS >= 4
        SHADOW_INTERNAL_NAME(sh_remove_l1_shadow,4,4), /* l2_64   */
        SHADOW_INTERNAL_NAME(sh_remove_l1_shadow,4,4), /* l2h_64  */
        SHADOW_INTERNAL_NAME(sh_remove_l2_shadow,4,4), /* l3_64   */
        SHADOW_INTERNAL_NAME(sh_remove_l3_shadow,4,4), /* l4_64   */
#else
        NULL, /* l2_64   */
        NULL, /* l2h_64  */
        NULL, /* l3_64   */
        NULL, /* l4_64   */
#endif
        NULL, /* p2m     */
        NULL  /* unused  */
    };

    /* Another lookup table, for choosing which mask to use */
    static unsigned int masks[SH_type_unused] = {
        0, /* none    */
        1 << SH_type_l2_32_shadow, /* l1_32   */
        0, /* fl1_32  */
        0, /* l2_32   */
        ((1 << SH_type_l2h_pae_shadow)
         | (1 << SH_type_l2_pae_shadow)), /* l1_pae  */
        0, /* fl1_pae */
        0, /* l2_pae  */
        0, /* l2h_pae  */
        ((1 << SH_type_l2h_64_shadow)
         | (1 << SH_type_l2_64_shadow)),  /* l1_64   */
        0, /* fl1_64  */
        1 << SH_type_l3_64_shadow, /* l2_64   */
        1 << SH_type_l3_64_shadow, /* l2h_64  */
        1 << SH_type_l4_64_shadow, /* l3_64   */
        0, /* l4_64   */
        0, /* p2m     */
        0  /* unused  */
    };

    ASSERT(!(all && fast));

    /* Although this is an externally visible function, we do not know
     * whether the shadow lock will be held when it is called (since it
     * can be called via put_page_type when we clear a shadow l1e).
     * If the lock isn't held, take it for the duration of the call. */
    do_locking = !shadow_locked_by_me(v->domain);
    if ( do_locking ) shadow_lock(v->domain);

    SHADOW_PRINTK("d=%d, v=%d, gmfn=%05lx\n",
                   v->domain->domain_id, v->vcpu_id, mfn_x(gmfn));

    /* Bail out now if the page is not shadowed */
    if ( (pg->count_info & PGC_page_table) == 0 )
    {
        if ( do_locking ) shadow_unlock(v->domain);
        return;
    }

    /* Search for this shadow in all appropriate shadows */
    perfc_incr(shadow_unshadow);

    /* Lower-level shadows need to be excised from upper-level shadows.
     * This call to hash_foreach() looks dangerous but is in fact OK: each
     * call will remove at most one shadow, and terminate immediately when
     * it does remove it, so we never walk the hash after doing a deletion.  */
#define DO_UNSHADOW(_type) do {                                         \
    t = (_type);                                                        \
    if( !(pg->count_info & PGC_page_table)                              \
        || !(pg->shadow_flags & (1 << t)) )                             \
        break;                                                          \
    smfn = shadow_hash_lookup(v, mfn_x(gmfn), t);                       \
    if ( unlikely(!mfn_valid(smfn)) )                                   \
    {                                                                   \
        SHADOW_ERROR(": gmfn %#lx has flags 0x%"PRIx32                  \
                     " but no type-0x%"PRIx32" shadow\n",               \
                     mfn_x(gmfn), (uint32_t)pg->shadow_flags, t);       \
        break;                                                          \
    }                                                                   \
    if ( sh_type_is_pinnable(v, t) )                                    \
        sh_unpin(v, smfn);                                              \
    else                                                                \
        sh_remove_shadow_via_pointer(v, smfn);                          \
    if( !fast                                                           \
        && (pg->count_info & PGC_page_table)                            \
        && (pg->shadow_flags & (1 << t)) )                              \
        hash_foreach(v, masks[t], callbacks, smfn);                     \
} while (0)

    DO_UNSHADOW(SH_type_l2_32_shadow);
    DO_UNSHADOW(SH_type_l1_32_shadow);
#if CONFIG_PAGING_LEVELS >= 3
    DO_UNSHADOW(SH_type_l2h_pae_shadow);
    DO_UNSHADOW(SH_type_l2_pae_shadow);
    DO_UNSHADOW(SH_type_l1_pae_shadow);
#if CONFIG_PAGING_LEVELS >= 4
    DO_UNSHADOW(SH_type_l4_64_shadow);
    DO_UNSHADOW(SH_type_l3_64_shadow);
    DO_UNSHADOW(SH_type_l2h_64_shadow);
    DO_UNSHADOW(SH_type_l2_64_shadow);
    DO_UNSHADOW(SH_type_l1_64_shadow);
#endif
#endif

#undef DO_UNSHADOW

    /* If that didn't catch the shadows, something is wrong */
    if ( !fast && (pg->count_info & PGC_page_table) )
    {
        SHADOW_ERROR("can't find all shadows of mfn %05lx "
                     "(shadow_flags=%08lx)\n",
                      mfn_x(gmfn), pg->shadow_flags);
        if ( all ) 
            domain_crash(v->domain);
    }

    /* Need to flush TLBs now, so that linear maps are safe next time we 
     * take a fault. */
    flush_tlb_mask(v->domain->domain_dirty_cpumask);

    if ( do_locking ) shadow_unlock(v->domain);
}

static void
sh_remove_all_shadows_and_parents(struct vcpu *v, mfn_t gmfn)
/* Even harsher: this is a HVM page that we thing is no longer a pagetable.
 * Unshadow it, and recursively unshadow pages that reference it. */
{
    sh_remove_shadows(v, gmfn, 0, 1);
    /* XXX TODO:
     * Rework this hashtable walker to return a linked-list of all 
     * the shadows it modified, then do breadth-first recursion 
     * to find the way up to higher-level tables and unshadow them too. 
     *
     * The current code (just tearing down each page's shadows as we
     * detect that it is not a pagetable) is correct, but very slow. 
     * It means extra emulated writes and slows down removal of mappings. */
}

/**************************************************************************/

static void sh_update_paging_modes(struct vcpu *v)
{
    struct domain *d = v->domain;
    struct paging_mode *old_mode = v->arch.paging.mode;

    ASSERT(shadow_locked_by_me(d));

#if (SHADOW_OPTIMIZATIONS & SHOPT_VIRTUAL_TLB) 
    /* Make sure this vcpu has a virtual TLB array allocated */
    if ( unlikely(!v->arch.paging.vtlb) )
    {
        v->arch.paging.vtlb = xmalloc_array(struct shadow_vtlb, VTLB_ENTRIES);
        if ( unlikely(!v->arch.paging.vtlb) )
        {
            SHADOW_ERROR("Could not allocate vTLB space for dom %u vcpu %u\n",
                         d->domain_id, v->vcpu_id);
            domain_crash(v->domain);
            return;
        }
        memset(v->arch.paging.vtlb, 0, 
               VTLB_ENTRIES * sizeof (struct shadow_vtlb));
        spin_lock_init(&v->arch.paging.vtlb_lock);
    }
#endif /* (SHADOW_OPTIMIZATIONS & SHOPT_VIRTUAL_TLB) */

    // Valid transitions handled by this function:
    // - For PV guests:
    //     - after a shadow mode has been changed
    // - For HVM guests:
    //     - after a shadow mode has been changed
    //     - changes in CR0.PG, CR4.PAE, CR4.PSE, or CR4.PGE
    //

    // First, tear down any old shadow tables held by this vcpu.
    //
    if ( v->arch.paging.mode )
        v->arch.paging.mode->shadow.detach_old_tables(v);

    if ( !is_hvm_domain(d) )
    {
        ///
        /// PV guest
        ///
#if CONFIG_PAGING_LEVELS == 4
        v->arch.paging.mode = &SHADOW_INTERNAL_NAME(sh_paging_mode,4,4);
#elif CONFIG_PAGING_LEVELS == 3
        v->arch.paging.mode = &SHADOW_INTERNAL_NAME(sh_paging_mode,3,3);
#elif CONFIG_PAGING_LEVELS == 2
        v->arch.paging.mode = &SHADOW_INTERNAL_NAME(sh_paging_mode,2,2);
#else
#error unexpected paging mode
#endif
    }
    else
    {
        ///
        /// HVM guest
        ///
        ASSERT(shadow_mode_translate(d));
        ASSERT(shadow_mode_external(d));

        if ( !hvm_paging_enabled(v) )
        {
            /* When the guest has CR0.PG clear, we provide a 32-bit, non-PAE
             * pagetable for it, mapping 4 GB one-to-one using a single l2
             * page of 1024 superpage mappings */
            v->arch.guest_table = d->arch.paging.shadow.unpaged_pagetable;
#if CONFIG_PAGING_LEVELS >= 3
            v->arch.paging.mode = &SHADOW_INTERNAL_NAME(sh_paging_mode, 3, 2);
#else
            v->arch.paging.mode = &SHADOW_INTERNAL_NAME(sh_paging_mode, 2, 2);
#endif
        }
        else
        {
#ifdef __x86_64__
            if ( hvm_long_mode_enabled(v) )
            {
                // long mode guest...
                v->arch.paging.mode =
                    &SHADOW_INTERNAL_NAME(sh_paging_mode, 4, 4);
            }
            else
#endif
                if ( hvm_pae_enabled(v) )
                {
#if CONFIG_PAGING_LEVELS >= 3
                    // 32-bit PAE mode guest...
                    v->arch.paging.mode =
                        &SHADOW_INTERNAL_NAME(sh_paging_mode, 3, 3);
#else
                    SHADOW_ERROR("PAE not supported in 32-bit Xen\n");
                    domain_crash(d);
                    return;
#endif
                }
                else
                {
                    // 32-bit 2 level guest...
#if CONFIG_PAGING_LEVELS >= 3
                    v->arch.paging.mode =
                        &SHADOW_INTERNAL_NAME(sh_paging_mode, 3, 2);
#else
                    v->arch.paging.mode =
                        &SHADOW_INTERNAL_NAME(sh_paging_mode, 2, 2);
#endif
                }
        }

        if ( pagetable_is_null(v->arch.monitor_table) )
        {
            mfn_t mmfn = v->arch.paging.mode->shadow.make_monitor_table(v);
            v->arch.monitor_table = pagetable_from_mfn(mmfn);
            make_cr3(v, mfn_x(mmfn));
            hvm_update_host_cr3(v);
        }

        if ( v->arch.paging.mode != old_mode )
        {
            SHADOW_PRINTK("new paging mode: d=%u v=%u pe=%d g=%u s=%u "
                          "(was g=%u s=%u)\n",
                          d->domain_id, v->vcpu_id,
                          is_hvm_domain(d) ? hvm_paging_enabled(v) : 1,
                          v->arch.paging.mode->guest_levels,
                          v->arch.paging.mode->shadow.shadow_levels,
                          old_mode ? old_mode->guest_levels : 0,
                          old_mode ? old_mode->shadow.shadow_levels : 0);
            if ( old_mode &&
                 (v->arch.paging.mode->shadow.shadow_levels !=
                  old_mode->shadow.shadow_levels) )
            {
                /* Need to make a new monitor table for the new mode */
                mfn_t new_mfn, old_mfn;

                if ( v != current && vcpu_runnable(v) ) 
                {
                    SHADOW_ERROR("Some third party (d=%u v=%u) is changing "
                                 "this HVM vcpu's (d=%u v=%u) paging mode "
                                 "while it is running.\n",
                                 current->domain->domain_id, current->vcpu_id,
                                 v->domain->domain_id, v->vcpu_id);
                    /* It's not safe to do that because we can't change
                     * the host CR� for a running domain */
                    domain_crash(v->domain);
                    return;
                }

                old_mfn = pagetable_get_mfn(v->arch.monitor_table);
                v->arch.monitor_table = pagetable_null();
                new_mfn = v->arch.paging.mode->shadow.make_monitor_table(v);
                v->arch.monitor_table = pagetable_from_mfn(new_mfn);
                SHADOW_PRINTK("new monitor table %"PRI_mfn "\n",
                               mfn_x(new_mfn));

                /* Don't be running on the old monitor table when we 
                 * pull it down!  Switch CR3, and warn the HVM code that
                 * its host cr3 has changed. */
                make_cr3(v, mfn_x(new_mfn));
                if ( v == current )
                    write_ptbase(v);
                hvm_update_host_cr3(v);
                old_mode->shadow.destroy_monitor_table(v, old_mfn);
            }
        }

        // XXX -- Need to deal with changes in CR4.PSE and CR4.PGE.
        //        These are HARD: think about the case where two CPU's have
        //        different values for CR4.PSE and CR4.PGE at the same time.
        //        This *does* happen, at least for CR4.PGE...
    }

    v->arch.paging.mode->update_cr3(v, 0);
}

void shadow_update_paging_modes(struct vcpu *v)
{
    shadow_lock(v->domain);
    sh_update_paging_modes(v);
    shadow_unlock(v->domain);
}

/**************************************************************************/
/* Turning on and off shadow features */

static void sh_new_mode(struct domain *d, u32 new_mode)
/* Inform all the vcpus that the shadow mode has been changed */
{
    struct vcpu *v;

    ASSERT(shadow_locked_by_me(d));
    ASSERT(d != current->domain);
    d->arch.paging.mode = new_mode;
    for_each_vcpu(d, v)
        sh_update_paging_modes(v);
}

int shadow_enable(struct domain *d, u32 mode)
/* Turn on "permanent" shadow features: external, translate, refcount.
 * Can only be called once on a domain, and these features cannot be
 * disabled. 
 * Returns 0 for success, -errno for failure. */
{    
    unsigned int old_pages;
    struct page_info *pg = NULL;
    uint32_t *e;
    int i, rv = 0;

    mode |= PG_SH_enable;

    domain_pause(d);

    /* Sanity check the arguments */
    if ( (d == current->domain) ||
         shadow_mode_enabled(d) ||
         ((mode & PG_translate) && !(mode & PG_refcounts)) ||
         ((mode & PG_external) && !(mode & PG_translate)) )
    {
        rv = -EINVAL;
        goto out_unlocked;
    }

    /* Init the shadow memory allocation if the user hasn't done so */
    old_pages = d->arch.paging.shadow.total_pages;
    if ( old_pages == 0 )
    {
        unsigned int r;
        shadow_lock(d);                
        r = sh_set_allocation(d, 256, NULL); /* Use at least 1MB */
        if ( r != 0 )
        {
            sh_set_allocation(d, 0, NULL);
            rv = -ENOMEM;
            goto out_locked;
        }        
        shadow_unlock(d);
    }

    /* Init the P2M table.  Must be done before we take the shadow lock 
     * to avoid possible deadlock. */
    if ( mode & PG_translate )
    {
        rv = p2m_alloc_table(d, shadow_alloc_p2m_page, shadow_free_p2m_page);
        if (rv != 0)
            goto out_unlocked;
    }

    /* HVM domains need an extra pagetable for vcpus that think they
     * have paging disabled */
    if ( is_hvm_domain(d) )
    {
        /* Get a single page from the shadow pool.  Take it via the 
         * P2M interface to make freeing it simpler afterwards. */
        pg = shadow_alloc_p2m_page(d);
        if ( pg == NULL )
        {
            rv = -ENOMEM;
            goto out_unlocked;
        }
        /* Fill it with 32-bit, non-PAE superpage entries, each mapping 4MB
         * of virtual address space onto the same physical address range */ 
        e = sh_map_domain_page(page_to_mfn(pg));
        for ( i = 0; i < PAGE_SIZE / sizeof(*e); i++ )
            e[i] = ((0x400000U * i)
                    | _PAGE_PRESENT | _PAGE_RW | _PAGE_USER 
                    | _PAGE_ACCESSED | _PAGE_DIRTY | _PAGE_PSE);
        sh_unmap_domain_page(e);
        pg->u.inuse.type_info = PGT_l2_page_table | 1 | PGT_validated;
    }

    shadow_lock(d);

    /* Sanity check again with the lock held */
    if ( shadow_mode_enabled(d) )
    {
        rv = -EINVAL;
        goto out_locked;
    }

    /* Init the hash table */
    if ( shadow_hash_alloc(d) != 0 )
    {
        rv = -ENOMEM;
        goto out_locked;
    }

#if (SHADOW_OPTIMIZATIONS & SHOPT_LINUX_L3_TOPLEVEL) 
    /* We assume we're dealing with an older 64bit linux guest until we 
     * see the guest use more than one l4 per vcpu. */
    d->arch.paging.shadow.opt_flags = SHOPT_LINUX_L3_TOPLEVEL;
#endif

    /* Record the 1-to-1 pagetable we just made */
    if ( is_hvm_domain(d) )
        d->arch.paging.shadow.unpaged_pagetable = pagetable_from_page(pg);

    /* Update the bits */
    sh_new_mode(d, mode);

 out_locked:
    shadow_unlock(d);
 out_unlocked:
    if ( rv != 0 && !pagetable_is_null(d->arch.phys_table) )
        p2m_teardown(d);
    if ( rv != 0 && pg != NULL )
        shadow_free_p2m_page(d, pg);
    domain_unpause(d);
    return rv;
}

void shadow_teardown(struct domain *d)
/* Destroy the shadow pagetables of this domain and free its shadow memory.
 * Should only be called for dying domains. */
{
    struct vcpu *v;
    mfn_t mfn;
    struct list_head *entry, *n;
    struct page_info *pg;

    ASSERT(d->is_dying);
    ASSERT(d != current->domain);

    if ( !shadow_locked_by_me(d) )
        shadow_lock(d); /* Keep various asserts happy */

    if ( shadow_mode_enabled(d) )
    {
        /* Release the shadow and monitor tables held by each vcpu */
        for_each_vcpu(d, v)
        {
            if ( v->arch.paging.mode )
            {
                v->arch.paging.mode->shadow.detach_old_tables(v);
                if ( shadow_mode_external(d) )
                {
                    mfn = pagetable_get_mfn(v->arch.monitor_table);
                    if ( mfn_valid(mfn) && (mfn_x(mfn) != 0) )
                        v->arch.paging.mode->shadow.destroy_monitor_table(v, mfn);
                    v->arch.monitor_table = pagetable_null();
                }
            }
        }
    }

#if (SHADOW_OPTIMIZATIONS & SHOPT_VIRTUAL_TLB) 
    /* Free the virtual-TLB array attached to each vcpu */
    for_each_vcpu(d, v)
    {
        if ( v->arch.paging.vtlb )
        {
            xfree(v->arch.paging.vtlb);
            v->arch.paging.vtlb = NULL;
        }
    }
#endif /* (SHADOW_OPTIMIZATIONS & SHOPT_VIRTUAL_TLB) */

    list_for_each_safe(entry, n, &d->arch.paging.shadow.p2m_freelist)
    {
        list_del(entry);
        pg = list_entry(entry, struct page_info, list);
        shadow_free_p2m_page(d, pg);
    }

    if ( d->arch.paging.shadow.total_pages != 0 )
    {
        SHADOW_PRINTK("teardown of domain %u starts."
                       "  Shadow pages total = %u, free = %u, p2m=%u\n",
                       d->domain_id,
                       d->arch.paging.shadow.total_pages, 
                       d->arch.paging.shadow.free_pages, 
                       d->arch.paging.shadow.p2m_pages);
        /* Destroy all the shadows and release memory to domheap */
        sh_set_allocation(d, 0, NULL);
        /* Release the hash table back to xenheap */
        if (d->arch.paging.shadow.hash_table) 
            shadow_hash_teardown(d);
        /* Should not have any more memory held */
        SHADOW_PRINTK("teardown done."
                       "  Shadow pages total = %u, free = %u, p2m=%u\n",
                       d->arch.paging.shadow.total_pages, 
                       d->arch.paging.shadow.free_pages, 
                       d->arch.paging.shadow.p2m_pages);
        ASSERT(d->arch.paging.shadow.total_pages == 0);
    }

    /* Free the non-paged-vcpus pagetable; must happen after we've 
     * destroyed any shadows of it or sh_destroy_shadow will get confused. */
    if ( !pagetable_is_null(d->arch.paging.shadow.unpaged_pagetable) )
    {
        for_each_vcpu(d, v)
        {
            ASSERT(is_hvm_vcpu(v));
            if ( !hvm_paging_enabled(v) )
                v->arch.guest_table = pagetable_null();
        }
        shadow_free_p2m_page(d, 
            pagetable_get_page(d->arch.paging.shadow.unpaged_pagetable));
        d->arch.paging.shadow.unpaged_pagetable = pagetable_null();
    }

    /* We leave the "permanent" shadow modes enabled, but clear the
     * log-dirty mode bit.  We don't want any more mark_dirty()
     * calls now that we've torn down the bitmap */
    d->arch.paging.mode &= ~PG_log_dirty;

    shadow_unlock(d);
}

void shadow_final_teardown(struct domain *d)
/* Called by arch_domain_destroy(), when it's safe to pull down the p2m map. */
{
    SHADOW_PRINTK("dom %u final teardown starts."
                   "  Shadow pages total = %u, free = %u, p2m=%u\n",
                   d->domain_id,
                   d->arch.paging.shadow.total_pages, 
                   d->arch.paging.shadow.free_pages, 
                   d->arch.paging.shadow.p2m_pages);

    /* Double-check that the domain didn't have any shadow memory.  
     * It is possible for a domain that never got domain_kill()ed
     * to get here with its shadow allocation intact. */
    if ( d->arch.paging.shadow.total_pages != 0 )
        shadow_teardown(d);

    /* It is now safe to pull down the p2m map. */
    p2m_teardown(d);

    SHADOW_PRINTK("dom %u final teardown done."
                   "  Shadow pages total = %u, free = %u, p2m=%u\n",
                   d->domain_id,
                   d->arch.paging.shadow.total_pages, 
                   d->arch.paging.shadow.free_pages, 
                   d->arch.paging.shadow.p2m_pages);
}

static int shadow_one_bit_enable(struct domain *d, u32 mode)
/* Turn on a single shadow mode feature */
{
    ASSERT(shadow_locked_by_me(d));

    /* Sanity check the call */
    if ( d == current->domain || (d->arch.paging.mode & mode) == mode )
    {
        return -EINVAL;
    }

    mode |= PG_SH_enable;

    if ( d->arch.paging.mode == 0 )
    {
        /* Init the shadow memory allocation and the hash table */
        if ( sh_set_allocation(d, 1, NULL) != 0 
             || shadow_hash_alloc(d) != 0 )
        {
            sh_set_allocation(d, 0, NULL);
            return -ENOMEM;
        }
    }

    /* Update the bits */
    sh_new_mode(d, d->arch.paging.mode | mode);

    return 0;
}

static int shadow_one_bit_disable(struct domain *d, u32 mode) 
/* Turn off a single shadow mode feature */
{
    struct vcpu *v;
    ASSERT(shadow_locked_by_me(d));

    /* Sanity check the call */
    if ( d == current->domain || !((d->arch.paging.mode & mode) == mode) )
    {
        return -EINVAL;
    }

    /* Update the bits */
    sh_new_mode(d, d->arch.paging.mode & ~mode);
    if ( d->arch.paging.mode == 0 )
    {
        /* Get this domain off shadows */
        SHADOW_PRINTK("un-shadowing of domain %u starts."
                       "  Shadow pages total = %u, free = %u, p2m=%u\n",
                       d->domain_id,
                       d->arch.paging.shadow.total_pages, 
                       d->arch.paging.shadow.free_pages, 
                       d->arch.paging.shadow.p2m_pages);
        for_each_vcpu(d, v)
        {
            if ( v->arch.paging.mode )
                v->arch.paging.mode->shadow.detach_old_tables(v);
#if CONFIG_PAGING_LEVELS == 4
            if ( !(v->arch.flags & TF_kernel_mode) )
                make_cr3(v, pagetable_get_pfn(v->arch.guest_table_user));
            else
#endif
                make_cr3(v, pagetable_get_pfn(v->arch.guest_table));

        }

        /* Pull down the memory allocation */
        if ( sh_set_allocation(d, 0, NULL) != 0 )
        {
            // XXX - How can this occur?
            //       Seems like a bug to return an error now that we've
            //       disabled the relevant shadow mode.
            //
            return -ENOMEM;
        }
        shadow_hash_teardown(d);
        SHADOW_PRINTK("un-shadowing of domain %u done."
                       "  Shadow pages total = %u, free = %u, p2m=%u\n",
                       d->domain_id,
                       d->arch.paging.shadow.total_pages, 
                       d->arch.paging.shadow.free_pages, 
                       d->arch.paging.shadow.p2m_pages);
    }

    return 0;
}

/* Enable/disable ops for the "test" and "log-dirty" modes */
static int shadow_test_enable(struct domain *d)
{
    int ret;

    domain_pause(d);
    shadow_lock(d);
    ret = shadow_one_bit_enable(d, PG_SH_enable);
    shadow_unlock(d);
    domain_unpause(d);

    return ret;
}

static int shadow_test_disable(struct domain *d)
{
    int ret;

    domain_pause(d);
    shadow_lock(d);
    ret = shadow_one_bit_disable(d, PG_SH_enable);
    shadow_unlock(d);
    domain_unpause(d);

    return ret;
}

/**************************************************************************/
/* P2M map manipulations */

/* shadow specific code which should be called when P2M table entry is updated
 * with new content. It is responsible for update the entry, as well as other 
 * shadow processing jobs.
 */
void
shadow_write_p2m_entry(struct vcpu *v, unsigned long gfn, 
                       l1_pgentry_t *p, mfn_t table_mfn, 
                       l1_pgentry_t new, unsigned int level)
{
    struct domain *d = v->domain;
    
    shadow_lock(d);

    /* If we're removing an MFN from the p2m, remove it from the shadows too */
    if ( level == 1 )
    {
        mfn_t mfn = _mfn(l1e_get_pfn(*p));
        p2m_type_t p2mt = p2m_flags_to_type(l1e_get_flags(*p));
        if ( p2m_is_valid(p2mt) && mfn_valid(mfn) ) 
        {
            sh_remove_all_shadows_and_parents(v, mfn);
            if ( sh_remove_all_mappings(v, mfn) )
                flush_tlb_mask(d->domain_dirty_cpumask);    
        }
    }

    /* Update the entry with new content */
    safe_write_pte(p, new);

    /* install P2M in monitors for PAE Xen */
#if CONFIG_PAGING_LEVELS == 3
    if ( level == 3 )
        /* We have written to the p2m l3: need to sync the per-vcpu
         * copies of it in the monitor tables */
        p2m_install_entry_in_monitors(d, (l3_pgentry_t *)p);
#endif

#if (SHADOW_OPTIMIZATIONS & SHOPT_FAST_FAULT_PATH)
    /* If we're doing FAST_FAULT_PATH, then shadow mode may have
       cached the fact that this is an mmio region in the shadow
       page tables.  Blow the tables away to remove the cache.
       This is pretty heavy handed, but this is a rare operation
       (it might happen a dozen times during boot and then never
       again), so it doesn't matter too much. */
    if ( d->arch.paging.shadow.has_fast_mmio_entries )
    {
        shadow_blow_tables(d);
        d->arch.paging.shadow.has_fast_mmio_entries = 0;
    }
#endif

    shadow_unlock(d);
}

/**************************************************************************/
/* Copy-on-Write (CoW) mode support */
static int shadow_cow_op(struct domain *d, struct xen_domctl_shadow_op *sc)
{
    if (sc->op == XEN_DOMCTL_SHADOW_COW_ON)
    {
        l1_pgentry_t eff_l1e;
        unsigned long gva;
        int i;

        cow.dom = d;
        cow.counter = 0;
        cow.update_shadows = 0;
        cow.do_update = 0;

        cow.pf_count = 0;
        cow.batches_count = 0;
        cow.made_rw_count = 0;
        cow.hot_count = 0;
        cow.ioemu_count = 0;

        cow.pages_mfns_size = sc->pages;
        cow.cpt_mfns_size = COW_TYPE_FN(sc->pages - 1) + 1;

        cow.pages_mfns = (unsigned long *) 
            xmalloc_array(unsigned long, cow.pages_mfns_size);
        if (cow.pages_mfns == NULL) { 
             printk("Unable to allocate cow.pages_mfns\n");
             return -ENOMEM;
        }

        cow.cpt_mfns = (unsigned long *) 
            xmalloc_array(unsigned long, cow.cpt_mfns_size);
        if (cow.cpt_mfns == NULL) {
             printk("Unable to allocate cow.cpt_mfns\n");
             return -ENOMEM;
        }

        /* translate guest pages to mfns for pages_mfns buffer */
        shadow_lock(d);
        gva = (unsigned long) sc->cow_pages.q;
        for (i = 0; i < cow.pages_mfns_size; i++)
        {
            guest_get_eff_l1e(current, gva, &eff_l1e);
            cow.pages_mfns[i] = (unsigned long) l1e_get_pfn(eff_l1e);
            gva += PAGE_SIZE;
        }
        shadow_unlock(d);

        /* translate guest pages to mfns for pfn_types_mfns buffer */
        shadow_lock(d);
        gva = (unsigned long) sc->cow_pfn_types.q;
        for (i = 0; i < cow.cpt_mfns_size; i++)
        {
            guest_get_eff_l1e(current, gva, &eff_l1e);
            cow.cpt_mfns[i] = (unsigned long) l1e_get_pfn(eff_l1e);
            gva += PAGE_SIZE;
        }
        shadow_unlock(d);
        
        /* setup hot bitmap */
        cow.hot_bitmap = (unsigned long *) xmalloc_array(char, COW_BITMAP_SIZE);
        if (cow.hot_bitmap == NULL)
        { 
            printk("Unable to allocate cow.hot_bitmap\n");
            return -ENOMEM;
        }
        memset(cow.hot_bitmap, 0, COW_BITMAP_SIZE);
        
        // should pause domain, or will getting the shadow lock be enough?
        if (!paging_mode_log_dirty(d))
        {
            cow_determine_hot(d->vcpu[0], cow.gl2mfn[0]);
            cow_determine_hot(d->vcpu[0], cow.gl2mfn[1]);
        }
        copy_to_guest_offset(sc->hot_bitmap, 
                             0, 
                             (void *) cow.hot_bitmap, 
                             COW_BITMAP_SIZE);
                             
        xfree(cow.hot_bitmap);

        /* calculate how many batch updates we should allow to update shadows */
        if ((cow.hot_count % 1024) > 0)
            cow.update_shadows = (cow.hot_count / 1024) + 1;
        else
            cow.update_shadows = cow.hot_count / 1024;
        printk("CoW: cow.update_shadows = %lu\n", cow.update_shadows);

        return paging_log_dirty_enable(d);
    }
    else if (sc->op == XEN_DOMCTL_SHADOW_COW_OFF)
    {
        int ret = 0;
       
        /* turn off cow/log_dirty */ 
        paging_log_dirty_disable(d);

        /* copy final cow count to dom0 */
        copy_to_guest_offset(sc->cow_count, 0, (void *) &(cow.counter), 
                             sizeof(unsigned long));      

#ifdef COW_INVERSE_MAP
        /* tear down our inverse mappings */
        invert_sh_table_teardown(); 
#endif

        printk("CoW: page faults during migration = %lu\n", cow.pf_count);
        printk("CoW: batches marked dirty = %lu\n", cow.batches_count);
        printk("CoW: pages identified as hot = %lu\n", cow.hot_count);
        printk("CoW: mappings made writable = %lu\n", cow.made_rw_count);
        printk("CoW: ioemu hypercalls = %lu\n", cow.ioemu_count);

        cow.dom = NULL;
        cow.gl2mfn[0] = INVALID_MFN;
        cow.gl2mfn[1] = INVALID_MFN;
        cow.counter = 0;
        cow.pages_mfns_size = 0;
        xfree(cow.pages_mfns);
        cow.cpt_mfns_size = 0;
        xfree(cow.cpt_mfns);
  
        return ret;
    }
    else if (sc->op == XEN_DOMCTL_SHADOW_COW_MARK_DIRTY)
    {
        int i;
        unsigned long batch_size = sc->pages;
        XEN_GUEST_HANDLE_64(uint8) hdl = sc->cow_pfn_types;
        unsigned long *pfn_batch;

        cow.batches_count++;
        
        pfn_batch = (unsigned long *) xmalloc_array(unsigned long, batch_size);
        if (pfn_batch == NULL)
        {
            printk("Unable to allocate pfn_batch in COW_MARK_DIRTY\n");
            return -ENOMEM;
        }
        copy_from_guest_offset((void *) pfn_batch, hdl, 
                               0, batch_size * sizeof(unsigned long));

        for (i = 0; i < batch_size; i++)
        {
            mfn_t mfn;
            unsigned long pfn = pfn_batch[i] & ~XEN_DOMCTL_PFINFO_LTAB_MASK;

            mfn = gmfn_to_mfn(d, pfn);
            if (mfn_valid(mfn) && (mfn_to_gfn(d, mfn) == pfn)) 
            {
                paging_mark_dirty(d, mfn);
#ifdef COW_INVERSE_MAP
                cow_add_writeable_mappings(d->vcpu[0], mfn);
#endif
            }
        }
        xfree(pfn_batch);

        /* probably need to update shadows as many times as batch update 
         * includes hot pages  */
        if (cow.update_shadows > 0)
        {
            cow_update_shadows(d->vcpu[0], cow.gl2mfn[0]);
            cow_update_shadows(d->vcpu[0], cow.gl2mfn[1]);
            cow_update_shadows(d->vcpu[0], 
                               pagetable_get_mfn(d->vcpu[0]->arch.guest_table));
            cow.update_shadows--;
        }
        
        /* update external dirty_bitmap for copy domain */
        if (paging_log_dirty_op(d, sc))
            printk("CoW: mark_dirty: paging_log_dirty_op() failed\n");

        return 0;
    }
    else if (sc->op == XEN_DOMCTL_SHADOW_COW_COPY)
    {
        mfn_t mfn;
        unsigned long pfn;

        cow.ioemu_count++;

        pfn = sc->pfn;
        if (((pfn >= 0xa0 && pfn < 0xc0)
                 || (pfn >= (HVM_BELOW_4G_MMIO_START >> PAGE_SHIFT)
                            && pfn < (1ULL<<32) >> PAGE_SHIFT))) 
            return 0;

        shadow_lock(d);
        mfn = gmfn_to_mfn(d, pfn);
        if (mfn_valid(mfn) && (mfn_to_gfn(d, mfn) == pfn)) 
            cow_copy_page(d, mfn);
            
        /* update external dirty_bitmap for copy domain */
        if (paging_mode_log_dirty(d))
        {
            if (paging_log_dirty_op(d, sc))
                printk("CoW: from ioemu, paging_log_dirty_op() failed\n");
        }
        shadow_unlock(d);

        return 0;
    }
    else 
    {
        /* Improper op */
        return 1;
    }
}

/**************************************************************************/
/* Log-dirty mode support */

/* Shadow specific code which is called in paging_log_dirty_enable().
 * Return 0 if no problem found.
 */
int shadow_enable_log_dirty(struct domain *d)
{
    int ret;

    /* shadow lock is required here */
    shadow_lock(d);
    if ( shadow_mode_enabled(d) )
    {
        /* This domain already has some shadows: need to clear them out 
         * of the way to make sure that all references to guest memory are 
         * properly write-protected */
        shadow_blow_tables(d);
    }

#if (SHADOW_OPTIMIZATIONS & SHOPT_LINUX_L3_TOPLEVEL)
    /* 32bit PV guests on 64bit xen behave like older 64bit linux: they
     * change an l4e instead of cr3 to switch tables.  Give them the
     * same optimization */
    if ( is_pv_32on64_domain(d) )
        d->arch.paging.shadow.opt_flags = SHOPT_LINUX_L3_TOPLEVEL;
#endif
    
    ret = shadow_one_bit_enable(d, PG_log_dirty);
    shadow_unlock(d);

    return ret;
}

/* shadow specfic code which is called in paging_log_dirty_disable() */
int shadow_disable_log_dirty(struct domain *d)
{
    int ret;

    /* shadow lock is required here */    
    shadow_lock(d);
    ret = shadow_one_bit_disable(d, PG_log_dirty);
    shadow_unlock(d);
    
    return ret;
}

/* This function is called when we CLEAN log dirty bitmap. See 
 * paging_log_dirty_op() for details. 
 */
void shadow_clean_dirty_bitmap(struct domain *d)
{
    shadow_lock(d);
    /* Need to revoke write access to the domain's pages again.
     * In future, we'll have a less heavy-handed approach to this,
     * but for now, we just unshadow everything except Xen. */
    shadow_blow_tables(d);
    shadow_unlock(d);
}
/**************************************************************************/
/* Shadow-control XEN_DOMCTL dispatcher */

int shadow_domctl(struct domain *d, 
                  xen_domctl_shadow_op_t *sc,
                  XEN_GUEST_HANDLE(void) u_domctl)
{
    int rc, preempted = 0;

    switch ( sc->op )
    {
    case XEN_DOMCTL_SHADOW_COW_ON:
    case XEN_DOMCTL_SHADOW_COW_OFF:
    case XEN_DOMCTL_SHADOW_COW_COPY:
    case XEN_DOMCTL_SHADOW_COW_MARK_DIRTY:
        return shadow_cow_op(d, sc);

    case XEN_DOMCTL_SHADOW_OP_OFF:
        if ( d->arch.paging.mode == PG_SH_enable )
            if ( (rc = shadow_test_disable(d)) != 0 ) 
                return rc;
        return 0;

    case XEN_DOMCTL_SHADOW_OP_ENABLE_TEST:
        return shadow_test_enable(d);

    case XEN_DOMCTL_SHADOW_OP_ENABLE_TRANSLATE:
        return shadow_enable(d, PG_refcounts|PG_translate);

    case XEN_DOMCTL_SHADOW_OP_ENABLE:
        return shadow_enable(d, sc->mode << PG_mode_shift);

    case XEN_DOMCTL_SHADOW_OP_GET_ALLOCATION:
        sc->mb = shadow_get_allocation(d);
        return 0;

    case XEN_DOMCTL_SHADOW_OP_SET_ALLOCATION:
        shadow_lock(d);
        if ( sc->mb == 0 && shadow_mode_enabled(d) )
        {            
            /* Can't set the allocation to zero unless the domain stops using
             * shadow pagetables first */
            SHADOW_ERROR("Can't set shadow allocation to zero, domain %u"
                         " is still using shadows.\n", d->domain_id);
            shadow_unlock(d);
            return -EINVAL;
        }
        rc = sh_set_allocation(d, sc->mb << (20 - PAGE_SHIFT), &preempted);
        shadow_unlock(d);
        if ( preempted )
            /* Not finished.  Set up to re-run the call. */
            rc = hypercall_create_continuation(
                __HYPERVISOR_domctl, "h", u_domctl);
        else 
            /* Finished.  Return the new allocation */
            sc->mb = shadow_get_allocation(d);
        return rc;

    default:
        SHADOW_ERROR("Bad shadow op %u\n", sc->op);
        return -EINVAL;
    }
}


/**************************************************************************/
/* Auditing shadow tables */

#if SHADOW_AUDIT & SHADOW_AUDIT_ENTRIES_FULL

void shadow_audit_tables(struct vcpu *v) 
{
    /* Dispatch table for getting per-type functions */
    static hash_callback_t callbacks[SH_type_unused] = {
        NULL, /* none    */
#if CONFIG_PAGING_LEVELS == 2
        SHADOW_INTERNAL_NAME(sh_audit_l1_table,2,2),  /* l1_32   */
        SHADOW_INTERNAL_NAME(sh_audit_fl1_table,2,2), /* fl1_32  */
        SHADOW_INTERNAL_NAME(sh_audit_l2_table,2,2),  /* l2_32   */
#else 
        SHADOW_INTERNAL_NAME(sh_audit_l1_table,3,2),  /* l1_32   */
        SHADOW_INTERNAL_NAME(sh_audit_fl1_table,3,2), /* fl1_32  */
        SHADOW_INTERNAL_NAME(sh_audit_l2_table,3,2),  /* l2_32   */
        SHADOW_INTERNAL_NAME(sh_audit_l1_table,3,3),  /* l1_pae  */
        SHADOW_INTERNAL_NAME(sh_audit_fl1_table,3,3), /* fl1_pae */
        SHADOW_INTERNAL_NAME(sh_audit_l2_table,3,3),  /* l2_pae  */
        SHADOW_INTERNAL_NAME(sh_audit_l2_table,3,3),  /* l2h_pae */
#if CONFIG_PAGING_LEVELS >= 4
        SHADOW_INTERNAL_NAME(sh_audit_l1_table,4,4),  /* l1_64   */
        SHADOW_INTERNAL_NAME(sh_audit_fl1_table,4,4), /* fl1_64  */
        SHADOW_INTERNAL_NAME(sh_audit_l2_table,4,4),  /* l2_64   */
        SHADOW_INTERNAL_NAME(sh_audit_l2_table,4,4),  /* l2h_64   */
        SHADOW_INTERNAL_NAME(sh_audit_l3_table,4,4),  /* l3_64   */
        SHADOW_INTERNAL_NAME(sh_audit_l4_table,4,4),  /* l4_64   */
#endif /* CONFIG_PAGING_LEVELS >= 4 */
#endif /* CONFIG_PAGING_LEVELS > 2 */
        NULL  /* All the rest */
    };
    unsigned int mask; 

    if ( !(SHADOW_AUDIT_ENABLE) )
        return;
    
    if ( SHADOW_AUDIT & SHADOW_AUDIT_ENTRIES_FULL )
        mask = ~1; /* Audit every table in the system */
    else 
    {
        /* Audit only the current mode's tables */
        switch ( v->arch.paging.mode->guest_levels )
        {
        case 2: mask = (SHF_L1_32|SHF_FL1_32|SHF_L2_32); break;
        case 3: mask = (SHF_L1_PAE|SHF_FL1_PAE|SHF_L2_PAE
                        |SHF_L2H_PAE); break;
        case 4: mask = (SHF_L1_64|SHF_FL1_64|SHF_L2_64  
                        |SHF_L3_64|SHF_L4_64); break;
        default: BUG();
        }
    }

    hash_foreach(v, ~1, callbacks, _mfn(INVALID_MFN));
}

#endif /* Shadow audit */

/*
 * Local variables:
 * mode: C
 * c-set-style: "BSD"
 * c-basic-offset: 4
 * indent-tabs-mode: nil
 * End: 
 */
