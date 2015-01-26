/******************************************************************************
 * arch/x86/mm/shadow/multi.c
 *
 * Simple, mostly-synchronous shadow page tables. 
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
#include <xen/domain_page.h>
#include <xen/guest_access.h>
#include <public/hvm/e820.h>
#include <asm/page.h>
#include <asm/current.h>
#include <asm/shadow.h>
#include <asm/flushtlb.h>
#include <asm/hvm/hvm.h>
#include <asm/hvm/cacheattr.h>
#include <asm/mtrr.h>
#include "private.h"
#include "types.h"

/* THINGS TO DO LATER:
 * 
 * TEARDOWN HEURISTICS
 * Also: have a heuristic for when to destroy a previous paging-mode's 
 * shadows.  When a guest is done with its start-of-day 32-bit tables
 * and reuses the memory we want to drop those shadows.  Start with 
 * shadows in a page in two modes as a hint, but beware of clever tricks 
 * like reusing a pagetable for both PAE and 64-bit during boot...
 *
 * PAE LINEAR MAPS
 * Rework shadow_get_l*e() to have the option of using map_domain_page()
 * instead of linear maps.  Add appropriate unmap_l*e calls in the users. 
 * Then we can test the speed difference made by linear maps.  If the 
 * map_domain_page() version is OK on PAE, we could maybe allow a lightweight 
 * l3-and-l2h-only shadow mode for PAE PV guests that would allow them 
 * to share l2h pages again. 
 *
 * GUEST_WALK_TABLES TLB FLUSH COALESCE
 * guest_walk_tables can do up to three remote TLB flushes as it walks to
 * the first l1 of a new pagetable.  Should coalesce the flushes to the end, 
 * and if we do flush, re-do the walk.  If anything has changed, then 
 * pause all the other vcpus and do the walk *again*.
 *
 * PSE disabled / PSE36/
 * We don't support any modes other than PSE enabled, PSE36 disabled.
 * Neither of those would be hard to change, but we'd need to be able to 
 * deal with shadows made in one mode and used in another.
 */

#define FETCH_TYPE_PREFETCH 1
#define FETCH_TYPE_DEMAND   2
#define FETCH_TYPE_WRITE    4
typedef enum {
    ft_prefetch     = FETCH_TYPE_PREFETCH,
    ft_demand_read  = FETCH_TYPE_DEMAND,
    ft_demand_write = FETCH_TYPE_DEMAND | FETCH_TYPE_WRITE,
} fetch_type_t;

#ifdef DEBUG_TRACE_DUMP
static char *fetch_type_names[] = {
    [ft_prefetch]     "prefetch",
    [ft_demand_read]  "demand read",
    [ft_demand_write] "demand write",
};
#endif

/**************************************************************************
 * Copy-on-Write (CoW) helper functions
 */
extern struct cow_data cow;

void cow_copy(struct domain *d, mfn_t mfn, int from)
{
    void *b, *p;
    unsigned long *cpt_ptr;    
    struct page_info *page;
    unsigned long pfn, pfn_type;
    int do_locking;

    if (!mfn_valid(mfn)) 
        return;

    do_locking = !shadow_locked_by_me(d);
    if (do_locking)
    {
        shadow_lock(d);
        /* Check the mode again with the lock held */
        if (unlikely(!paging_mode_log_dirty(d)))
        {
            shadow_unlock(d);
            return;
        }
    }
    log_dirty_lock(d);

    if (cow.counter > cow.pages_mfns_size)
    {
        printk("no more free cow pages to copy to\n");
        goto out;
    }

    page = mfn_to_page(mfn);
    if (get_page(page, d))
    {
        /* get pfn of page to copy */
        pfn = mfn_to_gfn(d, mfn_x(mfn));
        pfn_type = pfn;

        /* Check if there is a valid M2P mapping */
        if (!VALID_M2P(pfn))
        {
            put_page(page);
            goto out;
        }

        if (((pfn >= 0xa0 && pfn < 0xc0) 
                 || (pfn >= (HVM_BELOW_4G_MMIO_START >> PAGE_SHIFT)
                            && pfn < (1ULL<<32) >> PAGE_SHIFT))) {
            put_page(page);
            goto out;
        }

        if (gmfn_to_mfn(d, pfn) != mfn)
        {
            put_page(page);
            goto out;
        }

        if (sh_mfn_is_dirty(d, mfn))
        {
            put_page(page);
            goto out;
        }

        switch(page->u.inuse.type_info & PGT_type_mask) 
        {
            case PGT_l1_page_table:
                pfn_type |= XEN_DOMCTL_PFINFO_L1TAB;
                break;
            case PGT_l2_page_table:
                pfn_type |= XEN_DOMCTL_PFINFO_L2TAB;
                break;
        }

        if (page->u.inuse.type_info & PGT_pinned) 
            pfn_type |= XEN_DOMCTL_PFINFO_LPINTAB;
    }
    else
        goto out;

    /* Map in dom0 allocated CoW pfn_type page */
    b = map_domain_page(cow.cpt_mfns[COW_TYPE_FN(cow.counter)]);
    cpt_ptr = &(((unsigned long *) b)[COW_TYPE_IX(cow.counter)]);
    *cpt_ptr = pfn_type;
    sh_unmap_domain_page(b);

    /* Map in HVM guest page */
    p = sh_map_domain_page(mfn);
    b = map_domain_page(cow.pages_mfns[cow.counter]);
    memcpy(b, p, PAGE_SIZE);
    sh_unmap_domain_page(p);
    sh_unmap_domain_page(b);

    /* Update ref count */
    put_page(page);

    /* Update bookkeeping */
    cow.counter++;
    
    /* Mark dirty */
    _paging_mark_dirty(d, mfn, 0);

out:
    log_dirty_unlock(d);
    if (do_locking)
        shadow_unlock(d);
}

/**************************************************************************/
/* Hash table mapping from guest pagetables to shadows
 *
 * Normal case: maps the mfn of a guest page to the mfn of its shadow page.
 * FL1's:       maps the *gfn* of the start of a superpage to the mfn of a
 *              shadow L1 which maps its "splinters".
 */

static inline mfn_t 
get_fl1_shadow_status(struct vcpu *v, gfn_t gfn)
/* Look for FL1 shadows in the hash table */
{
    mfn_t smfn = shadow_hash_lookup(v, gfn_x(gfn), SH_type_fl1_shadow);
    return smfn;
}

static inline mfn_t 
get_shadow_status(struct vcpu *v, mfn_t gmfn, u32 shadow_type)
/* Look for shadows in the hash table */
{
    mfn_t smfn = shadow_hash_lookup(v, mfn_x(gmfn), shadow_type);
    perfc_incr(shadow_get_shadow_status);
    return smfn;
}

static inline void 
set_fl1_shadow_status(struct vcpu *v, gfn_t gfn, mfn_t smfn)
/* Put an FL1 shadow into the hash table */
{
    SHADOW_PRINTK("gfn=%"SH_PRI_gfn", type=%08x, smfn=%05lx\n",
                   gfn_x(gfn), SH_type_fl1_shadow, mfn_x(smfn));

    shadow_hash_insert(v, gfn_x(gfn), SH_type_fl1_shadow, smfn);
}

static inline void 
set_shadow_status(struct vcpu *v, mfn_t gmfn, u32 shadow_type, mfn_t smfn)
/* Put a shadow into the hash table */
{
    struct domain *d = v->domain;
    int res;

    SHADOW_PRINTK("d=%d, v=%d, gmfn=%05lx, type=%08x, smfn=%05lx\n",
                   d->domain_id, v->vcpu_id, mfn_x(gmfn),
                   shadow_type, mfn_x(smfn));

    /* 32-on-64 PV guests don't own their l4 pages so can't get_page them */
    if ( !is_pv_32on64_vcpu(v) || shadow_type != SH_type_l4_64_shadow )
    {
        res = get_page(mfn_to_page(gmfn), d);
        ASSERT(res == 1);
    }

    shadow_hash_insert(v, mfn_x(gmfn), shadow_type, smfn);
}

static inline void 
delete_fl1_shadow_status(struct vcpu *v, gfn_t gfn, mfn_t smfn)
/* Remove a shadow from the hash table */
{
    SHADOW_PRINTK("gfn=%"SH_PRI_gfn", type=%08x, smfn=%05lx\n",
                   gfn_x(gfn), SH_type_fl1_shadow, mfn_x(smfn));
    shadow_hash_delete(v, gfn_x(gfn), SH_type_fl1_shadow, smfn);
}

static inline void 
delete_shadow_status(struct vcpu *v, mfn_t gmfn, u32 shadow_type, mfn_t smfn)
/* Remove a shadow from the hash table */
{
    SHADOW_PRINTK("d=%d, v=%d, gmfn=%05lx, type=%08x, smfn=%05lx\n",
                   v->domain->domain_id, v->vcpu_id,
                   mfn_x(gmfn), shadow_type, mfn_x(smfn));
    shadow_hash_delete(v, mfn_x(gmfn), shadow_type, smfn);
    /* 32-on-64 PV guests don't own their l4 pages; see set_shadow_status */
    if ( !is_pv_32on64_vcpu(v) || shadow_type != SH_type_l4_64_shadow )
        put_page(mfn_to_page(gmfn));
}

/**************************************************************************/
/* CPU feature support querying */

static inline int
guest_supports_superpages(struct vcpu *v)
{
    /* The _PAGE_PSE bit must be honoured in HVM guests, whenever
     * CR4.PSE is set or the guest is in PAE or long mode. 
     * It's also used in the dummy PT for vcpus with CR4.PG cleared. */
    return (is_hvm_vcpu(v) && 
            (GUEST_PAGING_LEVELS != 2 
             || !hvm_paging_enabled(v)
             || (v->arch.hvm_vcpu.guest_cr[4] & X86_CR4_PSE)));
}

static inline int
guest_supports_nx(struct vcpu *v)
{
    if ( GUEST_PAGING_LEVELS == 2 || !cpu_has_nx )
        return 0;
    if ( !is_hvm_vcpu(v) )
        return cpu_has_nx;
    return hvm_nx_enabled(v);
}


/**************************************************************************/
/* Functions for walking the guest page tables */

/* Flags that are needed in a pagetable entry, with the sense of NX inverted */
static uint32_t mandatory_flags(struct vcpu *v, uint32_t pfec) 
{
    static uint32_t flags[] = {
        /* I/F -  Usr Wr */
        /* 0   0   0   0 */ _PAGE_PRESENT, 
        /* 0   0   0   1 */ _PAGE_PRESENT|_PAGE_RW,
        /* 0   0   1   0 */ _PAGE_PRESENT|_PAGE_USER,
        /* 0   0   1   1 */ _PAGE_PRESENT|_PAGE_RW|_PAGE_USER,
        /* 0   1   0   0 */ _PAGE_PRESENT, 
        /* 0   1   0   1 */ _PAGE_PRESENT|_PAGE_RW,
        /* 0   1   1   0 */ _PAGE_PRESENT|_PAGE_USER,
        /* 0   1   1   1 */ _PAGE_PRESENT|_PAGE_RW|_PAGE_USER,
        /* 1   0   0   0 */ _PAGE_PRESENT|_PAGE_NX_BIT, 
        /* 1   0   0   1 */ _PAGE_PRESENT|_PAGE_RW|_PAGE_NX_BIT,
        /* 1   0   1   0 */ _PAGE_PRESENT|_PAGE_USER|_PAGE_NX_BIT,
        /* 1   0   1   1 */ _PAGE_PRESENT|_PAGE_RW|_PAGE_USER|_PAGE_NX_BIT,
        /* 1   1   0   0 */ _PAGE_PRESENT|_PAGE_NX_BIT, 
        /* 1   1   0   1 */ _PAGE_PRESENT|_PAGE_RW|_PAGE_NX_BIT,
        /* 1   1   1   0 */ _PAGE_PRESENT|_PAGE_USER|_PAGE_NX_BIT,
        /* 1   1   1   1 */ _PAGE_PRESENT|_PAGE_RW|_PAGE_USER|_PAGE_NX_BIT,
    };

    /* Don't demand not-NX if the CPU wouldn't enforce it. */
    if ( !guest_supports_nx(v) )
        pfec &= ~PFEC_insn_fetch;

    /* Don't demand R/W if the CPU wouldn't enforce it. */
    if ( is_hvm_vcpu(v) && unlikely(!hvm_wp_enabled(v)) 
         && !(pfec & PFEC_user_mode) )
        pfec &= ~PFEC_write_access;

    return flags[(pfec & 0x1f) >> 1];
}

/* Modify a guest pagetable entry to set the Accessed and Dirty bits.
 * Returns non-zero if it actually writes to guest memory. */
static uint32_t set_ad_bits(void *guest_p, void *walk_p, int set_dirty)
{
    guest_intpte_t old, new;

    old = *(guest_intpte_t *)walk_p;
    new = old | _PAGE_ACCESSED | (set_dirty ? _PAGE_DIRTY : 0);
    if ( old != new ) 
    {
        /* Write the new entry into the walk, and try to write it back
         * into the guest table as well.  If the guest table has changed
         * under out feet then leave it alone. */
        *(guest_intpte_t *)walk_p = new;
        if ( cmpxchg(((guest_intpte_t *)guest_p), old, new) == old ) 
            return 1;
    }
    return 0;
}

/* Walk the guest pagetables, after the manner of a hardware walker. 
 *
 * Inputs: a vcpu, a virtual address, a walk_t to fill, a 
 *         pointer to a pagefault code, and a flag "shadow_op".
 * 
 * We walk the vcpu's guest pagetables, filling the walk_t with what we
 * see and adding any Accessed and Dirty bits that are needed in the
 * guest entries.  Using the pagefault code, we check the permissions as
 * we go.  For the purposes of reading pagetables we treat all non-RAM
 * memory as contining zeroes.
 * 
 * If "shadow_op" is non-zero, we are serving a genuine guest memory access, 
 * and must (a) be under the shadow lock, and (b) remove write access
 * from any guest PT pages we see, as we will be shadowing them soon
 * and will rely on the contents' not having changed.
 * 
 * Returns 0 for success, or the set of permission bits that we failed on 
 * if the walk did not complete.
 * N.B. This is different from the old return code but almost no callers
 * checked the old return code anyway.
 */
static uint32_t
guest_walk_tables(struct vcpu *v, unsigned long va, walk_t *gw, 
                  uint32_t pfec, int shadow_op)
{
    struct domain *d = v->domain;
    p2m_type_t p2mt;
    guest_l1e_t *l1p = NULL;
    guest_l2e_t *l2p = NULL;
#if GUEST_PAGING_LEVELS >= 4 /* 64-bit only... */
    guest_l3e_t *l3p = NULL;
    guest_l4e_t *l4p;
#endif
    uint32_t gflags, mflags, rc = 0;
    int pse;

    ASSERT(!shadow_op || shadow_locked_by_me(d));
    
    perfc_incr(shadow_guest_walk);
    memset(gw, 0, sizeof(*gw));
    gw->va = va;

    /* Mandatory bits that must be set in every entry.  We invert NX, to
     * calculate as if there were an "X" bit that allowed access. 
     * We will accumulate, in rc, the set of flags that are missing. */
    mflags = mandatory_flags(v, pfec);

    /* Get l2e from the top level table */
    gw->l2mfn = pagetable_get_mfn(v->arch.guest_table);
    l2p = ((guest_l2e_t *)v->arch.paging.shadow.guest_vtable);
    gw->l2e = l2p[guest_l2_table_offset(va)];

    gflags = guest_l2e_get_flags(gw->l2e) ^ _PAGE_NX_BIT;
    rc |= ((gflags & mflags) ^ mflags);
    if ( rc & _PAGE_PRESENT )
        goto out;

    pse = (guest_supports_superpages(v) && 
           (guest_l2e_get_flags(gw->l2e) & _PAGE_PSE)); 

    if ( pse )
    {
        /* Special case: this guest VA is in a PSE superpage, so there's
         * no guest l1e.  We make one up so that the propagation code
         * can generate a shadow l1 table.  Start with the gfn of the 
         * first 4k-page of the superpage. */
        gfn_t start = guest_l2e_get_gfn(gw->l2e);
        /* Grant full access in the l1e, since all the guest entry's 
         * access controls are enforced in the shadow l2e. */
        int flags = (_PAGE_PRESENT|_PAGE_USER|_PAGE_RW|
                     _PAGE_ACCESSED|_PAGE_DIRTY);
        /* PSE level 2 entries use bit 12 for PAT; propagate it to bit 7
         * of the level 1. */
        if ( (guest_l2e_get_flags(gw->l2e) & _PAGE_PSE_PAT) ) 
            flags |= _PAGE_PAT;
        /* Copy the cache-control bits to the l1 as well, because we
         * can't represent PAT in the (non-PSE) shadow l2e. :(
         * This could cause problems if a guest ever maps an area of
         * memory with superpages using more than one caching mode. */
        flags |= guest_l2e_get_flags(gw->l2e) & (_PAGE_PWT|_PAGE_PCD);
        /* Increment the pfn by the right number of 4k pages.  
         * The ~0x1 is to mask out the PAT bit mentioned above. */
        start = _gfn((gfn_x(start) & ~0x1) + guest_l1_table_offset(va));
        gw->l1e = guest_l1e_from_gfn(start, flags);
        gw->l1mfn = _mfn(INVALID_MFN);
    } 
    else 
    {
        /* Not a superpage: carry on and find the l1e. */
        gw->l1mfn = gfn_to_mfn(d, guest_l2e_get_gfn(gw->l2e), &p2mt);
        if ( !p2m_is_ram(p2mt) )
        {
            rc |= _PAGE_PRESENT;
            goto out;
        }
        ASSERT(mfn_valid(gw->l1mfn));
        /* This mfn is a pagetable: make sure the guest can't write to it. */
        if ( shadow_op 
             && sh_remove_write_access(v, gw->l1mfn, 1, va) != 0 )
            flush_tlb_mask(d->domain_dirty_cpumask); 
        l1p = sh_map_domain_page(gw->l1mfn);
        gw->l1e = l1p[guest_l1_table_offset(va)];
        gflags = guest_l1e_get_flags(gw->l1e) ^ _PAGE_NX_BIT;
        rc |= ((gflags & mflags) ^ mflags);
    }

    /* Go back and set accessed and dirty bits only if the walk was a
     * success.  Although the PRMs say higher-level _PAGE_ACCESSED bits
     * get set whenever a lower-level PT is used, at least some hardware
     * walkers behave this way. */
    if ( rc == 0 ) 
    {
        /* CoW: Copy pages before they're dirtied */
        cow_copy_page(d, mfn_x(gw->l2mfn));
        cow_copy_page(d, mfn_x(gw->l1mfn));

        if ( set_ad_bits(l2p + guest_l2_table_offset(va), &gw->l2e,
                         (pse && (pfec & PFEC_write_access))) )
            paging_mark_dirty(d, mfn_x(gw->l2mfn));            
        if ( !pse ) 
        {
            if ( set_ad_bits(l1p + guest_l1_table_offset(va), &gw->l1e, 
                             (pfec & PFEC_write_access)) )
                paging_mark_dirty(d, mfn_x(gw->l1mfn));
        }
    }

 out:
    if ( l1p ) sh_unmap_domain_page(l1p);

    return rc;
}

/* Given a walk_t, translate the gw->va into the guest's notion of the
 * corresponding frame number. */
static inline gfn_t
guest_walk_to_gfn(walk_t *gw)
{
    if ( !(guest_l1e_get_flags(gw->l1e) & _PAGE_PRESENT) )
        return _gfn(INVALID_GFN);
    return guest_l1e_get_gfn(gw->l1e);
}

/* Given a walk_t, translate the gw->va into the guest's notion of the
 * corresponding physical address. */
static inline paddr_t
guest_walk_to_gpa(walk_t *gw)
{
    if ( !(guest_l1e_get_flags(gw->l1e) & _PAGE_PRESENT) )
        return 0;
    return guest_l1e_get_paddr(gw->l1e) + (gw->va & ~PAGE_MASK);
}

#if 0 /* Keep for debugging */
/* Pretty-print the contents of a guest-walk */
static inline void print_gw(walk_t *gw)
{
    SHADOW_PRINTK("GUEST WALK TO %#lx:\n", gw->va);
#if GUEST_PAGING_LEVELS >= 3 /* PAE or 64... */
#if GUEST_PAGING_LEVELS >= 4 /* 64-bit only... */
    SHADOW_PRINTK("   l4mfn=%" PRI_mfn "\n", mfn_x(gw->l4mfn));
    SHADOW_PRINTK("   l4e=%" SH_PRI_gpte "\n", gw->l4e.l4);
    SHADOW_PRINTK("   l3mfn=%" PRI_mfn "\n", mfn_x(gw->l3mfn));
#endif /* PAE or 64... */
    SHADOW_PRINTK("   l3e=%" SH_PRI_gpte "\n", gw->l3e.l3);
#endif /* All levels... */
    SHADOW_PRINTK("   l2mfn=%" PRI_mfn "\n", mfn_x(gw->l2mfn));
    SHADOW_PRINTK("   l2e=%" SH_PRI_gpte "\n", gw->l2e.l2);
    SHADOW_PRINTK("   l1mfn=%" PRI_mfn "\n", mfn_x(gw->l1mfn));
    SHADOW_PRINTK("   l1e=%" SH_PRI_gpte "\n", gw->l1e.l1);
}
#endif /* 0 */

#if SHADOW_AUDIT & SHADOW_AUDIT_ENTRIES
/* Lightweight audit: pass all the shadows associated with this guest walk
 * through the audit mechanisms */
static void sh_audit_gw(struct vcpu *v, walk_t *gw) 
{
    mfn_t smfn;

    if ( !(SHADOW_AUDIT_ENABLE) )
        return;

#if GUEST_PAGING_LEVELS >= 4 /* 64-bit only... */
    if ( mfn_valid(gw->l4mfn)
         && mfn_valid((smfn = get_shadow_status(v, gw->l4mfn, 
                                                SH_type_l4_shadow))) )
        (void) sh_audit_l4_table(v, smfn, _mfn(INVALID_MFN));
    if ( mfn_valid(gw->l3mfn)
         && mfn_valid((smfn = get_shadow_status(v, gw->l3mfn, 
                                                SH_type_l3_shadow))) )
        (void) sh_audit_l3_table(v, smfn, _mfn(INVALID_MFN));
#endif /* PAE or 64... */
    if ( mfn_valid(gw->l2mfn) )
    {
        if ( mfn_valid((smfn = get_shadow_status(v, gw->l2mfn, 
                                                 SH_type_l2_shadow))) )
            (void) sh_audit_l2_table(v, smfn, _mfn(INVALID_MFN));
#if GUEST_PAGING_LEVELS == 3
        if ( mfn_valid((smfn = get_shadow_status(v, gw->l2mfn, 
                                                 SH_type_l2h_shadow))) )
            (void) sh_audit_l2_table(v, smfn, _mfn(INVALID_MFN));
#endif
    }
    if ( mfn_valid(gw->l1mfn)
         && mfn_valid((smfn = get_shadow_status(v, gw->l1mfn, 
                                                SH_type_l1_shadow))) )
        (void) sh_audit_l1_table(v, smfn, _mfn(INVALID_MFN));
    else if ( (guest_l2e_get_flags(gw->l2e) & _PAGE_PRESENT)
              && (guest_l2e_get_flags(gw->l2e) & _PAGE_PSE)
              && mfn_valid( 
              (smfn = get_fl1_shadow_status(v, guest_l2e_get_gfn(gw->l2e)))) )
        (void) sh_audit_fl1_table(v, smfn, _mfn(INVALID_MFN));
}

#else
#define sh_audit_gw(_v, _gw) do {} while(0)
#endif /* audit code */


#if (CONFIG_PAGING_LEVELS == GUEST_PAGING_LEVELS) && (CONFIG_PAGING_LEVELS == SHADOW_PAGING_LEVELS)
void *
sh_guest_map_l1e(struct vcpu *v, unsigned long addr,
                  unsigned long *gl1mfn)
{
    void *pl1e = NULL;
    walk_t gw;

    ASSERT(shadow_mode_translate(v->domain));
        
    // XXX -- this is expensive, but it's easy to cobble together...
    // FIXME!

    shadow_lock(v->domain);
    if ( guest_walk_tables(v, addr, &gw, PFEC_page_present, 1) == 0 
         && mfn_valid(gw.l1mfn) )
    {
        if ( gl1mfn )
            *gl1mfn = mfn_x(gw.l1mfn);
        pl1e = map_domain_page(mfn_x(gw.l1mfn)) +
            (guest_l1_table_offset(addr) * sizeof(guest_l1e_t));
    }

    shadow_unlock(v->domain);

    return pl1e;
}

void
sh_guest_get_eff_l1e(struct vcpu *v, unsigned long addr, void *eff_l1e)
{
    walk_t gw;

    ASSERT(shadow_mode_translate(v->domain));
        
    // XXX -- this is expensive, but it's easy to cobble together...
    // FIXME!

    shadow_lock(v->domain);
    (void) guest_walk_tables(v, addr, &gw, PFEC_page_present, 1);
    *(guest_l1e_t *)eff_l1e = gw.l1e;
    shadow_unlock(v->domain);
}
#endif /* CONFIG==SHADOW==GUEST */

/**************************************************************************/
/* Functions to compute the correct index into a shadow page, given an
 * index into the guest page (as returned by guest_get_index()).
 * This is trivial when the shadow and guest use the same sized PTEs, but
 * gets more interesting when those sizes are mismatched (e.g. 32-bit guest,
 * PAE- or 64-bit shadows).
 *
 * These functions also increment the shadow mfn, when necessary.  When PTE
 * sizes are mismatched, it takes 2 shadow L1 pages for a single guest L1
 * page.  In this case, we allocate 2 contiguous pages for the shadow L1, and
 * use simple pointer arithmetic on a pointer to the guest L1e to figure out
 * which shadow page we really want.  Similarly, when PTE sizes are
 * mismatched, we shadow a guest L2 page with 4 shadow L2 pages.  (The easiest
 * way to see this is: a 32-bit guest L2 page maps 4GB of virtual address
 * space, while a PAE- or 64-bit shadow L2 page maps 1GB of virtual address
 * space.)
 *
 * For PAE guests, for every 32-bytes of guest L3 page table, we use 64-bytes
 * of shadow (to store both the shadow, and the info that would normally be
 * stored in page_info fields).  This arrangement allows the shadow and the
 * "page_info" fields to always be stored in the same page (in fact, in
 * the same cache line), avoiding an extra call to map_domain_page().
 */

static inline u32
guest_index(void *ptr)
{
    return (u32)((unsigned long)ptr & ~PAGE_MASK) / sizeof(guest_l1e_t);
}

static u32
shadow_l1_index(mfn_t *smfn, u32 guest_index)
{
#if (GUEST_PAGING_LEVELS == 2) && (SHADOW_PAGING_LEVELS != 2)
    *smfn = _mfn(mfn_x(*smfn) +
                 (guest_index / SHADOW_L1_PAGETABLE_ENTRIES));
    return (guest_index % SHADOW_L1_PAGETABLE_ENTRIES);
#else
    return guest_index;
#endif
}

static u32
shadow_l2_index(mfn_t *smfn, u32 guest_index)
{
#if (GUEST_PAGING_LEVELS == 2) && (SHADOW_PAGING_LEVELS != 2)
    // Because we use 2 shadow l2 entries for each guest entry, the number of
    // guest entries per shadow page is SHADOW_L2_PAGETABLE_ENTRIES/2
    //
    *smfn = _mfn(mfn_x(*smfn) +
                 (guest_index / (SHADOW_L2_PAGETABLE_ENTRIES / 2)));

    // We multiple by two to get the index of the first of the two entries
    // used to shadow the specified guest entry.
    return (guest_index % (SHADOW_L2_PAGETABLE_ENTRIES / 2)) * 2;
#else
    return guest_index;
#endif
}

#if GUEST_PAGING_LEVELS >= 4

static u32
shadow_l3_index(mfn_t *smfn, u32 guest_index)
{
    return guest_index;
}

static u32
shadow_l4_index(mfn_t *smfn, u32 guest_index)
{
    return guest_index;
}

#endif // GUEST_PAGING_LEVELS >= 4

extern u32 get_pat_flags(struct vcpu *v,
                  u32 gl1e_flags,
                  paddr_t gpaddr,
                  paddr_t spaddr);

unsigned char pat_type_2_pte_flags(unsigned char pat_type);
/**************************************************************************/
/* Function which computes shadow entries from their corresponding guest
 * entries.  This is the "heart" of the shadow code. It operates using
 * level-1 shadow types, but handles all levels of entry.
 * Don't call it directly, but use the four wrappers below.
 */

static always_inline void
_sh_propagate(struct vcpu *v, 
              guest_intpte_t guest_intpte,
              mfn_t target_mfn, 
              void *shadow_entry_ptr,
              int level,
              fetch_type_t ft, 
              p2m_type_t p2mt)
{
    guest_l1e_t guest_entry = { guest_intpte };
    shadow_l1e_t *sp = shadow_entry_ptr;
    struct domain *d = v->domain;
    gfn_t target_gfn = guest_l1e_get_gfn(guest_entry);
    u32 pass_thru_flags;
    u32 gflags, sflags;

    /* We don't shadow PAE l3s */
    ASSERT(GUEST_PAGING_LEVELS > 3 || level != 3);

    /* Check there's something for the shadows to map to */
    if ( !p2m_is_valid(p2mt) )
    {
        *sp = shadow_l1e_empty();
        goto done;
    }

    gflags = guest_l1e_get_flags(guest_entry);

    if ( unlikely(!(gflags & _PAGE_PRESENT)) )
    {
        /* If a guest l1 entry is not present, shadow with the magic 
         * guest-not-present entry. */
        if ( level == 1 )
            *sp = sh_l1e_gnp();
        else 
            *sp = shadow_l1e_empty();
        goto done;
    }

    if ( level == 1 && p2mt == p2m_mmio_dm )
    {
        /* Guest l1e maps emulated MMIO space */
        *sp = sh_l1e_mmio(target_gfn, gflags);
        if ( !d->arch.paging.shadow.has_fast_mmio_entries )
            d->arch.paging.shadow.has_fast_mmio_entries = 1;
        goto done;
    }

    // Must have a valid target_mfn unless this is a prefetch or an l1
    // pointing at MMIO space.  In the case of a prefetch, an invalid
    // mfn means that we can not usefully shadow anything, and so we
    // return early.
    //
    if ( !mfn_valid(target_mfn)
         && !(level == 1 && (!shadow_mode_refcounts(d) 
                             || p2mt == p2m_mmio_direct)) )
    {
        ASSERT((ft == ft_prefetch));
        *sp = shadow_l1e_empty();
        goto done;
    }

    // Propagate bits from the guest to the shadow.
    // Some of these may be overwritten, below.
    // Since we know the guest's PRESENT bit is set, we also set the shadow's
    // SHADOW_PRESENT bit.
    //
    pass_thru_flags = (_PAGE_DIRTY | _PAGE_ACCESSED | _PAGE_USER |
                       _PAGE_RW | _PAGE_PRESENT);
    if ( guest_supports_nx(v) )
        pass_thru_flags |= _PAGE_NX_BIT;
    if ( !shadow_mode_refcounts(d) && !mfn_valid(target_mfn) )
        pass_thru_flags |= _PAGE_PAT | _PAGE_PCD | _PAGE_PWT;
    sflags = gflags & pass_thru_flags;

    /*
     * For HVM domains with direct access to MMIO areas, set the correct
     * caching attributes in the shadows to match what was asked for.
     */
    if ( (level == 1) && is_hvm_domain(d) &&
         !list_empty(&(domain_hvm_iommu(d)->pdev_list)) &&
         !is_xen_heap_mfn(mfn_x(target_mfn)) )
    {
        unsigned int type;
        if ( hvm_get_mem_pinned_cacheattr(d, gfn_x(target_gfn), &type) )
            sflags |= pat_type_2_pte_flags(type);
        else if ( d->arch.hvm_domain.is_in_uc_mode )
            sflags |= pat_type_2_pte_flags(PAT_TYPE_UNCACHABLE);
        else
            sflags |= get_pat_flags(v,
                                    gflags,
                                    gfn_to_paddr(target_gfn),
                                    ((paddr_t)mfn_x(target_mfn)) << PAGE_SHIFT);
    }

    // Set the A&D bits for higher level shadows.
    // Higher level entries do not, strictly speaking, have dirty bits, but
    // since we use shadow linear tables, each of these entries may, at some
    // point in time, also serve as a shadow L1 entry.
    // By setting both the A&D bits in each of these, we eliminate the burden
    // on the hardware to update these bits on initial accesses.
    //
    if ( (level > 1) && !((SHADOW_PAGING_LEVELS == 3) && (level == 3)) )
        sflags |= _PAGE_ACCESSED | _PAGE_DIRTY;

    // If the A or D bit has not yet been set in the guest, then we must
    // prevent the corresponding kind of access.
    //
    if ( unlikely(!(gflags & _PAGE_ACCESSED)) )
        sflags &= ~_PAGE_PRESENT;

    /* D bits exist in L1es and PSE L2es */
    if ( unlikely(((level == 1) ||
                   ((level == 2) &&
                    (gflags & _PAGE_PSE) &&
                    guest_supports_superpages(v)))
                  && !(gflags & _PAGE_DIRTY)) )
        sflags &= ~_PAGE_RW;

    // shadow_mode_log_dirty support
    //
    // Only allow the guest write access to a page a) on a demand fault,
    // or b) if the page is already marked as dirty.
    //
    // (We handle log-dirty entirely inside the shadow code, without using the 
    // p2m_ram_logdirty p2m type: only HAP uses that.)
    if ( unlikely((level == 1) && shadow_mode_log_dirty(d)) )
    {
        if ( mfn_valid(target_mfn) ) {
            if ( ft & FETCH_TYPE_WRITE ) {
                /* CoW: make copy of page to buffer, then mark dirty */
                cow_copy(d, target_mfn, 1);
                paging_mark_dirty(d, mfn_x(target_mfn));
            }
            else if (!sh_mfn_is_dirty(d, target_mfn)) 
                sflags &= ~_PAGE_RW;
        }
    }

    /* Read-only memory */
    if ( p2mt == p2m_ram_ro ) 
        sflags &= ~_PAGE_RW;
    
    // protect guest page tables
    //
    if ( unlikely((level == 1) && sh_mfn_is_a_page_table(target_mfn)) )
    {
        if ( shadow_mode_trap_reads(d) )
        {
            // if we are trapping both reads & writes, then mark this page
            // as not present...
            //
            sflags &= ~_PAGE_PRESENT;
        }
        else
        {
            // otherwise, just prevent any writes...
            //
            sflags &= ~_PAGE_RW;
        }
    }

    // PV guests in 64-bit mode use two different page tables for user vs
    // supervisor permissions, making the guest's _PAGE_USER bit irrelevant.
    // It is always shadowed as present...
    if ( (GUEST_PAGING_LEVELS == 4) && !is_pv_32on64_domain(d) 
         && !is_hvm_domain(d) )
    {
        sflags |= _PAGE_USER;
    }

    *sp = shadow_l1e_from_mfn(target_mfn, sflags);

 done:
    SHADOW_DEBUG(PROPAGATE,
                 "%s level %u guest %" SH_PRI_gpte " shadow %" SH_PRI_pte "\n",
                 fetch_type_names[ft], level, guest_entry.l1, sp->l1);
}


/* These four wrappers give us a little bit of type-safety back around
 * the use of void-* pointers and intpte types in _sh_propagate(), and
 * allow the compiler to optimize out some level checks. */

#if GUEST_PAGING_LEVELS >= 4
static void
l4e_propagate_from_guest(struct vcpu *v, 
                         guest_l4e_t gl4e,
                         mfn_t sl3mfn,
                         shadow_l4e_t *sl4e,
                         fetch_type_t ft)
{
    _sh_propagate(v, gl4e.l4, sl3mfn, sl4e, 4, ft, p2m_ram_rw);
}

static void
l3e_propagate_from_guest(struct vcpu *v,
                         guest_l3e_t gl3e,
                         mfn_t sl2mfn, 
                         shadow_l3e_t *sl3e,
                         fetch_type_t ft)
{
    _sh_propagate(v, gl3e.l3, sl2mfn, sl3e, 3, ft, p2m_ram_rw);
}
#endif // GUEST_PAGING_LEVELS >= 4

static void
l2e_propagate_from_guest(struct vcpu *v, 
                         guest_l2e_t gl2e,
                         mfn_t sl1mfn,
                         shadow_l2e_t *sl2e,
                         fetch_type_t ft)
{
    _sh_propagate(v, gl2e.l2, sl1mfn, sl2e, 2, ft, p2m_ram_rw);
}

static void
l1e_propagate_from_guest(struct vcpu *v, 
                         guest_l1e_t gl1e,
                         mfn_t gmfn, 
                         shadow_l1e_t *sl1e,
                         fetch_type_t ft, 
                         p2m_type_t p2mt)
{
    _sh_propagate(v, gl1e.l1, gmfn, sl1e, 1, ft, p2mt);
}


/**************************************************************************/
/* These functions update shadow entries (and do bookkeeping on the shadow
 * tables they are in).  It is intended that they are the only
 * functions which ever write (non-zero) data onto a shadow page.
 */

static inline void safe_write_entry(void *dst, void *src) 
/* Copy one PTE safely when processors might be running on the
 * destination pagetable.   This does *not* give safety against
 * concurrent writes (that's what the shadow lock is for), just 
 * stops the hardware picking up partially written entries. */
{
    volatile unsigned long *d = dst;
    unsigned long *s = src;
    ASSERT(!((unsigned long) d & (sizeof (shadow_l1e_t) - 1)));
#if CONFIG_PAGING_LEVELS == 3
    /* In PAE mode, pagetable entries are larger
     * than machine words, so won't get written atomically.  We need to make
     * sure any other cpu running on these shadows doesn't see a
     * half-written entry.  Do this by marking the entry not-present first,
     * then writing the high word before the low word. */
    BUILD_BUG_ON(sizeof (shadow_l1e_t) != 2 * sizeof (unsigned long));
    d[0] = 0;
    d[1] = s[1];
    d[0] = s[0];
#else
    /* In 32-bit and 64-bit, sizeof(pte) == sizeof(ulong) == 1 word,
     * which will be an atomic write, since the entry is aligned. */
    BUILD_BUG_ON(sizeof (shadow_l1e_t) != sizeof (unsigned long));
    *d = *s;
#endif
}


static inline void 
shadow_write_entries(void *d, void *s, int entries, mfn_t mfn)
/* This function does the actual writes to shadow pages.
 * It must not be called directly, since it doesn't do the bookkeeping
 * that shadow_set_l*e() functions do. */
{
    shadow_l1e_t *dst = d;
    shadow_l1e_t *src = s;
    void *map = NULL;
    int i;

    /* Because we mirror access rights at all levels in the shadow, an
     * l2 (or higher) entry with the RW bit cleared will leave us with
     * no write access through the linear map.  
     * We detect that by writing to the shadow with copy_to_user() and 
     * using map_domain_page() to get a writeable mapping if we need to. */
    if ( __copy_to_user(d, d, sizeof (unsigned long)) != 0 ) 
    {
        perfc_incr(shadow_linear_map_failed);
        map = sh_map_domain_page(mfn);
        ASSERT(map != NULL);
        dst = map + ((unsigned long)dst & (PAGE_SIZE - 1));
    }


    for ( i = 0; i < entries; i++ )
        safe_write_entry(dst++, src++);

    if ( map != NULL ) sh_unmap_domain_page(map);
}

static inline int
perms_strictly_increased(u32 old_flags, u32 new_flags) 
/* Given the flags of two entries, are the new flags a strict
 * increase in rights over the old ones? */
{
    u32 of = old_flags & (_PAGE_PRESENT|_PAGE_RW|_PAGE_USER|_PAGE_NX);
    u32 nf = new_flags & (_PAGE_PRESENT|_PAGE_RW|_PAGE_USER|_PAGE_NX);
    /* Flip the NX bit, since it's the only one that decreases rights;
     * we calculate as if it were an "X" bit. */
    of ^= _PAGE_NX_BIT;
    nf ^= _PAGE_NX_BIT;
    /* If the changed bits are all set in the new flags, then rights strictly 
     * increased between old and new. */
    return ((of | (of ^ nf)) == nf);
}

static int inline
__shadow_get_page_from_l1e(shadow_l1e_t sl1e, struct domain *d, int cow_reset)
{
    int res;
    mfn_t mfn;
    struct domain *owner;

    ASSERT(!sh_l1e_is_magic(sl1e));

    if ( !shadow_mode_refcounts(d) )
        return 1;

    res = __get_page_from_l1e(sl1e, d, cow_reset);

    // If a privileged domain is attempting to install a map of a page it does
    // not own, we let it succeed anyway.
    //
    if ( unlikely(!res) &&
         IS_PRIV(d) &&
         !shadow_mode_translate(d) &&
         mfn_valid(mfn = shadow_l1e_get_mfn(sl1e)) &&
         (owner = page_get_owner(mfn_to_page(mfn))) &&
         (d != owner) )
    {
        res = get_page_from_l1e(sl1e, owner);
        SHADOW_PRINTK("privileged domain %d installs map of mfn %05lx "
                       "which is owned by domain %d: %s\n",
                       d->domain_id, mfn_x(mfn), owner->domain_id,
                       res ? "success" : "failed");
    }

    if ( unlikely(!res) )
    {
        perfc_incr(shadow_get_page_fail);
        SHADOW_PRINTK("failed: l1e=" SH_PRI_pte "\n");
    }

    return res;
}

static int inline
shadow_get_page_from_l1e(shadow_l1e_t sl1e, struct domain *d)
{
    return __shadow_get_page_from_l1e(sl1e, d, 0);
}

static void inline
shadow_put_page_from_l1e(shadow_l1e_t sl1e, struct domain *d)
{ 
    if ( !shadow_mode_refcounts(d) )
        return;

    put_page_from_l1e(sl1e, d);
}

#if GUEST_PAGING_LEVELS >= 4
static int shadow_set_l4e(struct vcpu *v, 
                          shadow_l4e_t *sl4e, 
                          shadow_l4e_t new_sl4e, 
                          mfn_t sl4mfn)
{
    int flags = 0, ok;
    shadow_l4e_t old_sl4e;
    paddr_t paddr;
    ASSERT(sl4e != NULL);
    old_sl4e = *sl4e;

    if ( old_sl4e.l4 == new_sl4e.l4 ) return 0; /* Nothing to do */
    
    paddr = ((((paddr_t)mfn_x(sl4mfn)) << PAGE_SHIFT) 
             | (((unsigned long)sl4e) & ~PAGE_MASK));

    if ( shadow_l4e_get_flags(new_sl4e) & _PAGE_PRESENT ) 
    {
        /* About to install a new reference */        
        mfn_t sl3mfn = shadow_l4e_get_mfn(new_sl4e);
        ok = sh_get_ref(v, sl3mfn, paddr);
        /* Are we pinning l3 shadows to handle wierd linux behaviour? */
        if ( sh_type_is_pinnable(v, SH_type_l3_64_shadow) )
            ok |= sh_pin(v, sl3mfn);
        if ( !ok )
        {
            domain_crash(v->domain);
            return SHADOW_SET_ERROR;
        }
    }

    /* Write the new entry */
    shadow_write_entries(sl4e, &new_sl4e, 1, sl4mfn);
    flags |= SHADOW_SET_CHANGED;

    if ( shadow_l4e_get_flags(old_sl4e) & _PAGE_PRESENT ) 
    {
        /* We lost a reference to an old mfn. */
        mfn_t osl3mfn = shadow_l4e_get_mfn(old_sl4e);
        if ( (mfn_x(osl3mfn) != mfn_x(shadow_l4e_get_mfn(new_sl4e)))
             || !perms_strictly_increased(shadow_l4e_get_flags(old_sl4e), 
                                          shadow_l4e_get_flags(new_sl4e)) )
        {
            flags |= SHADOW_SET_FLUSH;
        }
        sh_put_ref(v, osl3mfn, paddr);
    }
    return flags;
}

static int shadow_set_l3e(struct vcpu *v, 
                          shadow_l3e_t *sl3e, 
                          shadow_l3e_t new_sl3e, 
                          mfn_t sl3mfn)
{
    int flags = 0;
    shadow_l3e_t old_sl3e;
    paddr_t paddr;
    ASSERT(sl3e != NULL);
    old_sl3e = *sl3e;

    if ( old_sl3e.l3 == new_sl3e.l3 ) return 0; /* Nothing to do */

    paddr = ((((paddr_t)mfn_x(sl3mfn)) << PAGE_SHIFT) 
             | (((unsigned long)sl3e) & ~PAGE_MASK));
    
    if ( shadow_l3e_get_flags(new_sl3e) & _PAGE_PRESENT )
        /* About to install a new reference */        
        if ( !sh_get_ref(v, shadow_l3e_get_mfn(new_sl3e), paddr) )
        {
            domain_crash(v->domain);
            return SHADOW_SET_ERROR;
        } 

    /* Write the new entry */
    shadow_write_entries(sl3e, &new_sl3e, 1, sl3mfn);
    flags |= SHADOW_SET_CHANGED;

    if ( shadow_l3e_get_flags(old_sl3e) & _PAGE_PRESENT ) 
    {
        /* We lost a reference to an old mfn. */
        mfn_t osl2mfn = shadow_l3e_get_mfn(old_sl3e);
        if ( (mfn_x(osl2mfn) != mfn_x(shadow_l3e_get_mfn(new_sl3e))) ||
             !perms_strictly_increased(shadow_l3e_get_flags(old_sl3e), 
                                       shadow_l3e_get_flags(new_sl3e)) ) 
        {
            flags |= SHADOW_SET_FLUSH;
        }
        sh_put_ref(v, osl2mfn, paddr);
    }
    return flags;
}
#endif /* GUEST_PAGING_LEVELS >= 4 */ 

static int shadow_set_l2e(struct vcpu *v, 
                          shadow_l2e_t *sl2e, 
                          shadow_l2e_t new_sl2e, 
                          mfn_t sl2mfn)
{
    int flags = 0;
    shadow_l2e_t old_sl2e;
    paddr_t paddr;

#if GUEST_PAGING_LEVELS == 2 && SHADOW_PAGING_LEVELS > 2
    /* In 2-on-3 we work with pairs of l2es pointing at two-page
     * shadows.  Reference counting and up-pointers track from the first
     * page of the shadow to the first l2e, so make sure that we're 
     * working with those:     
     * Align the pointer down so it's pointing at the first of the pair */
    sl2e = (shadow_l2e_t *)((unsigned long)sl2e & ~(sizeof(shadow_l2e_t)));
    /* Align the mfn of the shadow entry too */
    new_sl2e.l2 &= ~(1<<PAGE_SHIFT);
#endif

    ASSERT(sl2e != NULL);
    old_sl2e = *sl2e;
    
    if ( old_sl2e.l2 == new_sl2e.l2 ) return 0; /* Nothing to do */
    
    paddr = ((((paddr_t)mfn_x(sl2mfn)) << PAGE_SHIFT)
             | (((unsigned long)sl2e) & ~PAGE_MASK));

    if ( shadow_l2e_get_flags(new_sl2e) & _PAGE_PRESENT ) 
        /* About to install a new reference */
        if ( !sh_get_ref(v, shadow_l2e_get_mfn(new_sl2e), paddr) )
        {
            domain_crash(v->domain);
            return SHADOW_SET_ERROR;
        } 

    /* Write the new entry */
#if GUEST_PAGING_LEVELS == 2 && SHADOW_PAGING_LEVELS > 2
    {
        shadow_l2e_t pair[2] = { new_sl2e, new_sl2e };
        /* The l1 shadow is two pages long and need to be pointed to by
         * two adjacent l1es.  The pair have the same flags, but point
         * at odd and even MFNs */
        ASSERT(!(pair[0].l2 & (1<<PAGE_SHIFT)));
        pair[1].l2 |= (1<<PAGE_SHIFT);
        shadow_write_entries(sl2e, &pair, 2, sl2mfn);
    }
#else /* normal case */
    shadow_write_entries(sl2e, &new_sl2e, 1, sl2mfn);
#endif
    flags |= SHADOW_SET_CHANGED;

    if ( shadow_l2e_get_flags(old_sl2e) & _PAGE_PRESENT ) 
    {
        /* We lost a reference to an old mfn. */
        mfn_t osl1mfn = shadow_l2e_get_mfn(old_sl2e);
        if ( (mfn_x(osl1mfn) != mfn_x(shadow_l2e_get_mfn(new_sl2e))) ||
             !perms_strictly_increased(shadow_l2e_get_flags(old_sl2e), 
                                       shadow_l2e_get_flags(new_sl2e)) ) 
        {
            flags |= SHADOW_SET_FLUSH;
        }
        sh_put_ref(v, osl1mfn, paddr);
    }
    return flags;
}

static inline int __shadow_set_l1e(struct vcpu *v, 
                                shadow_l1e_t *sl1e, 
                                shadow_l1e_t new_sl1e,
                                mfn_t sl1mfn,
                                int cow_reset)
{
    int flags = 0;
    struct domain *d = v->domain;
    shadow_l1e_t old_sl1e;
    ASSERT(sl1e != NULL);
    
    old_sl1e = *sl1e;

    if ( old_sl1e.l1 == new_sl1e.l1 ) return 0; /* Nothing to do */
    
    if ( (shadow_l1e_get_flags(new_sl1e) & _PAGE_PRESENT)
         && !sh_l1e_is_magic(new_sl1e) ) 
    {
        /* About to install a new reference */        
        if ( shadow_mode_refcounts(d) ) {
            if ( __shadow_get_page_from_l1e(new_sl1e, d, cow_reset) == 0 ) 
            {
                /* Doesn't look like a pagetable. */
                flags |= SHADOW_SET_ERROR;
                new_sl1e = shadow_l1e_empty();
            }
#ifdef COW_INVERSE_MAP
            if (unlikely(paging_mode_log_dirty(d)))
                invert_sh_table_insert(shadow_l1e_get_mfn(new_sl1e), sl1mfn);
#endif
        }
    } 

    /* Write the new entry */
    shadow_write_entries(sl1e, &new_sl1e, 1, sl1mfn);
    flags |= SHADOW_SET_CHANGED;

    if ( (shadow_l1e_get_flags(old_sl1e) & _PAGE_PRESENT) 
         && !sh_l1e_is_magic(old_sl1e) )
    {
        /* We lost a reference to an old mfn. */
        /* N.B. Unlike higher-level sets, never need an extra flush 
         * when writing an l1e.  Because it points to the same guest frame 
         * as the guest l1e did, it's the guest's responsibility to
         * trigger a flush later. */
        if ( shadow_mode_refcounts(d) ) 
        {
            shadow_put_page_from_l1e(old_sl1e, d);
#ifdef COW_INVERSE_MAP
            if (unlikely(paging_mode_log_dirty(d)))
                invert_sh_table_remove(shadow_l1e_get_mfn(old_sl1e), sl1mfn);
#endif
        } 
    }
    return flags;
}

static int shadow_set_l1e(struct vcpu *v, 
                          shadow_l1e_t *sl1e, 
                          shadow_l1e_t new_sl1e,
                          mfn_t sl1mfn)
{
    return __shadow_set_l1e(v, sl1e, new_sl1e, sl1mfn, 0);
}


/**************************************************************************/
/* Macros to walk pagetables.  These take the shadow of a pagetable and 
 * walk every "interesting" entry.  That is, they don't touch Xen mappings, 
 * and for 32-bit l2s shadowed onto PAE or 64-bit, they only touch every 
 * second entry (since pairs of entries are managed together). For multi-page
 * shadows they walk all pages.
 * 
 * Arguments are an MFN, the variable to point to each entry, a variable 
 * to indicate that we are done (we will shortcut to the end of the scan 
 * when _done != 0), a variable to indicate that we should avoid Xen mappings,
 * and the code. 
 *
 * WARNING: These macros have side-effects.  They change the values of both 
 * the pointer and the MFN. */ 

static inline void increment_ptr_to_guest_entry(void *ptr)
{
    if ( ptr )
    {
        guest_l1e_t **entry = ptr;
        (*entry)++;
    }
}

/* All kinds of l1: touch all entries */
#define _SHADOW_FOREACH_L1E(_sl1mfn, _sl1e, _gl1p, _done, _code)        \
do {                                                                    \
    int _i;                                                             \
    shadow_l1e_t *_sp = map_shadow_page((_sl1mfn));                     \
    ASSERT(mfn_to_shadow_page(_sl1mfn)->type == SH_type_l1_shadow       \
           || mfn_to_shadow_page(_sl1mfn)->type == SH_type_fl1_shadow); \
    for ( _i = 0; _i < SHADOW_L1_PAGETABLE_ENTRIES; _i++ )              \
    {                                                                   \
        (_sl1e) = _sp + _i;                                             \
        if ( shadow_l1e_get_flags(*(_sl1e)) & _PAGE_PRESENT )           \
            {_code}                                                     \
        if ( _done ) break;                                             \
        increment_ptr_to_guest_entry(_gl1p);                            \
    }                                                                   \
    unmap_shadow_page(_sp);                                             \
} while (0)

/* 32-bit l1, on PAE or 64-bit shadows: need to walk both pages of shadow */
#if GUEST_PAGING_LEVELS == 2 && SHADOW_PAGING_LEVELS > 2
#define SHADOW_FOREACH_L1E(_sl1mfn, _sl1e, _gl1p, _done,  _code)        \
do {                                                                    \
    int __done = 0;                                                     \
    _SHADOW_FOREACH_L1E(_sl1mfn, _sl1e, _gl1p,                          \
                         ({ (__done = _done); }), _code);               \
    _sl1mfn = _mfn(mfn_x(_sl1mfn) + 1);                                 \
    if ( !__done )                                                      \
        _SHADOW_FOREACH_L1E(_sl1mfn, _sl1e, _gl1p,                      \
                             ({ (__done = _done); }), _code);           \
} while (0)
#else /* Everything else; l1 shadows are only one page */
#define SHADOW_FOREACH_L1E(_sl1mfn, _sl1e, _gl1p, _done, _code)         \
       _SHADOW_FOREACH_L1E(_sl1mfn, _sl1e, _gl1p, _done, _code)
#endif
    

#if GUEST_PAGING_LEVELS == 2 && SHADOW_PAGING_LEVELS > 2

/* 32-bit l2 on PAE/64: four pages, touch every second entry, and avoid Xen */
#define SHADOW_FOREACH_L2E(_sl2mfn, _sl2e, _gl2p, _done, _dom, _code)     \
do {                                                                      \
    int _i, _j, __done = 0;                                               \
    int _xen = !shadow_mode_external(_dom);                               \
    ASSERT(mfn_to_shadow_page(_sl2mfn)->type == SH_type_l2_32_shadow);    \
    for ( _j = 0; _j < 4 && !__done; _j++ )                               \
    {                                                                     \
        shadow_l2e_t *_sp = map_shadow_page(_sl2mfn);                     \
        for ( _i = 0; _i < SHADOW_L2_PAGETABLE_ENTRIES; _i += 2 )         \
            if ( (!(_xen))                                                \
                 || ((_j * SHADOW_L2_PAGETABLE_ENTRIES) + _i)             \
                 < (HYPERVISOR_VIRT_START >> SHADOW_L2_PAGETABLE_SHIFT) ) \
            {                                                             \
                (_sl2e) = _sp + _i;                                       \
                if ( shadow_l2e_get_flags(*(_sl2e)) & _PAGE_PRESENT )     \
                    {_code}                                               \
                if ( (__done = (_done)) ) break;                          \
                increment_ptr_to_guest_entry(_gl2p);                      \
            }                                                             \
        unmap_shadow_page(_sp);                                           \
        _sl2mfn = _mfn(mfn_x(_sl2mfn) + 1);                               \
    }                                                                     \
} while (0)

#elif GUEST_PAGING_LEVELS == 2

/* 32-bit on 32-bit: avoid Xen entries */
#define SHADOW_FOREACH_L2E(_sl2mfn, _sl2e, _gl2p, _done, _dom, _code)      \
do {                                                                       \
    int _i;                                                                \
    int _xen = !shadow_mode_external(_dom);                                \
    shadow_l2e_t *_sp = map_shadow_page((_sl2mfn));                        \
    ASSERT(mfn_to_shadow_page(_sl2mfn)->type == SH_type_l2_32_shadow);     \
    for ( _i = 0; _i < SHADOW_L2_PAGETABLE_ENTRIES; _i++ )                 \
        if ( (!(_xen))                                                     \
             ||                                                            \
             (_i < (HYPERVISOR_VIRT_START >> SHADOW_L2_PAGETABLE_SHIFT)) ) \
        {                                                                  \
            (_sl2e) = _sp + _i;                                            \
            if ( shadow_l2e_get_flags(*(_sl2e)) & _PAGE_PRESENT )          \
                {_code}                                                    \
            if ( _done ) break;                                            \
            increment_ptr_to_guest_entry(_gl2p);                           \
        }                                                                  \
    unmap_shadow_page(_sp);                                                \
} while (0)

#elif GUEST_PAGING_LEVELS == 3

/* PAE: if it's an l2h, don't touch Xen mappings */
#define SHADOW_FOREACH_L2E(_sl2mfn, _sl2e, _gl2p, _done, _dom, _code)      \
do {                                                                       \
    int _i;                                                                \
    int _xen = !shadow_mode_external(_dom);                                \
    shadow_l2e_t *_sp = map_shadow_page((_sl2mfn));                        \
    ASSERT(mfn_to_shadow_page(_sl2mfn)->type == SH_type_l2_pae_shadow      \
           || mfn_to_shadow_page(_sl2mfn)->type == SH_type_l2h_pae_shadow);\
    for ( _i = 0; _i < SHADOW_L2_PAGETABLE_ENTRIES; _i++ )                 \
        if ( (!(_xen))                                                     \
             || mfn_to_shadow_page(_sl2mfn)->type != SH_type_l2h_pae_shadow\
             || ((_i + (3 * SHADOW_L2_PAGETABLE_ENTRIES))                  \
                 < (HYPERVISOR_VIRT_START >> SHADOW_L2_PAGETABLE_SHIFT)) ) \
        {                                                                  \
            (_sl2e) = _sp + _i;                                            \
            if ( shadow_l2e_get_flags(*(_sl2e)) & _PAGE_PRESENT )          \
                {_code}                                                    \
            if ( _done ) break;                                            \
            increment_ptr_to_guest_entry(_gl2p);                           \
        }                                                                  \
    unmap_shadow_page(_sp);                                                \
} while (0)

#else 

/* 64-bit l2: touch all entries except for PAE compat guests. */
#define SHADOW_FOREACH_L2E(_sl2mfn, _sl2e, _gl2p, _done, _dom, _code)       \
do {                                                                        \
    int _i;                                                                 \
    int _xen = !shadow_mode_external(_dom);                                 \
    shadow_l2e_t *_sp = map_shadow_page((_sl2mfn));                         \
    ASSERT(mfn_to_shadow_page(_sl2mfn)->type == SH_type_l2_64_shadow ||     \
           mfn_to_shadow_page(_sl2mfn)->type == SH_type_l2h_64_shadow);     \
    for ( _i = 0; _i < SHADOW_L2_PAGETABLE_ENTRIES; _i++ )                  \
    {                                                                       \
        if ( (!(_xen))                                                      \
             || !is_pv_32on64_domain(_dom)                                  \
             || mfn_to_shadow_page(_sl2mfn)->type != SH_type_l2h_64_shadow  \
             || (_i < COMPAT_L2_PAGETABLE_FIRST_XEN_SLOT(_dom)) )           \
        {                                                                   \
            (_sl2e) = _sp + _i;                                             \
            if ( shadow_l2e_get_flags(*(_sl2e)) & _PAGE_PRESENT )           \
                {_code}                                                     \
            if ( _done ) break;                                             \
            increment_ptr_to_guest_entry(_gl2p);                            \
        }                                                                   \
    }                                                                       \
    unmap_shadow_page(_sp);                                                 \
} while (0)

#endif /* different kinds of l2 */

#if GUEST_PAGING_LEVELS == 4

/* 64-bit l3: touch all entries */
#define SHADOW_FOREACH_L3E(_sl3mfn, _sl3e, _gl3p, _done, _code)         \
do {                                                                    \
    int _i;                                                             \
    shadow_l3e_t *_sp = map_shadow_page((_sl3mfn));                     \
    ASSERT(mfn_to_shadow_page(_sl3mfn)->type == SH_type_l3_64_shadow);  \
    for ( _i = 0; _i < SHADOW_L3_PAGETABLE_ENTRIES; _i++ )              \
    {                                                                   \
        (_sl3e) = _sp + _i;                                             \
        if ( shadow_l3e_get_flags(*(_sl3e)) & _PAGE_PRESENT )           \
            {_code}                                                     \
        if ( _done ) break;                                             \
        increment_ptr_to_guest_entry(_gl3p);                            \
    }                                                                   \
    unmap_shadow_page(_sp);                                             \
} while (0)

/* 64-bit l4: avoid Xen mappings */
#define SHADOW_FOREACH_L4E(_sl4mfn, _sl4e, _gl4p, _done, _dom, _code)   \
do {                                                                    \
    shadow_l4e_t *_sp = map_shadow_page((_sl4mfn));                     \
    int _xen = !shadow_mode_external(_dom);                             \
    int _i;                                                             \
    ASSERT(mfn_to_shadow_page(_sl4mfn)->type == SH_type_l4_64_shadow);  \
    for ( _i = 0; _i < SHADOW_L4_PAGETABLE_ENTRIES; _i++ )              \
    {                                                                   \
        if ( (!(_xen)) || is_guest_l4_slot(_dom, _i) )                  \
        {                                                               \
            (_sl4e) = _sp + _i;                                         \
            if ( shadow_l4e_get_flags(*(_sl4e)) & _PAGE_PRESENT )       \
                {_code}                                                 \
            if ( _done ) break;                                         \
        }                                                               \
        increment_ptr_to_guest_entry(_gl4p);                            \
    }                                                                   \
    unmap_shadow_page(_sp);                                             \
} while (0)

#endif



/**************************************************************************/
/* Functions to install Xen mappings and linear mappings in shadow pages */

// XXX -- this function should probably be moved to shadow-common.c, but that
//        probably wants to wait until the shadow types have been moved from
//        shadow-types.h to shadow-private.h
//
#if CONFIG_PAGING_LEVELS == 4 && GUEST_PAGING_LEVELS == 4
void sh_install_xen_entries_in_l4(struct vcpu *v, mfn_t gl4mfn, mfn_t sl4mfn)
{
    struct domain *d = v->domain;
    shadow_l4e_t *sl4e;

    sl4e = sh_map_domain_page(sl4mfn);
    ASSERT(sl4e != NULL);
    ASSERT(sizeof (l4_pgentry_t) == sizeof (shadow_l4e_t));
    
    /* Copy the common Xen mappings from the idle domain */
    memcpy(&sl4e[ROOT_PAGETABLE_FIRST_XEN_SLOT],
           &idle_pg_table[ROOT_PAGETABLE_FIRST_XEN_SLOT],
           ROOT_PAGETABLE_XEN_SLOTS * sizeof(l4_pgentry_t));

    /* Install the per-domain mappings for this domain */
    sl4e[shadow_l4_table_offset(PERDOMAIN_VIRT_START)] =
        shadow_l4e_from_mfn(page_to_mfn(virt_to_page(d->arch.mm_perdomain_l3)),
                            __PAGE_HYPERVISOR);

    /* Linear mapping */
    sl4e[shadow_l4_table_offset(SH_LINEAR_PT_VIRT_START)] =
        shadow_l4e_from_mfn(sl4mfn, __PAGE_HYPERVISOR);

    if ( shadow_mode_translate(v->domain) && !shadow_mode_external(v->domain) )
    {
        // linear tables may not be used with translated PV guests
        sl4e[shadow_l4_table_offset(LINEAR_PT_VIRT_START)] =
            shadow_l4e_empty();
    }
    else
    {
        sl4e[shadow_l4_table_offset(LINEAR_PT_VIRT_START)] =
            shadow_l4e_from_mfn(gl4mfn, __PAGE_HYPERVISOR);
    }

    if ( shadow_mode_translate(v->domain) )
    {
        /* install domain-specific P2M table */
        sl4e[shadow_l4_table_offset(RO_MPT_VIRT_START)] =
            shadow_l4e_from_mfn(pagetable_get_mfn(d->arch.phys_table),
                                __PAGE_HYPERVISOR);
    }

    if ( is_pv_32on64_domain(v->domain) )
    {
        /* install compat arg xlat entry */
        sl4e[shadow_l4_table_offset(COMPAT_ARG_XLAT_VIRT_BASE)] =
            shadow_l4e_from_mfn(
                    page_to_mfn(virt_to_page(d->arch.mm_arg_xlat_l3)),
                    __PAGE_HYPERVISOR);
    }

    sh_unmap_domain_page(sl4e);    
}
#endif

#if CONFIG_PAGING_LEVELS >= 3 && GUEST_PAGING_LEVELS >= 3
// For 3-on-3 PV guests, we need to make sure the xen mappings are in
// place, which means that we need to populate the l2h entry in the l3
// table.

static void sh_install_xen_entries_in_l2h(struct vcpu *v, mfn_t sl2hmfn)
{
    struct domain *d = v->domain;
    shadow_l2e_t *sl2e;
#if CONFIG_PAGING_LEVELS == 3
    int i;
#else

    if ( !is_pv_32on64_vcpu(v) )
        return;
#endif

    sl2e = sh_map_domain_page(sl2hmfn);
    ASSERT(sl2e != NULL);
    ASSERT(sizeof (l2_pgentry_t) == sizeof (shadow_l2e_t));
    
#if CONFIG_PAGING_LEVELS == 3

    /* Copy the common Xen mappings from the idle domain */
    memcpy(&sl2e[L2_PAGETABLE_FIRST_XEN_SLOT & (L2_PAGETABLE_ENTRIES-1)],
           &idle_pg_table_l2[L2_PAGETABLE_FIRST_XEN_SLOT],
           L2_PAGETABLE_XEN_SLOTS * sizeof(l2_pgentry_t));

    /* Install the per-domain mappings for this domain */
    for ( i = 0; i < PDPT_L2_ENTRIES; i++ )
        sl2e[shadow_l2_table_offset(PERDOMAIN_VIRT_START) + i] =
            shadow_l2e_from_mfn(
                page_to_mfn(virt_to_page(d->arch.mm_perdomain_pt) + i),
                __PAGE_HYPERVISOR);
    
    /* We don't set up a linear mapping here because we can't until this
     * l2h is installed in an l3e.  sh_update_linear_entries() handles
     * the linear mappings when CR3 (and so the fourth l3e) is loaded.  
     * We zero them here, just as a safety measure.
     */
    for ( i = 0; i < SHADOW_L3_PAGETABLE_ENTRIES; i++ )
        sl2e[shadow_l2_table_offset(LINEAR_PT_VIRT_START) + i] =
            shadow_l2e_empty();
    for ( i = 0; i < SHADOW_L3_PAGETABLE_ENTRIES; i++ )
        sl2e[shadow_l2_table_offset(SH_LINEAR_PT_VIRT_START) + i] =
            shadow_l2e_empty();

    if ( shadow_mode_translate(d) )
    {
        /* Install the domain-specific p2m table */
        l3_pgentry_t *p2m;
        ASSERT(pagetable_get_pfn(d->arch.phys_table) != 0);
        p2m = sh_map_domain_page(pagetable_get_mfn(d->arch.phys_table));
        for ( i = 0; i < MACHPHYS_MBYTES>>1; i++ )
        {
            sl2e[shadow_l2_table_offset(RO_MPT_VIRT_START) + i] =
                (l3e_get_flags(p2m[i]) & _PAGE_PRESENT)
                ? shadow_l2e_from_mfn(_mfn(l3e_get_pfn(p2m[i])),
                                      __PAGE_HYPERVISOR)
                : shadow_l2e_empty();
        }
        sh_unmap_domain_page(p2m);
    }

#else

    /* Copy the common Xen mappings from the idle domain */
    memcpy(
        &sl2e[COMPAT_L2_PAGETABLE_FIRST_XEN_SLOT(d)],
        &compat_idle_pg_table_l2[l2_table_offset(HIRO_COMPAT_MPT_VIRT_START)],
        COMPAT_L2_PAGETABLE_XEN_SLOTS(d) * sizeof(*sl2e));

#endif
    
    sh_unmap_domain_page(sl2e);
}
#endif


#if CONFIG_PAGING_LEVELS == 2 && GUEST_PAGING_LEVELS == 2
void sh_install_xen_entries_in_l2(struct vcpu *v, mfn_t gl2mfn, mfn_t sl2mfn)
{
    struct domain *d = v->domain;
    shadow_l2e_t *sl2e;
    int i;

    sl2e = sh_map_domain_page(sl2mfn);
    ASSERT(sl2e != NULL);
    ASSERT(sizeof (l2_pgentry_t) == sizeof (shadow_l2e_t));
    
    /* Copy the common Xen mappings from the idle domain */
    memcpy(&sl2e[L2_PAGETABLE_FIRST_XEN_SLOT],
           &idle_pg_table[L2_PAGETABLE_FIRST_XEN_SLOT],
           L2_PAGETABLE_XEN_SLOTS * sizeof(l2_pgentry_t));

    /* Install the per-domain mappings for this domain */
    for ( i = 0; i < PDPT_L2_ENTRIES; i++ )
        sl2e[shadow_l2_table_offset(PERDOMAIN_VIRT_START) + i] =
            shadow_l2e_from_mfn(
                page_to_mfn(virt_to_page(d->arch.mm_perdomain_pt) + i),
                __PAGE_HYPERVISOR);

    /* Linear mapping */
    sl2e[shadow_l2_table_offset(SH_LINEAR_PT_VIRT_START)] =
        shadow_l2e_from_mfn(sl2mfn, __PAGE_HYPERVISOR);

    if ( shadow_mode_translate(v->domain) && !shadow_mode_external(v->domain) )
    {
        // linear tables may not be used with translated PV guests
        sl2e[shadow_l2_table_offset(LINEAR_PT_VIRT_START)] =
            shadow_l2e_empty();
    }
    else
    {
        sl2e[shadow_l2_table_offset(LINEAR_PT_VIRT_START)] =
            shadow_l2e_from_mfn(gl2mfn, __PAGE_HYPERVISOR);
    }

    if ( shadow_mode_translate(d) )
    {
        /* install domain-specific P2M table */
        sl2e[shadow_l2_table_offset(RO_MPT_VIRT_START)] =
            shadow_l2e_from_mfn(pagetable_get_mfn(d->arch.phys_table),
                                __PAGE_HYPERVISOR);
    }

    sh_unmap_domain_page(sl2e);
}
#endif



/**************************************************************************/
/* Create a shadow of a given guest page.
 */
static mfn_t
sh_make_shadow(struct vcpu *v, mfn_t gmfn, u32 shadow_type)
{
    mfn_t smfn = shadow_alloc(v->domain, shadow_type, mfn_x(gmfn));
    SHADOW_DEBUG(MAKE_SHADOW, "(%05lx, %u)=>%05lx\n",
                  mfn_x(gmfn), shadow_type, mfn_x(smfn));

    if ( shadow_type != SH_type_l2_32_shadow 
         && shadow_type != SH_type_l2_pae_shadow 
         && shadow_type != SH_type_l2h_pae_shadow 
         && shadow_type != SH_type_l4_64_shadow )
        /* Lower-level shadow, not yet linked form a higher level */
        mfn_to_shadow_page(smfn)->up = 0;

#if GUEST_PAGING_LEVELS == 4
#if (SHADOW_OPTIMIZATIONS & SHOPT_LINUX_L3_TOPLEVEL) 
    if ( shadow_type == SH_type_l4_64_shadow &&
         unlikely(v->domain->arch.paging.shadow.opt_flags & SHOPT_LINUX_L3_TOPLEVEL) )
    {
        /* We're shadowing a new l4, but we've been assuming the guest uses
         * only one l4 per vcpu and context switches using an l4 entry. 
         * Count the number of active l4 shadows.  If there are enough
         * of them, decide that this isn't an old linux guest, and stop
         * pinning l3es.  This is not very quick but it doesn't happen
         * very often. */
        struct list_head *l, *t;
        struct shadow_page_info *sp;
        struct vcpu *v2;
        int l4count = 0, vcpus = 0;
        list_for_each(l, &v->domain->arch.paging.shadow.pinned_shadows)
        {
            sp = list_entry(l, struct shadow_page_info, list);
            if ( sp->type == SH_type_l4_64_shadow )
                l4count++;
        }
        for_each_vcpu ( v->domain, v2 ) 
            vcpus++;
        if ( l4count > 2 * vcpus ) 
        {
            /* Unpin all the pinned l3 tables, and don't pin any more. */
            list_for_each_safe(l, t, &v->domain->arch.paging.shadow.pinned_shadows)
            {
                sp = list_entry(l, struct shadow_page_info, list);
                if ( sp->type == SH_type_l3_64_shadow )
                    sh_unpin(v, shadow_page_to_mfn(sp));
            }
            v->domain->arch.paging.shadow.opt_flags &= ~SHOPT_LINUX_L3_TOPLEVEL;
        }
    }
#endif
#endif

    // Create the Xen mappings...
    if ( !shadow_mode_external(v->domain) )
    {
        switch (shadow_type) 
        {
#if CONFIG_PAGING_LEVELS == 4 && GUEST_PAGING_LEVELS == 4
        case SH_type_l4_shadow:
            sh_install_xen_entries_in_l4(v, gmfn, smfn); break;
#endif
#if CONFIG_PAGING_LEVELS >= 3 && GUEST_PAGING_LEVELS >= 3
        case SH_type_l2h_shadow:
            sh_install_xen_entries_in_l2h(v, smfn); break;
#endif
#if CONFIG_PAGING_LEVELS == 2 && GUEST_PAGING_LEVELS == 2
        case SH_type_l2_shadow:
            sh_install_xen_entries_in_l2(v, gmfn, smfn); break;
#endif
        default: /* Do nothing */ break;
        }
    }

    shadow_promote(v, gmfn, shadow_type);
    set_shadow_status(v, gmfn, shadow_type, smfn);

    return smfn;
}

/* Make a splintered superpage shadow */
static mfn_t
make_fl1_shadow(struct vcpu *v, gfn_t gfn)
{
    mfn_t smfn = shadow_alloc(v->domain, SH_type_fl1_shadow,
                               (unsigned long) gfn_x(gfn));

    SHADOW_DEBUG(MAKE_SHADOW, "(%" SH_PRI_gfn ")=>%" PRI_mfn "\n",
                  gfn_x(gfn), mfn_x(smfn));

    set_fl1_shadow_status(v, gfn, smfn);
    return smfn;
}


#if SHADOW_PAGING_LEVELS == GUEST_PAGING_LEVELS
mfn_t
sh_make_monitor_table(struct vcpu *v)
{
    struct domain *d = v->domain;

    ASSERT(pagetable_get_pfn(v->arch.monitor_table) == 0);
    
    /* Guarantee we can get the memory we need */
    shadow_prealloc(d, SH_type_monitor_table, CONFIG_PAGING_LEVELS - 1);

#if CONFIG_PAGING_LEVELS == 4    
    {
        mfn_t m4mfn;
        m4mfn = shadow_alloc(d, SH_type_monitor_table, 0);
        sh_install_xen_entries_in_l4(v, m4mfn, m4mfn);
        /* Remember the level of this table */
        mfn_to_page(m4mfn)->shadow_flags = 4;
#if SHADOW_PAGING_LEVELS < 4
        // Install a monitor l3 table in slot 0 of the l4 table.
        // This is used for shadow linear maps.
        {
            mfn_t m3mfn; 
            l4_pgentry_t *l4e;
            m3mfn = shadow_alloc(d, SH_type_monitor_table, 0);
            mfn_to_page(m3mfn)->shadow_flags = 3;
            l4e = sh_map_domain_page(m4mfn);
            l4e[0] = l4e_from_pfn(mfn_x(m3mfn), __PAGE_HYPERVISOR);
            sh_unmap_domain_page(l4e);
            if ( is_pv_32on64_vcpu(v) )
            {
                // Install a monitor l2 table in slot 3 of the l3 table.
                // This is used for all Xen entries.
                mfn_t m2mfn;
                l3_pgentry_t *l3e;
                m2mfn = shadow_alloc(d, SH_type_monitor_table, 0);
                mfn_to_page(m2mfn)->shadow_flags = 2;
                l3e = sh_map_domain_page(m3mfn);
                l3e[3] = l3e_from_pfn(mfn_x(m2mfn), _PAGE_PRESENT);
                sh_install_xen_entries_in_l2h(v, m2mfn);
                sh_unmap_domain_page(l3e);
            }
        }
#endif /* SHADOW_PAGING_LEVELS < 4 */
        return m4mfn;
    }

#elif CONFIG_PAGING_LEVELS == 3

    {
        mfn_t m3mfn, m2mfn; 
        l3_pgentry_t *l3e;
        l2_pgentry_t *l2e;
        int i;

        m3mfn = shadow_alloc(d, SH_type_monitor_table, 0);
        /* Remember the level of this table */
        mfn_to_page(m3mfn)->shadow_flags = 3;

        // Install a monitor l2 table in slot 3 of the l3 table.
        // This is used for all Xen entries, including linear maps
        m2mfn = shadow_alloc(d, SH_type_monitor_table, 0);
        mfn_to_page(m2mfn)->shadow_flags = 2;
        l3e = sh_map_domain_page(m3mfn);
        l3e[3] = l3e_from_pfn(mfn_x(m2mfn), _PAGE_PRESENT);
        sh_install_xen_entries_in_l2h(v, m2mfn);
        /* Install the monitor's own linear map */
        l2e = sh_map_domain_page(m2mfn);
        for ( i = 0; i < L3_PAGETABLE_ENTRIES; i++ )
            l2e[l2_table_offset(LINEAR_PT_VIRT_START) + i] =
                (l3e_get_flags(l3e[i]) & _PAGE_PRESENT) 
                ? l2e_from_pfn(l3e_get_pfn(l3e[i]), __PAGE_HYPERVISOR) 
                : l2e_empty();
        sh_unmap_domain_page(l2e);
        sh_unmap_domain_page(l3e);

        SHADOW_PRINTK("new monitor table: %#lx\n", mfn_x(m3mfn));
        return m3mfn;
    }

#elif CONFIG_PAGING_LEVELS == 2

    {
        mfn_t m2mfn;
        m2mfn = shadow_alloc(d, SH_type_monitor_table, 0);
        sh_install_xen_entries_in_l2(v, m2mfn, m2mfn);
        /* Remember the level of this table */
        mfn_to_page(m2mfn)->shadow_flags = 2;
        return m2mfn;
    }

#else
#error this should not happen
#endif /* CONFIG_PAGING_LEVELS */
}
#endif /* SHADOW_PAGING_LEVELS == GUEST_PAGING_LEVELS */

/**************************************************************************/
/* These functions also take a virtual address and return the level-N
 * shadow table mfn and entry, but they create the shadow pagetables if
 * they are needed.  The "demand" argument is non-zero when handling
 * a demand fault (so we know what to do about accessed bits &c).
 * If the necessary tables are not present in the guest, they return NULL. */

/* N.B. The use of GUEST_PAGING_LEVELS here is correct.  If the shadow has
 * more levels than the guest, the upper levels are always fixed and do not 
 * reflect any information from the guest, so we do not use these functions 
 * to access them. */

#if GUEST_PAGING_LEVELS >= 4
static shadow_l4e_t * shadow_get_and_create_l4e(struct vcpu *v, 
                                                walk_t *gw, 
                                                mfn_t *sl4mfn)
{
    /* There is always a shadow of the top level table.  Get it. */
    *sl4mfn = pagetable_get_mfn(v->arch.shadow_table[0]);
    /* Reading the top level table is always valid. */
    return sh_linear_l4_table(v) + shadow_l4_linear_offset(gw->va);
}

static shadow_l3e_t * shadow_get_and_create_l3e(struct vcpu *v, 
                                                walk_t *gw, 
                                                mfn_t *sl3mfn,
                                                fetch_type_t ft)
{
    mfn_t sl4mfn;
    shadow_l4e_t *sl4e;
    if ( !mfn_valid(gw->l3mfn) ) return NULL; /* No guest page. */
    /* Get the l4e */
    sl4e = shadow_get_and_create_l4e(v, gw, &sl4mfn);
    ASSERT(sl4e != NULL);
    if ( shadow_l4e_get_flags(*sl4e) & _PAGE_PRESENT ) 
    {
        *sl3mfn = shadow_l4e_get_mfn(*sl4e);
        ASSERT(mfn_valid(*sl3mfn));
    } 
    else 
    {
        int r;
        shadow_l4e_t new_sl4e;
        /* No l3 shadow installed: find and install it. */
        *sl3mfn = get_shadow_status(v, gw->l3mfn, SH_type_l3_shadow);
        if ( !mfn_valid(*sl3mfn) ) 
        {
            /* No l3 shadow of this page exists at all: make one. */
            *sl3mfn = sh_make_shadow(v, gw->l3mfn, SH_type_l3_shadow);
        }
        /* Install the new sl3 table in the sl4e */
        l4e_propagate_from_guest(v, gw->l4e, *sl3mfn, &new_sl4e, ft);
        r = shadow_set_l4e(v, sl4e, new_sl4e, sl4mfn);
        ASSERT((r & SHADOW_SET_FLUSH) == 0);
        if ( r & SHADOW_SET_ERROR )
            return NULL;
    }
    /* Now follow it down a level.  Guaranteed to succeed. */
    return sh_linear_l3_table(v) + shadow_l3_linear_offset(gw->va);
}
#endif /* GUEST_PAGING_LEVELS >= 4 */


static shadow_l2e_t * shadow_get_and_create_l2e(struct vcpu *v, 
                                                walk_t *gw, 
                                                mfn_t *sl2mfn,
                                                fetch_type_t ft)
{
#if GUEST_PAGING_LEVELS >= 4 /* 64bit... */
    mfn_t sl3mfn = _mfn(INVALID_MFN);
    shadow_l3e_t *sl3e;
    if ( !mfn_valid(gw->l2mfn) ) return NULL; /* No guest page. */
    /* Get the l3e */
    sl3e = shadow_get_and_create_l3e(v, gw, &sl3mfn, ft);
    if ( sl3e == NULL ) return NULL; 
    if ( shadow_l3e_get_flags(*sl3e) & _PAGE_PRESENT ) 
    {
        *sl2mfn = shadow_l3e_get_mfn(*sl3e);
        ASSERT(mfn_valid(*sl2mfn));
    } 
    else 
    {
        int r;
        shadow_l3e_t new_sl3e;
        unsigned int t = SH_type_l2_shadow;

        /* Tag compat L2 containing hypervisor (m2p) mappings */
        if ( is_pv_32on64_domain(v->domain) &&
             guest_l4_table_offset(gw->va) == 0 &&
             guest_l3_table_offset(gw->va) == 3 )
            t = SH_type_l2h_shadow;

        /* No l2 shadow installed: find and install it. */
        *sl2mfn = get_shadow_status(v, gw->l2mfn, t);
        if ( !mfn_valid(*sl2mfn) ) 
        {
            /* No l2 shadow of this page exists at all: make one. */
            *sl2mfn = sh_make_shadow(v, gw->l2mfn, t);
        }
        /* Install the new sl2 table in the sl3e */
        l3e_propagate_from_guest(v, gw->l3e, *sl2mfn, &new_sl3e, ft);
        r = shadow_set_l3e(v, sl3e, new_sl3e, sl3mfn);
        ASSERT((r & SHADOW_SET_FLUSH) == 0);
        if ( r & SHADOW_SET_ERROR )
            return NULL;        
    }
    /* Now follow it down a level.  Guaranteed to succeed. */
    return sh_linear_l2_table(v) + shadow_l2_linear_offset(gw->va);
#elif GUEST_PAGING_LEVELS == 3 /* PAE... */
    /* We never demand-shadow PAE l3es: they are only created in
     * sh_update_cr3().  Check if the relevant sl3e is present. */
    shadow_l3e_t *sl3e = ((shadow_l3e_t *)&v->arch.paging.shadow.l3table) 
        + shadow_l3_linear_offset(gw->va);
    if ( !(shadow_l3e_get_flags(*sl3e) & _PAGE_PRESENT) ) 
        return NULL;
    *sl2mfn = shadow_l3e_get_mfn(*sl3e);
    ASSERT(mfn_valid(*sl2mfn));
    return sh_linear_l2_table(v) + shadow_l2_linear_offset(gw->va);
#else /* 32bit... */
    /* There is always a shadow of the top level table.  Get it. */
    *sl2mfn = pagetable_get_mfn(v->arch.shadow_table[0]);
    /* This next line is important: the guest l2 has a 16k
     * shadow, we need to return the right mfn of the four. This
     * call will set it for us as a side-effect. */
    (void) shadow_l2_index(sl2mfn, guest_l2_table_offset(gw->va));
    /* Reading the top level table is always valid. */
    return sh_linear_l2_table(v) + shadow_l2_linear_offset(gw->va);
#endif 
}


static shadow_l1e_t * shadow_get_and_create_l1e(struct vcpu *v, 
                                                walk_t *gw, 
                                                mfn_t *sl1mfn,
                                                fetch_type_t ft)
{
    mfn_t sl2mfn;
    shadow_l2e_t *sl2e;

    /* Get the l2e */
    sl2e = shadow_get_and_create_l2e(v, gw, &sl2mfn, ft);
    if ( sl2e == NULL ) return NULL;
    /* Install the sl1 in the l2e if it wasn't there or if we need to
     * re-do it to fix a PSE dirty bit. */
    if ( shadow_l2e_get_flags(*sl2e) & _PAGE_PRESENT 
         && likely(ft != ft_demand_write
                   || (shadow_l2e_get_flags(*sl2e) & _PAGE_RW) 
                   || !(guest_l2e_get_flags(gw->l2e) & _PAGE_PSE)) )
    {
        *sl1mfn = shadow_l2e_get_mfn(*sl2e);
        ASSERT(mfn_valid(*sl1mfn));
    } 
    else 
    {
        shadow_l2e_t new_sl2e;
        int r, flags = guest_l2e_get_flags(gw->l2e);
        /* No l1 shadow installed: find and install it. */
        if ( !(flags & _PAGE_PRESENT) )
            return NULL; /* No guest page. */
        if ( guest_supports_superpages(v) && (flags & _PAGE_PSE) ) 
        {
            /* Splintering a superpage */
            gfn_t l2gfn = guest_l2e_get_gfn(gw->l2e);
            *sl1mfn = get_fl1_shadow_status(v, l2gfn);
            if ( !mfn_valid(*sl1mfn) ) 
            {
                /* No fl1 shadow of this superpage exists at all: make one. */
                *sl1mfn = make_fl1_shadow(v, l2gfn);
            }
        } 
        else 
        {
            /* Shadowing an actual guest l1 table */
            if ( !mfn_valid(gw->l1mfn) ) return NULL; /* No guest page. */
            *sl1mfn = get_shadow_status(v, gw->l1mfn, SH_type_l1_shadow);
            if ( !mfn_valid(*sl1mfn) ) 
            {
                /* No l1 shadow of this page exists at all: make one. */
                *sl1mfn = sh_make_shadow(v, gw->l1mfn, SH_type_l1_shadow);
            }
        }
        /* Install the new sl1 table in the sl2e */
        l2e_propagate_from_guest(v, gw->l2e, *sl1mfn, &new_sl2e, ft);
        r = shadow_set_l2e(v, sl2e, new_sl2e, sl2mfn);
        ASSERT((r & SHADOW_SET_FLUSH) == 0);        
        if ( r & SHADOW_SET_ERROR )
            return NULL;
        /* This next line is important: in 32-on-PAE and 32-on-64 modes,
         * the guest l1 table has an 8k shadow, and we need to return
         * the right mfn of the pair. This call will set it for us as a
         * side-effect.  (In all other cases, it's a no-op and will be
         * compiled out.) */
        (void) shadow_l1_index(sl1mfn, guest_l1_table_offset(gw->va));
    }
    /* Now follow it down a level.  Guaranteed to succeed. */
    return sh_linear_l1_table(v) + shadow_l1_linear_offset(gw->va);
}



/**************************************************************************/
/* Destructors for shadow tables: 
 * Unregister the shadow, decrement refcounts of any entries present in it,
 * and release the memory.
 *
 * N.B. These destructors do not clear the contents of the shadows.
 *      This allows us to delay TLB shootdowns until the page is being reused.
 *      See shadow_alloc() and shadow_free() for how this is handled.
 */

#if GUEST_PAGING_LEVELS >= 4
void sh_destroy_l4_shadow(struct vcpu *v, mfn_t smfn)
{
    shadow_l4e_t *sl4e;
    u32 t = mfn_to_shadow_page(smfn)->type;
    mfn_t gmfn, sl4mfn;

    SHADOW_DEBUG(DESTROY_SHADOW,
                  "%s(%05lx)\n", __func__, mfn_x(smfn));
    ASSERT(t == SH_type_l4_shadow);

    /* Record that the guest page isn't shadowed any more (in this type) */
    gmfn = _mfn(mfn_to_shadow_page(smfn)->backpointer);
    delete_shadow_status(v, gmfn, t, smfn);
    shadow_demote(v, gmfn, t);
    /* Decrement refcounts of all the old entries */
    sl4mfn = smfn; 
    SHADOW_FOREACH_L4E(sl4mfn, sl4e, 0, 0, v->domain, {
        if ( shadow_l4e_get_flags(*sl4e) & _PAGE_PRESENT ) 
        {
            sh_put_ref(v, shadow_l4e_get_mfn(*sl4e),
                       (((paddr_t)mfn_x(sl4mfn)) << PAGE_SHIFT) 
                       | ((unsigned long)sl4e & ~PAGE_MASK));
        }
    });
    
    /* Put the memory back in the pool */
    shadow_free(v->domain, smfn);
}

void sh_destroy_l3_shadow(struct vcpu *v, mfn_t smfn)
{
    shadow_l3e_t *sl3e;
    u32 t = mfn_to_shadow_page(smfn)->type;
    mfn_t gmfn, sl3mfn;

    SHADOW_DEBUG(DESTROY_SHADOW,
                  "%s(%05lx)\n", __func__, mfn_x(smfn));
    ASSERT(t == SH_type_l3_shadow);

    /* Record that the guest page isn't shadowed any more (in this type) */
    gmfn = _mfn(mfn_to_shadow_page(smfn)->backpointer);
    delete_shadow_status(v, gmfn, t, smfn);
    shadow_demote(v, gmfn, t);

    /* Decrement refcounts of all the old entries */
    sl3mfn = smfn; 
    SHADOW_FOREACH_L3E(sl3mfn, sl3e, 0, 0, {
        if ( shadow_l3e_get_flags(*sl3e) & _PAGE_PRESENT ) 
            sh_put_ref(v, shadow_l3e_get_mfn(*sl3e),
                        (((paddr_t)mfn_x(sl3mfn)) << PAGE_SHIFT) 
                        | ((unsigned long)sl3e & ~PAGE_MASK));
    });

    /* Put the memory back in the pool */
    shadow_free(v->domain, smfn);
}
#endif /* GUEST_PAGING_LEVELS >= 4 */


void sh_destroy_l2_shadow(struct vcpu *v, mfn_t smfn)
{
    shadow_l2e_t *sl2e;
    u32 t = mfn_to_shadow_page(smfn)->type;
    mfn_t gmfn, sl2mfn;

    SHADOW_DEBUG(DESTROY_SHADOW,
                  "%s(%05lx)\n", __func__, mfn_x(smfn));

#if GUEST_PAGING_LEVELS >= 3
    ASSERT(t == SH_type_l2_shadow || t == SH_type_l2h_shadow);
#else
    ASSERT(t == SH_type_l2_shadow);
#endif

    /* Record that the guest page isn't shadowed any more (in this type) */
    gmfn = _mfn(mfn_to_shadow_page(smfn)->backpointer);
    delete_shadow_status(v, gmfn, t, smfn);
    shadow_demote(v, gmfn, t);

    /* Decrement refcounts of all the old entries */
    sl2mfn = smfn;
    SHADOW_FOREACH_L2E(sl2mfn, sl2e, 0, 0, v->domain, {
        if ( shadow_l2e_get_flags(*sl2e) & _PAGE_PRESENT ) 
            sh_put_ref(v, shadow_l2e_get_mfn(*sl2e),
                        (((paddr_t)mfn_x(sl2mfn)) << PAGE_SHIFT) 
                        | ((unsigned long)sl2e & ~PAGE_MASK));
    });

    /* Put the memory back in the pool */
    shadow_free(v->domain, smfn);
}

void sh_destroy_l1_shadow(struct vcpu *v, mfn_t smfn)
{
    struct domain *d = v->domain;
    shadow_l1e_t *sl1e;
    u32 t = mfn_to_shadow_page(smfn)->type;

    SHADOW_DEBUG(DESTROY_SHADOW,
                  "%s(%05lx)\n", __func__, mfn_x(smfn));
    ASSERT(t == SH_type_l1_shadow || t == SH_type_fl1_shadow);

    /* Record that the guest page isn't shadowed any more (in this type) */
    if ( t == SH_type_fl1_shadow )
    {
        gfn_t gfn = _gfn(mfn_to_shadow_page(smfn)->backpointer);
        delete_fl1_shadow_status(v, gfn, smfn);
    }
    else 
    {
        mfn_t gmfn = _mfn(mfn_to_shadow_page(smfn)->backpointer);
        delete_shadow_status(v, gmfn, t, smfn);
        shadow_demote(v, gmfn, t);
    }
    
    if ( shadow_mode_refcounts(d) )
    {
        /* Decrement refcounts of all the old entries */
        mfn_t sl1mfn = smfn; 
        SHADOW_FOREACH_L1E(sl1mfn, sl1e, 0, 0, {
            if ( (shadow_l1e_get_flags(*sl1e) & _PAGE_PRESENT)
                 && !sh_l1e_is_magic(*sl1e) )
                shadow_put_page_from_l1e(*sl1e, d);
        });
    }
    
    /* Put the memory back in the pool */
    shadow_free(v->domain, smfn);
}

#if SHADOW_PAGING_LEVELS == GUEST_PAGING_LEVELS
void sh_destroy_monitor_table(struct vcpu *v, mfn_t mmfn)
{
    struct domain *d = v->domain;
    ASSERT(mfn_to_shadow_page(mmfn)->type == SH_type_monitor_table);

#if (CONFIG_PAGING_LEVELS == 4) && (SHADOW_PAGING_LEVELS != 4)
    /* Need to destroy the l3 monitor page in slot 0 too */
    {
        mfn_t m3mfn;
        l4_pgentry_t *l4e = sh_map_domain_page(mmfn);
        ASSERT(l4e_get_flags(l4e[0]) & _PAGE_PRESENT);
        m3mfn = _mfn(l4e_get_pfn(l4e[0]));
        if ( is_pv_32on64_vcpu(v) )
        {
            /* Need to destroy the l2 monitor page in slot 3 too */
            l3_pgentry_t *l3e = sh_map_domain_page(m3mfn);
            ASSERT(l3e_get_flags(l3e[3]) & _PAGE_PRESENT);
            shadow_free(d, _mfn(l3e_get_pfn(l3e[3])));
            sh_unmap_domain_page(l3e);
        }
        shadow_free(d, m3mfn);
        sh_unmap_domain_page(l4e);
    }
#elif CONFIG_PAGING_LEVELS == 3
    /* Need to destroy the l2 monitor page in slot 4 too */
    {
        l3_pgentry_t *l3e = sh_map_domain_page(mmfn);
        ASSERT(l3e_get_flags(l3e[3]) & _PAGE_PRESENT);
        shadow_free(d, _mfn(l3e_get_pfn(l3e[3])));
        sh_unmap_domain_page(l3e);
    }
#endif

    /* Put the memory back in the pool */
    shadow_free(d, mmfn);
}
#endif

/**************************************************************************/
/* Functions to destroy non-Xen mappings in a pagetable hierarchy.
 * These are called from common code when we are running out of shadow
 * memory, and unpinning all the top-level shadows hasn't worked. 
 *
 * This implementation is pretty crude and slow, but we hope that it won't 
 * be called very often. */

#if GUEST_PAGING_LEVELS == 2

void sh_unhook_32b_mappings(struct vcpu *v, mfn_t sl2mfn)
{    
    shadow_l2e_t *sl2e;
    SHADOW_FOREACH_L2E(sl2mfn, sl2e, 0, 0, v->domain, {
        (void) shadow_set_l2e(v, sl2e, shadow_l2e_empty(), sl2mfn);
    });
}

#elif GUEST_PAGING_LEVELS == 3

void sh_unhook_pae_mappings(struct vcpu *v, mfn_t sl2mfn)
/* Walk a PAE l2 shadow, unhooking entries from all the subshadows */
{
    shadow_l2e_t *sl2e;
    SHADOW_FOREACH_L2E(sl2mfn, sl2e, 0, 0, v->domain, {
        (void) shadow_set_l2e(v, sl2e, shadow_l2e_empty(), sl2mfn);
    });
}

#elif GUEST_PAGING_LEVELS == 4

void sh_unhook_64b_mappings(struct vcpu *v, mfn_t sl4mfn)
{
    shadow_l4e_t *sl4e;
    SHADOW_FOREACH_L4E(sl4mfn, sl4e, 0, 0, v->domain, {
        (void) shadow_set_l4e(v, sl4e, shadow_l4e_empty(), sl4mfn);
    });
}

#endif

/**************************************************************************/
/* Internal translation functions.
 * These functions require a pointer to the shadow entry that will be updated.
 */

/* These functions take a new guest entry, translate it to shadow and write 
 * the shadow entry.
 *
 * They return the same bitmaps as the shadow_set_lXe() functions.
 */

#if GUEST_PAGING_LEVELS >= 4
static int validate_gl4e(struct vcpu *v, void *new_ge, mfn_t sl4mfn, void *se)
{
    shadow_l4e_t new_sl4e;
    guest_l4e_t new_gl4e = *(guest_l4e_t *)new_ge;
    shadow_l4e_t *sl4p = se;
    mfn_t sl3mfn = _mfn(INVALID_MFN);
    struct domain *d = v->domain;
    p2m_type_t p2mt;
    int result = 0;

    perfc_incr(shadow_validate_gl4e_calls);

    if ( guest_l4e_get_flags(new_gl4e) & _PAGE_PRESENT )
    {
        gfn_t gl3gfn = guest_l4e_get_gfn(new_gl4e);
        mfn_t gl3mfn = gfn_to_mfn(d, gl3gfn, &p2mt);
        if ( p2m_is_ram(p2mt) )
            sl3mfn = get_shadow_status(v, gl3mfn, SH_type_l3_shadow);
        else
            result |= SHADOW_SET_ERROR;
    }
    l4e_propagate_from_guest(v, new_gl4e, sl3mfn, &new_sl4e, ft_prefetch);

    // check for updates to xen reserved slots
    if ( !shadow_mode_external(d) )
    {
        int shadow_index = (((unsigned long)sl4p & ~PAGE_MASK) /
                            sizeof(shadow_l4e_t));
        int reserved_xen_slot = !is_guest_l4_slot(d, shadow_index);

        if ( unlikely(reserved_xen_slot) )
        {
            // attempt by the guest to write to a xen reserved slot
            //
            SHADOW_PRINTK("%s out-of-range update "
                           "sl4mfn=%05lx index=0x%x val=%" SH_PRI_pte "\n",
                           __func__, mfn_x(sl4mfn), shadow_index, new_sl4e.l4);
            if ( shadow_l4e_get_flags(new_sl4e) & _PAGE_PRESENT )
            {
                SHADOW_ERROR("out-of-range l4e update\n");
                result |= SHADOW_SET_ERROR;
            }

            // do not call shadow_set_l4e...
            return result;
        }
    }

    result |= shadow_set_l4e(v, sl4p, new_sl4e, sl4mfn);
    return result;
}


static int validate_gl3e(struct vcpu *v, void *new_ge, mfn_t sl3mfn, void *se)
{
    shadow_l3e_t new_sl3e;
    guest_l3e_t new_gl3e = *(guest_l3e_t *)new_ge;
    shadow_l3e_t *sl3p = se;
    mfn_t sl2mfn = _mfn(INVALID_MFN);
    p2m_type_t p2mt;
    int result = 0;

    perfc_incr(shadow_validate_gl3e_calls);

    if ( guest_l3e_get_flags(new_gl3e) & _PAGE_PRESENT )
    {
        gfn_t gl2gfn = guest_l3e_get_gfn(new_gl3e);
        mfn_t gl2mfn = gfn_to_mfn(v->domain, gl2gfn, &p2mt);
        if ( p2m_is_ram(p2mt) )
            sl2mfn = get_shadow_status(v, gl2mfn, SH_type_l2_shadow);
        else
            result |= SHADOW_SET_ERROR;
    }
    l3e_propagate_from_guest(v, new_gl3e, sl2mfn, &new_sl3e, ft_prefetch);
    result |= shadow_set_l3e(v, sl3p, new_sl3e, sl3mfn);

    return result;
}
#endif // GUEST_PAGING_LEVELS >= 4

static int validate_gl2e(struct vcpu *v, void *new_ge, mfn_t sl2mfn, void *se)
{
    shadow_l2e_t new_sl2e;
    guest_l2e_t new_gl2e = *(guest_l2e_t *)new_ge;
    shadow_l2e_t *sl2p = se;
    mfn_t sl1mfn = _mfn(INVALID_MFN);
    p2m_type_t p2mt;
    int result = 0;

    perfc_incr(shadow_validate_gl2e_calls);

    if ( guest_l2e_get_flags(new_gl2e) & _PAGE_PRESENT )
    {
        gfn_t gl1gfn = guest_l2e_get_gfn(new_gl2e);
        if ( guest_supports_superpages(v) &&
             (guest_l2e_get_flags(new_gl2e) & _PAGE_PSE) )
        {
            // superpage -- need to look up the shadow L1 which holds the
            // splitters...
            sl1mfn = get_fl1_shadow_status(v, gl1gfn);
#if 0
            // XXX - it's possible that we want to do some kind of prefetch
            // for superpage fl1's here, but this is *not* on the demand path,
            // so we'll hold off trying that for now...
            //
            if ( !mfn_valid(sl1mfn) )
                sl1mfn = make_fl1_shadow(v, gl1gfn);
#endif
        }
        else
        {
            mfn_t gl1mfn = gfn_to_mfn(v->domain, gl1gfn, &p2mt);
            if ( p2m_is_ram(p2mt) )
                sl1mfn = get_shadow_status(v, gl1mfn, SH_type_l1_shadow);
            else
                result |= SHADOW_SET_ERROR;
        }
    }
    l2e_propagate_from_guest(v, new_gl2e, sl1mfn, &new_sl2e, ft_prefetch);

    // check for updates to xen reserved slots in PV guests...
    // XXX -- need to revisit this for PV 3-on-4 guests.
    //
#if SHADOW_PAGING_LEVELS < 4
#if CONFIG_PAGING_LEVELS == SHADOW_PAGING_LEVELS
    if ( !shadow_mode_external(v->domain) )
    {
        int shadow_index = (((unsigned long)sl2p & ~PAGE_MASK) /
                            sizeof(shadow_l2e_t));
        int reserved_xen_slot;

#if SHADOW_PAGING_LEVELS == 3
        reserved_xen_slot = 
            ((mfn_to_shadow_page(sl2mfn)->type == SH_type_l2h_pae_shadow) &&
             (shadow_index 
              >= (L2_PAGETABLE_FIRST_XEN_SLOT & (L2_PAGETABLE_ENTRIES-1))));
#else /* SHADOW_PAGING_LEVELS == 2 */
        reserved_xen_slot = (shadow_index >= L2_PAGETABLE_FIRST_XEN_SLOT);
#endif

        if ( unlikely(reserved_xen_slot) )
        {
            // attempt by the guest to write to a xen reserved slot
            //
            SHADOW_PRINTK("%s out-of-range update "
                           "sl2mfn=%05lx index=0x%x val=%" SH_PRI_pte "\n",
                           __func__, mfn_x(sl2mfn), shadow_index, new_sl2e.l2);
            if ( shadow_l2e_get_flags(new_sl2e) & _PAGE_PRESENT )
            {
                SHADOW_ERROR("out-of-range l2e update\n");
                result |= SHADOW_SET_ERROR;
            }

            // do not call shadow_set_l2e...
            return result;
        }
    }
#endif /* CONFIG_PAGING_LEVELS == SHADOW_PAGING_LEVELS */
#endif /* SHADOW_PAGING_LEVELS < 4 */

    result |= shadow_set_l2e(v, sl2p, new_sl2e, sl2mfn);

    return result;
}

static inline int 
__validate_gl1e(struct vcpu *v, void *new_ge, mfn_t sl1mfn, 
                void *se, int cow_reset)
{
    shadow_l1e_t new_sl1e;
    guest_l1e_t new_gl1e = *(guest_l1e_t *)new_ge;
    shadow_l1e_t *sl1p = se;
    gfn_t gfn;
    mfn_t gmfn;
    p2m_type_t p2mt;
    int result = 0;

    perfc_incr(shadow_validate_gl1e_calls);

    gfn = guest_l1e_get_gfn(new_gl1e);
    gmfn = gfn_to_mfn(v->domain, gfn, &p2mt);

    l1e_propagate_from_guest(v, new_gl1e, gmfn, &new_sl1e, ft_prefetch, p2mt);
    
    result |= __shadow_set_l1e(v, sl1p, new_sl1e, sl1mfn, cow_reset);
    return result;
}

static int validate_gl1e(struct vcpu *v, void *new_ge, mfn_t sl1mfn, void *se)
{
    return __validate_gl1e(v, new_ge, sl1mfn, se, 0);
}

/**************************************************************************/
/* Functions which translate and install the shadows of arbitrary guest 
 * entries that we have just seen the guest write. */


static inline int 
sh_map_and_validate(struct vcpu *v, mfn_t gmfn,
                     void *new_gp, u32 size, u32 sh_type, 
                     u32 (*shadow_index)(mfn_t *smfn, u32 idx),
                     int (*validate_ge)(struct vcpu *v, void *ge, 
                                        mfn_t smfn, void *se))
/* Generic function for mapping and validating. */
{
    mfn_t smfn, smfn2, map_mfn;
    shadow_l1e_t *sl1p;
    u32 shadow_idx, guest_idx;
    int result = 0;

    /* Align address and size to guest entry boundaries */
    size += (unsigned long)new_gp & (sizeof (guest_l1e_t) - 1);
    new_gp = (void *)((unsigned long)new_gp & ~(sizeof (guest_l1e_t) - 1));
    size = (size + sizeof (guest_l1e_t) - 1) & ~(sizeof (guest_l1e_t) - 1);
    ASSERT(size + (((unsigned long)new_gp) & ~PAGE_MASK) <= PAGE_SIZE);

    /* Map the shadow page */
    smfn = get_shadow_status(v, gmfn, sh_type);
    ASSERT(mfn_valid(smfn)); /* Otherwise we would not have been called */
    guest_idx = guest_index(new_gp);
    map_mfn = smfn;
    shadow_idx = shadow_index(&map_mfn, guest_idx);
    sl1p = map_shadow_page(map_mfn);

    /* Validate one entry at a time */
    while ( size )
    {
        smfn2 = smfn;
        guest_idx = guest_index(new_gp);
        shadow_idx = shadow_index(&smfn2, guest_idx);
        if ( mfn_x(smfn2) != mfn_x(map_mfn) )
        {
            /* We have moved to another page of the shadow */
            map_mfn = smfn2;
            unmap_shadow_page(sl1p);
            sl1p = map_shadow_page(map_mfn);
        }
        result |= validate_ge(v,
                              new_gp,
                              map_mfn,
                              &sl1p[shadow_idx]);
        size -= sizeof(guest_l1e_t);
        new_gp += sizeof(guest_l1e_t);
    }
    unmap_shadow_page(sl1p);
    return result;
}


int
sh_map_and_validate_gl4e(struct vcpu *v, mfn_t gl4mfn,
                          void *new_gl4p, u32 size)
{
#if GUEST_PAGING_LEVELS >= 4
    return sh_map_and_validate(v, gl4mfn, new_gl4p, size, 
                                SH_type_l4_shadow, 
                                shadow_l4_index, 
                                validate_gl4e);
#else // ! GUEST_PAGING_LEVELS >= 4
    SHADOW_ERROR("called in wrong paging mode!\n");
    BUG();
    return 0;
#endif 
}
    
int
sh_map_and_validate_gl3e(struct vcpu *v, mfn_t gl3mfn,
                          void *new_gl3p, u32 size)
{
#if GUEST_PAGING_LEVELS >= 4
    return sh_map_and_validate(v, gl3mfn, new_gl3p, size, 
                                SH_type_l3_shadow, 
                                shadow_l3_index, 
                                validate_gl3e);
#else // ! GUEST_PAGING_LEVELS >= 4
    SHADOW_ERROR("called in wrong paging mode!\n");
    BUG();
    return 0;
#endif
}

int
sh_map_and_validate_gl2e(struct vcpu *v, mfn_t gl2mfn,
                          void *new_gl2p, u32 size)
{
    return sh_map_and_validate(v, gl2mfn, new_gl2p, size, 
                                SH_type_l2_shadow, 
                                shadow_l2_index, 
                                validate_gl2e);
}

int
sh_map_and_validate_gl2he(struct vcpu *v, mfn_t gl2mfn,
                           void *new_gl2p, u32 size)
{
#if GUEST_PAGING_LEVELS >= 3
    return sh_map_and_validate(v, gl2mfn, new_gl2p, size, 
                                SH_type_l2h_shadow, 
                                shadow_l2_index, 
                                validate_gl2e);
#else /* Non-PAE guests don't have different kinds of l2 table */
    SHADOW_ERROR("called in wrong paging mode!\n");
    BUG();
    return 0;
#endif
}

int
sh_map_and_validate_gl1e(struct vcpu *v, mfn_t gl1mfn,
                          void *new_gl1p, u32 size)
{
    return sh_map_and_validate(v, gl1mfn, new_gl1p, size, 
                                SH_type_l1_shadow, 
                                shadow_l1_index, 
                                validate_gl1e);
}


/**************************************************************************/
/* Optimization: If we see two emulated writes of zeros to the same
 * page-table without another kind of page fault in between, we guess
 * that this is a batch of changes (for process destruction) and
 * unshadow the page so we don't take a pagefault on every entry.  This
 * should also make finding writeable mappings of pagetables much
 * easier. */

/* Look to see if this is the second emulated write in a row to this
 * page, and unshadow if it is */
static inline void check_for_early_unshadow(struct vcpu *v, mfn_t gmfn)
{
#if SHADOW_OPTIMIZATIONS & SHOPT_EARLY_UNSHADOW
    if ( v->arch.paging.shadow.last_emulated_mfn == mfn_x(gmfn) &&
         sh_mfn_is_a_page_table(gmfn) )
    {
        perfc_incr(shadow_early_unshadow);
        sh_remove_shadows(v, gmfn, 1, 0 /* Fast, can fail to unshadow */ );
    }
    v->arch.paging.shadow.last_emulated_mfn = mfn_x(gmfn);
#endif
}

/* Stop counting towards early unshadows, as we've seen a real page fault */
static inline void reset_early_unshadow(struct vcpu *v)
{
#if SHADOW_OPTIMIZATIONS & SHOPT_EARLY_UNSHADOW
    v->arch.paging.shadow.last_emulated_mfn = INVALID_MFN;
#endif
}



/**************************************************************************/
/* Optimization: Prefetch multiple L1 entries.  This is called after we have 
 * demand-faulted a shadow l1e in the fault handler, to see if it's
 * worth fetching some more.
 */

#if SHADOW_OPTIMIZATIONS & SHOPT_PREFETCH

/* XXX magic number */
#define PREFETCH_DISTANCE 32

static void sh_prefetch(struct vcpu *v, walk_t *gw, 
                        shadow_l1e_t *ptr_sl1e, mfn_t sl1mfn)
{
    int i, dist;
    gfn_t gfn;
    mfn_t gmfn;
    guest_l1e_t *gl1p = NULL, gl1e;
    shadow_l1e_t sl1e;
    u32 gflags;
    p2m_type_t p2mt;

    /* Prefetch no further than the end of the _shadow_ l1 MFN */
    dist = (PAGE_SIZE - ((unsigned long)ptr_sl1e & ~PAGE_MASK)) / sizeof sl1e;
    /* And no more than a maximum fetches-per-fault */
    if ( dist > PREFETCH_DISTANCE )
        dist = PREFETCH_DISTANCE;

    if ( mfn_valid(gw->l1mfn) )
    {
        /* Normal guest page; grab the next guest entry */
        gl1p = sh_map_domain_page(gw->l1mfn);
        gl1p += guest_l1_table_offset(gw->va);
    }

    for ( i = 1; i < dist ; i++ ) 
    {
        /* No point in prefetching if there's already a shadow */
        if ( ptr_sl1e[i].l1 != 0 )
            break;

        if ( mfn_valid(gw->l1mfn) )
        {
            /* Normal guest page; grab the next guest entry */
            gl1e = gl1p[i];
            /* Not worth continuing if we hit an entry that will need another
             * fault for A/D-bit propagation anyway */
            gflags = guest_l1e_get_flags(gl1e);
            if ( (gflags & _PAGE_PRESENT) 
                 && (!(gflags & _PAGE_ACCESSED)
                     || ((gflags & _PAGE_RW) && !(gflags & _PAGE_DIRTY))) )
                break;
        } 
        else 
        {
            /* Fragmented superpage, unless we've been called wrongly */
            ASSERT(guest_l2e_get_flags(gw->l2e) & _PAGE_PSE);
            /* Increment the l1e's GFN by the right number of guest pages */
            gl1e = guest_l1e_from_gfn(
                _gfn(gfn_x(guest_l1e_get_gfn(gw->l1e)) + i), 
                guest_l1e_get_flags(gw->l1e));
        }

        /* Look at the gfn that the l1e is pointing at */
        gfn = guest_l1e_get_gfn(gl1e);
        gmfn = gfn_to_mfn(v->domain, gfn, &p2mt);

        /* Propagate the entry.  */
        l1e_propagate_from_guest(v, gl1e, gmfn, &sl1e, ft_prefetch, p2mt);
        (void) shadow_set_l1e(v, ptr_sl1e + i, sl1e, sl1mfn);
    }
    if ( gl1p != NULL )
        sh_unmap_domain_page(gl1p);
}

#endif /* SHADOW_OPTIMIZATIONS & SHOPT_PREFETCH */


/**************************************************************************/
/* Entry points into the shadow code */

/* Called from pagefault handler in Xen, and from the HVM trap handlers
 * for pagefaults.  Returns 1 if this fault was an artefact of the
 * shadow code (and the guest should retry) or 0 if it is not (and the
 * fault should be handled elsewhere or passed to the guest). */

static int sh_page_fault(struct vcpu *v, 
                          unsigned long va, 
                          struct cpu_user_regs *regs)
{
    struct domain *d = v->domain;
    walk_t gw;
    gfn_t gfn;
    mfn_t gmfn, sl1mfn=_mfn(0);
    shadow_l1e_t sl1e, *ptr_sl1e;
    paddr_t gpa;
    struct sh_emulate_ctxt emul_ctxt;
    struct x86_emulate_ops *emul_ops;
    int r;
    fetch_type_t ft = 0;
    p2m_type_t p2mt;

    SHADOW_PRINTK("d:v=%u:%u va=%#lx err=%u, rip=%lx\n",
                  v->domain->domain_id, v->vcpu_id, va, regs->error_code,
                  regs->rip);

    perfc_incr(shadow_fault);
    //
    // XXX: Need to think about eventually mapping superpages directly in the
    //      shadow (when possible), as opposed to splintering them into a
    //      bunch of 4K maps.
    //

    /* Detect if this page fault happened while we were already in Xen
     * doing a shadow operation.  If that happens, the only thing we can
     * do is let Xen's normal fault handlers try to fix it.  In any case, 
     * a diagnostic trace of the fault will be more useful than 
     * a BUG() when we try to take the lock again. */
    if ( unlikely(shadow_locked_by_me(d)) )
    {
        SHADOW_ERROR("Recursive shadow fault: lock was taken by %s\n",
                     d->arch.paging.shadow.locker_function);
        return 0;
    }

    shadow_lock(d);
 
    shadow_audit_tables(v);
    
    if ( guest_walk_tables(v, va, &gw, regs->error_code, 1) != 0 )
    {
        perfc_incr(shadow_fault_bail_real_fault);
        goto not_a_shadow_fault;
    }

    /* It's possible that the guest has put pagetables in memory that it has 
     * already used for some special purpose (ioreq pages, or granted pages).
     * If that happens we'll have killed the guest already but it's still not 
     * safe to propagate entries out of the guest PT so get out now. */
    if ( unlikely(d->is_shutting_down) )
    {
        SHADOW_PRINTK("guest is shutting down\n");
        shadow_unlock(d);
        return 0;
    }

    sh_audit_gw(v, &gw);

    /* What kind of access are we dealing with? */
    ft = ((regs->error_code & PFEC_write_access)
          ? ft_demand_write : ft_demand_read);

    /* What mfn is the guest trying to access? */
    gfn = guest_l1e_get_gfn(gw.l1e);
    gmfn = gfn_to_mfn(d, gfn, &p2mt);

    if ( shadow_mode_refcounts(d) && 
         (!p2m_is_valid(p2mt) || (!p2m_is_mmio(p2mt) && !mfn_valid(gmfn))) )
    {
        perfc_incr(shadow_fault_bail_bad_gfn);
        SHADOW_PRINTK("BAD gfn=%"SH_PRI_gfn" gmfn=%"PRI_mfn"\n", 
                      gfn_x(gfn), mfn_x(gmfn));
        goto not_a_shadow_fault;
    }

#if (SHADOW_OPTIMIZATIONS & SHOPT_VIRTUAL_TLB)
    /* Remember this successful VA->GFN translation for later. */
    vtlb_insert(v, va >> PAGE_SHIFT, gfn_x(gfn), 
                regs->error_code | PFEC_page_present);
#endif /* (SHADOW_OPTIMIZATIONS & SHOPT_VIRTUAL_TLB) */

    /* Make sure there is enough free shadow memory to build a chain of
     * shadow tables. (We never allocate a top-level shadow on this path,
     * only a 32b l1, pae l1, or 64b l3+2+1. Note that while
     * SH_type_l1_shadow isn't correct in the latter case, all page
     * tables are the same size there.) */
    shadow_prealloc(d,
                    SH_type_l1_shadow,
                    GUEST_PAGING_LEVELS < 4 ? 1 : GUEST_PAGING_LEVELS - 1);

    /* Acquire the shadow.  This must happen before we figure out the rights 
     * for the shadow entry, since we might promote a page here. */
    ptr_sl1e = shadow_get_and_create_l1e(v, &gw, &sl1mfn, ft);
    if ( unlikely(ptr_sl1e == NULL) ) 
    {
        /* Couldn't get the sl1e!  Since we know the guest entries
         * are OK, this can only have been caused by a failed
         * shadow_set_l*e(), which will have crashed the guest.
         * Get out of the fault handler immediately. */
        ASSERT(d->is_shutting_down);
        shadow_unlock(d);
        return 0;
    }

    /* Calculate the shadow entry and write it */
    l1e_propagate_from_guest(v, gw.l1e, gmfn, &sl1e, ft, p2mt);
    r = shadow_set_l1e(v, ptr_sl1e, sl1e, sl1mfn);

#if SHADOW_OPTIMIZATIONS & SHOPT_PREFETCH
    /* Prefetch some more shadow entries */
    sh_prefetch(v, &gw, ptr_sl1e, sl1mfn);
#endif

    /* Need to emulate accesses to page tables */
    if ( sh_mfn_is_a_page_table(gmfn) )
    {
        if ( ft == ft_demand_write )
        {
            perfc_incr(shadow_fault_emulate_write);
            goto emulate;
        }
        else if ( shadow_mode_trap_reads(d) && ft == ft_demand_read )
        {
            perfc_incr(shadow_fault_emulate_read);
            goto emulate;
        }
    }

    /* Need to hand off device-model MMIO and writes to read-only
     * memory to the device model */
    if ( p2mt == p2m_mmio_dm 
         || (p2mt == p2m_ram_ro && ft == ft_demand_write) ) 
    {
        gpa = guest_walk_to_gpa(&gw);
        goto mmio;
    }

    /* In HVM guests, we force CR0.WP always to be set, so that the
     * pagetables are always write-protected.  If the guest thinks
     * CR0.WP is clear, we must emulate faulting supervisor writes to
     * allow the guest to write through read-only PTEs.  Emulate if the 
     * fault was a non-user write to a present page.  */
    if ( is_hvm_domain(d) 
         && unlikely(!hvm_wp_enabled(v)) 
         && regs->error_code == (PFEC_write_access|PFEC_page_present) )
    {
        perfc_incr(shadow_fault_emulate_wp);
        goto emulate;
    }

    perfc_incr(shadow_fault_fixed);
    d->arch.paging.log_dirty.fault_count++;
    
    if (paging_mode_log_dirty(v->domain))
        cow.pf_count++;

    reset_early_unshadow(v);

 done:
    sh_audit_gw(v, &gw);
    SHADOW_PRINTK("fixed\n");
    shadow_audit_tables(v);
    shadow_unlock(d);
    return EXCRET_fault_fixed;

 emulate:
    if ( !shadow_mode_refcounts(d) || !guest_mode(regs) )
        goto not_a_shadow_fault;

    /*
     * We do not emulate user writes. Instead we use them as a hint that the
     * page is no longer a page table. This behaviour differs from native, but
     * it seems very unlikely that any OS grants user access to page tables.
     */
    if ( (regs->error_code & PFEC_user_mode) )
    {
        SHADOW_PRINTK("user-mode fault to PT, unshadowing mfn %#lx\n", 
                      mfn_x(gmfn));
        perfc_incr(shadow_fault_emulate_failed);
        sh_remove_shadows(v, gmfn, 0 /* thorough */, 1 /* must succeed */);
        goto done;
    }

    if ( is_hvm_domain(d) )
    {
        /*
         * If we are in the middle of injecting an exception or interrupt then
         * we should not emulate: it is not the instruction at %eip that caused
         * the fault. Furthermore it is almost certainly the case the handler
         * stack is currently considered to be a page table, so we should
         * unshadow the faulting page before exiting.
         */
        if ( unlikely(hvm_event_pending(v)) )
        {
            gdprintk(XENLOG_DEBUG, "write to pagetable during event "
                     "injection: cr2=%#lx, mfn=%#lx\n", 
                     va, mfn_x(gmfn));
            sh_remove_shadows(v, gmfn, 0 /* thorough */, 1 /* must succeed */);
            goto done;
        }
    }

    SHADOW_PRINTK("emulate: eip=%#lx esp=%#lx\n", 
                  (unsigned long)regs->eip, (unsigned long)regs->esp);

    /*
     * We don't need to hold the lock for the whole emulation; we will
     * take it again when we write to the pagetables.
     */
    sh_audit_gw(v, &gw);
    shadow_audit_tables(v);
    shadow_unlock(d);

    emul_ops = shadow_init_emulation(&emul_ctxt, regs);

    r = x86_emulate(&emul_ctxt.ctxt, emul_ops);

    /*
     * NB. We do not unshadow on X86EMUL_EXCEPTION. It's not clear that it
     * would be a good unshadow hint. If we *do* decide to unshadow-on-fault
     * then it must be 'failable': we cannot require the unshadow to succeed.
     */
    if ( r == X86EMUL_UNHANDLEABLE )
    {
        SHADOW_PRINTK("emulator failure, unshadowing mfn %#lx\n", 
                       mfn_x(gmfn));
        perfc_incr(shadow_fault_emulate_failed);
        /* If this is actually a page table, then we have a bug, and need 
         * to support more operations in the emulator.  More likely, 
         * though, this is a hint that this page should not be shadowed. */
        shadow_remove_all_shadows(v, gmfn);
    }

    SHADOW_PRINTK("emulated\n");
    return EXCRET_fault_fixed;

 mmio:
    if ( !guest_mode(regs) )
        goto not_a_shadow_fault;
    perfc_incr(shadow_fault_mmio);

    sh_audit_gw(v, &gw);
    SHADOW_PRINTK("mmio %#"PRIpaddr"\n", gpa);
    shadow_audit_tables(v);
    reset_early_unshadow(v);
    shadow_unlock(d);
    handle_mmio(gpa);
    return EXCRET_fault_fixed;

 not_a_shadow_fault:
    sh_audit_gw(v, &gw);
    SHADOW_PRINTK("not a shadow fault\n");
    shadow_audit_tables(v);
    reset_early_unshadow(v);
    shadow_unlock(d);
    return 0;
}


static int
sh_invlpg(struct vcpu *v, unsigned long va)
/* Called when the guest requests an invlpg.  Returns 1 if the invlpg
 * instruction should be issued on the hardware, or 0 if it's safe not
 * to do so. */
{
    shadow_l2e_t sl2e;
    
    perfc_incr(shadow_invlpg);

#if (SHADOW_OPTIMIZATIONS & SHOPT_VIRTUAL_TLB)
    /* No longer safe to use cached gva->gfn translations */
    vtlb_flush(v);
#endif

    /* First check that we can safely read the shadow l2e.  SMP/PAE linux can
     * run as high as 6% of invlpg calls where we haven't shadowed the l2 
     * yet. */
#if SHADOW_PAGING_LEVELS == 4
    {
        shadow_l3e_t sl3e;
        if ( !(shadow_l4e_get_flags(
                   sh_linear_l4_table(v)[shadow_l4_linear_offset(va)])
               & _PAGE_PRESENT) )
            return 0;
        /* This must still be a copy-from-user because we don't have the
         * shadow lock, and the higher-level shadows might disappear
         * under our feet. */
        if ( __copy_from_user(&sl3e, (sh_linear_l3_table(v) 
                                      + shadow_l3_linear_offset(va)),
                              sizeof (sl3e)) != 0 )
        {
            perfc_incr(shadow_invlpg_fault);
            return 0;
        }
        if ( (!shadow_l3e_get_flags(sl3e) & _PAGE_PRESENT) )
            return 0;
    }
#elif SHADOW_PAGING_LEVELS == 3
    if ( !(l3e_get_flags(v->arch.paging.shadow.l3table[shadow_l3_linear_offset(va)])
           & _PAGE_PRESENT) )
        // no need to flush anything if there's no SL2...
        return 0;
#endif

    /* This must still be a copy-from-user because we don't have the shadow
     * lock, and the higher-level shadows might disappear under our feet. */
    if ( __copy_from_user(&sl2e, 
                          sh_linear_l2_table(v) + shadow_l2_linear_offset(va),
                          sizeof (sl2e)) != 0 )
    {
        perfc_incr(shadow_invlpg_fault);
        return 0;
    }

    // If there's nothing shadowed for this particular sl2e, then
    // there is no need to do an invlpg, either...
    //
    if ( !(shadow_l2e_get_flags(sl2e) & _PAGE_PRESENT) )
        return 0;

    // Check to see if the SL2 is a splintered superpage...
    // If so, then we'll need to flush the entire TLB (because that's
    // easier than invalidating all of the individual 4K pages).
    //
    if ( mfn_to_shadow_page(shadow_l2e_get_mfn(sl2e))->type
         == SH_type_fl1_shadow )
    {
        flush_tlb_local();
        return 0;
    }

    return 1;
}


static unsigned long
sh_gva_to_gfn(struct vcpu *v, unsigned long va, uint32_t *pfec)
/* Called to translate a guest virtual address to what the *guest*
 * pagetables would map it to. */
{
    walk_t gw;
    gfn_t gfn;

#if (SHADOW_OPTIMIZATIONS & SHOPT_VIRTUAL_TLB)
    /* Check the vTLB cache first */
    unsigned long vtlb_gfn = vtlb_lookup(v, va, pfec[0]);
    if ( VALID_GFN(vtlb_gfn) ) 
        return vtlb_gfn;
#endif /* (SHADOW_OPTIMIZATIONS & SHOPT_VIRTUAL_TLB) */

    if ( guest_walk_tables(v, va, &gw, pfec[0], 0) != 0 )
    {
        if ( !(guest_l1e_get_flags(gw.l1e) & _PAGE_PRESENT) )
            pfec[0] &= ~PFEC_page_present;
        return INVALID_GFN;
    }
    gfn = guest_walk_to_gfn(&gw);

#if (SHADOW_OPTIMIZATIONS & SHOPT_VIRTUAL_TLB)
    /* Remember this successful VA->GFN translation for later. */
    vtlb_insert(v, va >> PAGE_SHIFT, gfn_x(gfn), pfec[0]);
#endif /* (SHADOW_OPTIMIZATIONS & SHOPT_VIRTUAL_TLB) */

    return gfn_x(gfn);
}


static inline void
sh_update_linear_entries(struct vcpu *v)
/* Sync up all the linear mappings for this vcpu's pagetables */
{
    struct domain *d = v->domain;

    /* Linear pagetables in PV guests
     * ------------------------------
     *
     * Guest linear pagetables, which map the guest pages, are at
     * LINEAR_PT_VIRT_START.  Shadow linear pagetables, which map the
     * shadows, are at SH_LINEAR_PT_VIRT_START.  Most of the time these
     * are set up at shadow creation time, but (of course!) the PAE case
     * is subtler.  Normal linear mappings are made by having an entry
     * in the top-level table that points to itself (shadow linear) or
     * to the guest top-level table (guest linear).  For PAE, to set up
     * a linear map requires us to copy the four top-level entries into 
     * level-2 entries.  That means that every time we change a PAE l3e,
     * we need to reflect the change into the copy.
     *
     * Linear pagetables in HVM guests
     * -------------------------------
     *
     * For HVM guests, the linear pagetables are installed in the monitor
     * tables (since we can't put them in the shadow).  Shadow linear
     * pagetables, which map the shadows, are at SH_LINEAR_PT_VIRT_START,
     * and we use the linear pagetable slot at LINEAR_PT_VIRT_START for 
     * a linear pagetable of the monitor tables themselves.  We have 
     * the same issue of having to re-copy PAE l3 entries whevever we use
     * PAE shadows. 
     *
     * Because HVM guests run on the same monitor tables regardless of the 
     * shadow tables in use, the linear mapping of the shadow tables has to 
     * be updated every time v->arch.shadow_table changes. 
     */

    /* Don't try to update the monitor table if it doesn't exist */
    if ( shadow_mode_external(d) 
         && pagetable_get_pfn(v->arch.monitor_table) == 0 ) 
        return;

#if (CONFIG_PAGING_LEVELS == 4) && (SHADOW_PAGING_LEVELS == 4)
    
    /* For PV, one l4e points at the guest l4, one points at the shadow
     * l4.  No maintenance required. 
     * For HVM, just need to update the l4e that points to the shadow l4. */

    if ( shadow_mode_external(d) )
    {
        /* Use the linear map if we can; otherwise make a new mapping */
        if ( v == current ) 
        {
            __linear_l4_table[l4_linear_offset(SH_LINEAR_PT_VIRT_START)] = 
                l4e_from_pfn(pagetable_get_pfn(v->arch.shadow_table[0]),
                             __PAGE_HYPERVISOR);
        } 
        else
        { 
            l4_pgentry_t *ml4e;
            ml4e = sh_map_domain_page(pagetable_get_mfn(v->arch.monitor_table));
            ml4e[l4_table_offset(SH_LINEAR_PT_VIRT_START)] = 
                l4e_from_pfn(pagetable_get_pfn(v->arch.shadow_table[0]),
                             __PAGE_HYPERVISOR);
            sh_unmap_domain_page(ml4e);
        }
    }

#elif (CONFIG_PAGING_LEVELS == 4) && (SHADOW_PAGING_LEVELS == 3)

    /* PV: XXX
     *
     * HVM: To give ourselves a linear map of the  shadows, we need to
     * extend a PAE shadow to 4 levels.  We do this by  having a monitor
     * l3 in slot 0 of the monitor l4 table, and  copying the PAE l3
     * entries into it.  Then, by having the monitor l4e for shadow
     * pagetables also point to the monitor l4, we can use it to access
     * the shadows.
     */

    if ( shadow_mode_external(d) )
    {
        /* Install copies of the shadow l3es into the monitor l3 table.
         * The monitor l3 table is hooked into slot 0 of the monitor
         * l4 table, so we use l3 linear indices 0 to 3 */
        shadow_l3e_t *sl3e;
        l3_pgentry_t *ml3e;
        mfn_t l3mfn;
        int i;

        /* Use linear mappings if we can; otherwise make new mappings */
        if ( v == current ) 
        {
            ml3e = __linear_l3_table;
            l3mfn = _mfn(l4e_get_pfn(__linear_l4_table[0]));
        }
        else 
        {   
            l4_pgentry_t *ml4e;
            ml4e = sh_map_domain_page(pagetable_get_mfn(v->arch.monitor_table));
            ASSERT(l4e_get_flags(ml4e[0]) & _PAGE_PRESENT);
            l3mfn = _mfn(l4e_get_pfn(ml4e[0]));
            ml3e = sh_map_domain_page(l3mfn);
            sh_unmap_domain_page(ml4e);
        }

        /* Shadow l3 tables are made up by sh_update_cr3 */
        sl3e = v->arch.paging.shadow.l3table;

        for ( i = 0; i < SHADOW_L3_PAGETABLE_ENTRIES; i++ )
        {
            ml3e[i] = 
                (shadow_l3e_get_flags(sl3e[i]) & _PAGE_PRESENT) 
                ? l3e_from_pfn(mfn_x(shadow_l3e_get_mfn(sl3e[i])), 
                               __PAGE_HYPERVISOR) 
                : l3e_empty();
        }

        if ( v != current ) 
            sh_unmap_domain_page(ml3e);
    }
    else
        domain_crash(d); /* XXX */

#elif CONFIG_PAGING_LEVELS == 3

    /* PV: need to copy the guest's l3 entries into the guest-linear-map l2
     * entries in the shadow, and the shadow's l3 entries into the 
     * shadow-linear-map l2 entries in the shadow.  This is safe to do 
     * because Xen does not let guests share high-slot l2 tables between l3s,
     * so we know we're not treading on anyone's toes. 
     *
     * HVM: need to copy the shadow's l3 entries into the
     * shadow-linear-map l2 entries in the monitor table.  This is safe
     * because we have one monitor table for each vcpu.  The monitor's
     * own l3es don't need to be copied because they never change.  
     * XXX That might change if we start stuffing things into the rest
     * of the monitor's virtual address space. 
     */ 
    {
        l2_pgentry_t *l2e, new_l2e;
        shadow_l3e_t *guest_l3e = NULL, *shadow_l3e;
        int i;
        int unmap_l2e = 0;

#if GUEST_PAGING_LEVELS == 2

        /* Shadow l3 tables were built by sh_update_cr3 */
        BUG_ON(!shadow_mode_external(d)); /* PV 2-on-3 is unsupported */
        shadow_l3e = (shadow_l3e_t *)&v->arch.paging.shadow.l3table;
        
#else /* GUEST_PAGING_LEVELS == 3 */
        
        shadow_l3e = (shadow_l3e_t *)&v->arch.paging.shadow.l3table;
        guest_l3e = (guest_l3e_t *)&v->arch.paging.shadow.gl3e;

#endif /* GUEST_PAGING_LEVELS */
        
        /* Choose where to write the entries, using linear maps if possible */
        if ( shadow_mode_external(d) )
        {
            if ( v == current )
            {
                /* From the monitor tables, it's safe to use linear maps
                 * to update monitor l2s */
                l2e = __linear_l2_table + (3 * L2_PAGETABLE_ENTRIES);
            }
            else
            {
                /* Map the monitor table's high l2 */
                l3_pgentry_t *l3e;
                l3e = sh_map_domain_page(
                    pagetable_get_mfn(v->arch.monitor_table));
                ASSERT(l3e_get_flags(l3e[3]) & _PAGE_PRESENT);
                l2e = sh_map_domain_page(_mfn(l3e_get_pfn(l3e[3])));
                unmap_l2e = 1;
                sh_unmap_domain_page(l3e);
            }
        }
        else 
        {
            /* Map the shadow table's high l2 */
            ASSERT(shadow_l3e_get_flags(shadow_l3e[3]) & _PAGE_PRESENT);
            l2e = sh_map_domain_page(shadow_l3e_get_mfn(shadow_l3e[3]));
            unmap_l2e = 1;
        }
        
        /* Write linear mapping of guest (only in PV, and only when 
         * not translated). */
        if ( !shadow_mode_translate(d) )
        {
            for ( i = 0; i < SHADOW_L3_PAGETABLE_ENTRIES; i++ )
            {
                new_l2e = 
                    ((shadow_l3e_get_flags(guest_l3e[i]) & _PAGE_PRESENT)
                     ? l2e_from_pfn(mfn_x(shadow_l3e_get_mfn(guest_l3e[i])),
                                    __PAGE_HYPERVISOR) 
                     : l2e_empty());
                safe_write_entry(
                    &l2e[l2_table_offset(LINEAR_PT_VIRT_START) + i],
                    &new_l2e);
            }
        }
        
        /* Write linear mapping of shadow. */
        for ( i = 0; i < SHADOW_L3_PAGETABLE_ENTRIES; i++ )
        {
            new_l2e = (shadow_l3e_get_flags(shadow_l3e[i]) & _PAGE_PRESENT) 
                ? l2e_from_pfn(mfn_x(shadow_l3e_get_mfn(shadow_l3e[i])),
                               __PAGE_HYPERVISOR) 
                : l2e_empty();
            safe_write_entry(
                &l2e[l2_table_offset(SH_LINEAR_PT_VIRT_START) + i],
                &new_l2e);
        }
        
        if ( unmap_l2e )
            sh_unmap_domain_page(l2e);
    }

#elif CONFIG_PAGING_LEVELS == 2

    /* For PV, one l2e points at the guest l2, one points at the shadow
     * l2. No maintenance required. 
     * For HVM, just need to update the l2e that points to the shadow l2. */

    if ( shadow_mode_external(d) )
    {
        /* Use the linear map if we can; otherwise make a new mapping */
        if ( v == current ) 
        {
            __linear_l2_table[l2_linear_offset(SH_LINEAR_PT_VIRT_START)] = 
                l2e_from_pfn(pagetable_get_pfn(v->arch.shadow_table[0]),
                             __PAGE_HYPERVISOR);
        } 
        else
        { 
            l2_pgentry_t *ml2e;
            ml2e = sh_map_domain_page(pagetable_get_mfn(v->arch.monitor_table));
            ml2e[l2_table_offset(SH_LINEAR_PT_VIRT_START)] = 
                l2e_from_pfn(pagetable_get_pfn(v->arch.shadow_table[0]),
                             __PAGE_HYPERVISOR);
            sh_unmap_domain_page(ml2e);
        }
    }

#else
#error this should not happen
#endif

    if ( shadow_mode_external(d) )
    {
        /*
         * Having modified the linear pagetable mapping, flush local host TLBs.
         * This was not needed when vmenter/vmexit always had the side effect
         * of flushing host TLBs but, with ASIDs, it is possible to finish 
         * this CR3 update, vmenter the guest, vmexit due to a page fault, 
         * without an intervening host TLB flush. Then the page fault code 
         * could use the linear pagetable to read a top-level shadow page 
         * table entry. But, without this change, it would fetch the wrong 
         * value due to a stale TLB.
         */
        flush_tlb_local();
    }
}


/* Removes vcpu->arch.paging.shadow.guest_vtable and vcpu->arch.shadow_table[].
 * Does all appropriate management/bookkeeping/refcounting/etc...
 */
static void
sh_detach_old_tables(struct vcpu *v)
{
    mfn_t smfn;
    int i = 0;

    ////
    //// vcpu->arch.paging.shadow.guest_vtable
    ////

#if GUEST_PAGING_LEVELS == 3
    /* PAE guests don't have a mapping of the guest top-level table */
    ASSERT(v->arch.paging.shadow.guest_vtable == NULL);
#else
    if ( v->arch.paging.shadow.guest_vtable )
    {
        struct domain *d = v->domain;
        if ( shadow_mode_external(d) || shadow_mode_translate(d) )
            sh_unmap_domain_page_global(v->arch.paging.shadow.guest_vtable);
        v->arch.paging.shadow.guest_vtable = NULL;
    }
#endif


    ////
    //// vcpu->arch.shadow_table[]
    ////

#if GUEST_PAGING_LEVELS == 3
    /* PAE guests have four shadow_table entries */
    for ( i = 0 ; i < 4 ; i++ )
#endif
    {
        smfn = pagetable_get_mfn(v->arch.shadow_table[i]);
        if ( mfn_x(smfn) )
            sh_put_ref(v, smfn, 0);
        v->arch.shadow_table[i] = pagetable_null();
    }
}

/* Set up the top-level shadow and install it in slot 'slot' of shadow_table */
static void
sh_set_toplevel_shadow(struct vcpu *v, 
                       int slot,
                       mfn_t gmfn, 
                       unsigned int root_type) 
{
    mfn_t smfn;
    pagetable_t old_entry, new_entry;

    struct domain *d = v->domain;
    
    /* Remember the old contents of this slot */
    old_entry = v->arch.shadow_table[slot];

    /* Now figure out the new contents: is this a valid guest MFN? */
    if ( !mfn_valid(gmfn) )
    {
        new_entry = pagetable_null();
        goto install_new_entry;
    }

    /* Guest mfn is valid: shadow it and install the shadow */
    smfn = get_shadow_status(v, gmfn, root_type);
    if ( !mfn_valid(smfn) )
    {
        /* Make sure there's enough free shadow memory. */
        shadow_prealloc(d, root_type, 1);
        /* Shadow the page. */
        smfn = sh_make_shadow(v, gmfn, root_type);
    }
    ASSERT(mfn_valid(smfn));
    
    /* Pin the shadow and put it (back) on the list of pinned shadows */
    if ( sh_pin(v, smfn) == 0 )
    {
        SHADOW_ERROR("can't pin %#lx as toplevel shadow\n", mfn_x(smfn));
        domain_crash(v->domain);
    }

    /* Take a ref to this page: it will be released in sh_detach_old_tables()
     * or the next call to set_toplevel_shadow() */
    if ( !sh_get_ref(v, smfn, 0) )
    {
        SHADOW_ERROR("can't install %#lx as toplevel shadow\n", mfn_x(smfn));
        domain_crash(v->domain);
    }

    new_entry = pagetable_from_mfn(smfn);

 install_new_entry:
    /* Done.  Install it */
    SHADOW_PRINTK("%u/%u [%u] gmfn %#"PRI_mfn" smfn %#"PRI_mfn"\n",
                  GUEST_PAGING_LEVELS, SHADOW_PAGING_LEVELS, slot,
                  mfn_x(gmfn), mfn_x(pagetable_get_mfn(new_entry)));
    v->arch.shadow_table[slot] = new_entry;

    /* Decrement the refcount of the old contents of this slot */
    if ( !pagetable_is_null(old_entry) ) {
        mfn_t old_smfn = pagetable_get_mfn(old_entry);
        /* Need to repin the old toplevel shadow if it's been unpinned
         * by shadow_prealloc(): in PV mode we're still running on this
         * shadow and it's not safe to free it yet. */
        if ( !mfn_to_shadow_page(old_smfn)->pinned && !sh_pin(v, old_smfn) )
        {
            SHADOW_ERROR("can't re-pin %#lx\n", mfn_x(old_smfn));
            domain_crash(v->domain);
        }
        sh_put_ref(v, old_smfn, 0);
    }
}


static void
sh_update_cr3(struct vcpu *v, int do_locking)
/* Updates vcpu->arch.cr3 after the guest has changed CR3.
 * Paravirtual guests should set v->arch.guest_table (and guest_table_user,
 * if appropriate).
 * HVM guests should also make sure hvm_get_guest_cntl_reg(v, 3) works;
 * this function will call hvm_update_guest_cr(v, 3) to tell them where the 
 * shadow tables are.
 * If do_locking != 0, assume we are being called from outside the 
 * shadow code, and must take and release the shadow lock; otherwise 
 * that is the caller's responsibility.
 */
{
    struct domain *d = v->domain;
    mfn_t gmfn;
#if GUEST_PAGING_LEVELS == 3
    guest_l3e_t *gl3e;
    u32 guest_idx=0;
    int i;
#endif

    /* Don't do anything on an uninitialised vcpu */
    if ( !is_hvm_domain(d) && !v->is_initialised )
    {
        ASSERT(v->arch.cr3 == 0);
        return;
    }

    if ( do_locking ) shadow_lock(v->domain);

    ASSERT(shadow_locked_by_me(v->domain));
    ASSERT(v->arch.paging.mode);

    ////
    //// vcpu->arch.guest_table is already set
    ////
    
#ifndef NDEBUG 
    /* Double-check that the HVM code has sent us a sane guest_table */
    if ( is_hvm_domain(d) )
    {
        ASSERT(shadow_mode_external(d));
        if ( hvm_paging_enabled(v) )
            ASSERT(pagetable_get_pfn(v->arch.guest_table));
        else 
            ASSERT(v->arch.guest_table.pfn
                   == d->arch.paging.shadow.unpaged_pagetable.pfn);
    }
#endif

    SHADOW_PRINTK("d=%u v=%u guest_table=%05lx\n",
                   d->domain_id, v->vcpu_id, 
                   (unsigned long)pagetable_get_pfn(v->arch.guest_table));

#if GUEST_PAGING_LEVELS == 4
    if ( !(v->arch.flags & TF_kernel_mode) && !is_pv_32on64_vcpu(v) )
        gmfn = pagetable_get_mfn(v->arch.guest_table_user);
    else
#endif
        gmfn = pagetable_get_mfn(v->arch.guest_table);


    ////
    //// vcpu->arch.paging.shadow.guest_vtable
    ////
#if GUEST_PAGING_LEVELS == 4
    if ( shadow_mode_external(d) || shadow_mode_translate(d) )
    {
        if ( v->arch.paging.shadow.guest_vtable )
            sh_unmap_domain_page_global(v->arch.paging.shadow.guest_vtable);
        v->arch.paging.shadow.guest_vtable = sh_map_domain_page_global(gmfn);
        /* PAGING_LEVELS==4 implies 64-bit, which means that
         * map_domain_page_global can't fail */
        BUG_ON(v->arch.paging.shadow.guest_vtable == NULL);
    }
    else
        v->arch.paging.shadow.guest_vtable = __linear_l4_table;
#elif GUEST_PAGING_LEVELS == 3
     /* On PAE guests we don't use a mapping of the guest's own top-level
      * table.  We cache the current state of that table and shadow that,
      * until the next CR3 write makes us refresh our cache. */
     ASSERT(v->arch.paging.shadow.guest_vtable == NULL);
 
     if ( shadow_mode_external(d) ) 
         /* Find where in the page the l3 table is */
         guest_idx = guest_index((void *)v->arch.hvm_vcpu.guest_cr[3]);
     else
         /* PV guest: l3 is at the start of a page */ 
         guest_idx = 0; 

     // Ignore the low 2 bits of guest_idx -- they are really just
     // cache control.
     guest_idx &= ~3;
     
     gl3e = ((guest_l3e_t *)sh_map_domain_page(gmfn)) + guest_idx;
     for ( i = 0; i < 4 ; i++ )
         v->arch.paging.shadow.gl3e[i] = gl3e[i];
     sh_unmap_domain_page(gl3e);
#elif GUEST_PAGING_LEVELS == 2
    if ( shadow_mode_external(d) || shadow_mode_translate(d) )
    {
        if ( v->arch.paging.shadow.guest_vtable )
            sh_unmap_domain_page_global(v->arch.paging.shadow.guest_vtable);
        v->arch.paging.shadow.guest_vtable = sh_map_domain_page_global(gmfn);
        /* Does this really need map_domain_page_global?  Handle the
         * error properly if so. */
        BUG_ON(v->arch.paging.shadow.guest_vtable == NULL); /* XXX */
    }
    else
        v->arch.paging.shadow.guest_vtable = __linear_l2_table;
#else
#error this should never happen
#endif

#if 0
    printk("%s %s %d gmfn=%05lx shadow.guest_vtable=%p\n",
           __func__, __FILE__, __LINE__, gmfn, v->arch.paging.shadow.guest_vtable);
#endif

    ////
    //// vcpu->arch.shadow_table[]
    ////

    /* We revoke write access to the new guest toplevel page(s) before we
     * replace the old shadow pagetable(s), so that we can safely use the 
     * (old) shadow linear maps in the writeable mapping heuristics. */
#if GUEST_PAGING_LEVELS == 2
    if ( sh_remove_write_access(v, gmfn, 2, 0) != 0 )
        flush_tlb_mask(v->domain->domain_dirty_cpumask); 
    sh_set_toplevel_shadow(v, 0, gmfn, SH_type_l2_shadow);
#elif GUEST_PAGING_LEVELS == 3
    /* PAE guests have four shadow_table entries, based on the 
     * current values of the guest's four l3es. */
    {
        int flush = 0;
        gfn_t gl2gfn;
        mfn_t gl2mfn;
        p2m_type_t p2mt;
        guest_l3e_t *gl3e = (guest_l3e_t*)&v->arch.paging.shadow.gl3e;
        /* First, make all four entries read-only. */
        for ( i = 0; i < 4; i++ )
        {
            if ( guest_l3e_get_flags(gl3e[i]) & _PAGE_PRESENT )
            {
                gl2gfn = guest_l3e_get_gfn(gl3e[i]);
                gl2mfn = gfn_to_mfn(d, gl2gfn, &p2mt);
                if ( p2m_is_ram(p2mt) )
                    flush |= sh_remove_write_access(v, gl2mfn, 2, 0);
            }
        }
        if ( flush ) 
            flush_tlb_mask(v->domain->domain_dirty_cpumask);
        /* Now install the new shadows. */
        for ( i = 0; i < 4; i++ ) 
        {
            if ( guest_l3e_get_flags(gl3e[i]) & _PAGE_PRESENT )
            {
                gl2gfn = guest_l3e_get_gfn(gl3e[i]);
                gl2mfn = gfn_to_mfn(d, gl2gfn, &p2mt);
                if ( p2m_is_ram(p2mt) )
                    sh_set_toplevel_shadow(v, i, gl2mfn, (i == 3) 
                                           ? SH_type_l2h_shadow 
                                           : SH_type_l2_shadow);
                else
                    sh_set_toplevel_shadow(v, i, _mfn(INVALID_MFN), 0); 
            }
            else
                sh_set_toplevel_shadow(v, i, _mfn(INVALID_MFN), 0); 
        }
    }
#elif GUEST_PAGING_LEVELS == 4
    if ( sh_remove_write_access(v, gmfn, 4, 0) != 0 )
        flush_tlb_mask(v->domain->domain_dirty_cpumask);
    sh_set_toplevel_shadow(v, 0, gmfn, SH_type_l4_shadow);
#else
#error This should never happen 
#endif

#if (CONFIG_PAGING_LEVELS == 3) && (GUEST_PAGING_LEVELS == 3)
#endif

    /// 
    /// v->arch.paging.shadow.l3table
    ///
#if SHADOW_PAGING_LEVELS == 3
        {
            mfn_t smfn;
            int i;
            for ( i = 0; i < 4; i++ )
            {
#if GUEST_PAGING_LEVELS == 2
                /* 2-on-3: make a PAE l3 that points at the four-page l2 */
                smfn = _mfn(pagetable_get_pfn(v->arch.shadow_table[0]) + i);
#else
                /* 3-on-3: make a PAE l3 that points at the four l2 pages */
                smfn = pagetable_get_mfn(v->arch.shadow_table[i]);
#endif
                v->arch.paging.shadow.l3table[i] = 
                    (mfn_x(smfn) == 0) 
                    ? shadow_l3e_empty()
                    : shadow_l3e_from_mfn(smfn, _PAGE_PRESENT);
            }
        }
#endif /* SHADOW_PAGING_LEVELS == 3 */


    ///
    /// v->arch.cr3
    ///
    if ( shadow_mode_external(d) )
    {
        make_cr3(v, pagetable_get_pfn(v->arch.monitor_table));
    }
    else // not shadow_mode_external...
    {
        /* We don't support PV except guest == shadow == config levels */
        BUG_ON(GUEST_PAGING_LEVELS != SHADOW_PAGING_LEVELS);
#if SHADOW_PAGING_LEVELS == 3
        /* 2-on-3 or 3-on-3: Use the PAE shadow l3 table we just fabricated.
         * Don't use make_cr3 because (a) we know it's below 4GB, and
         * (b) it's not necessarily page-aligned, and make_cr3 takes a pfn */
        ASSERT(virt_to_maddr(&v->arch.paging.shadow.l3table) <= 0xffffffe0ULL);
        v->arch.cr3 = virt_to_maddr(&v->arch.paging.shadow.l3table);
#else
        /* 2-on-2 or 4-on-4: Just use the shadow top-level directly */
        make_cr3(v, pagetable_get_pfn(v->arch.shadow_table[0]));
#endif
    }


    ///
    /// v->arch.hvm_vcpu.hw_cr[3]
    ///
    if ( shadow_mode_external(d) )
    {
        ASSERT(is_hvm_domain(d));
#if SHADOW_PAGING_LEVELS == 3
        /* 2-on-3 or 3-on-3: Use the PAE shadow l3 table we just fabricated */
        v->arch.hvm_vcpu.hw_cr[3] =
            virt_to_maddr(&v->arch.paging.shadow.l3table);
#else
        /* 2-on-2 or 4-on-4: Just use the shadow top-level directly */
        v->arch.hvm_vcpu.hw_cr[3] =
            pagetable_get_paddr(v->arch.shadow_table[0]);
#endif
        hvm_update_guest_cr(v, 3);
    }

    /* Fix up the linear pagetable mappings */
    sh_update_linear_entries(v);

#if (SHADOW_OPTIMIZATIONS & SHOPT_VIRTUAL_TLB)
    /* No longer safe to use cached gva->gfn translations */
    vtlb_flush(v);
#endif

    /* CoW: keep track of last 'n' top-level directories */
    if (!paging_mode_log_dirty(d))
    {
        cow.gl2mfn[1] = cow.gl2mfn[0];
        cow.gl2mfn[0] = pagetable_get_mfn(v->arch.guest_table);
    }
    
    /* Release the lock, if we took it (otherwise it's the caller's problem) */
    if ( do_locking ) shadow_unlock(v->domain);
}


/**************************************************************************/
/* Functions to revoke guest rights */

#if SHADOW_OPTIMIZATIONS & SHOPT_WRITABLE_HEURISTIC
static int sh_guess_wrmap(struct vcpu *v, unsigned long vaddr, mfn_t gmfn)
/* Look up this vaddr in the current shadow and see if it's a writeable
 * mapping of this gmfn.  If so, remove it.  Returns 1 if it worked. */
{
    shadow_l1e_t sl1e, *sl1p;
    shadow_l2e_t *sl2p;
#if SHADOW_PAGING_LEVELS >= 3
    shadow_l3e_t *sl3p;
#if SHADOW_PAGING_LEVELS >= 4
    shadow_l4e_t *sl4p;
#endif
#endif
    mfn_t sl1mfn;
    int r;

    /* Carefully look in the shadow linear map for the l1e we expect */
#if SHADOW_PAGING_LEVELS >= 4
    sl4p = sh_linear_l4_table(v) + shadow_l4_linear_offset(vaddr);
    if ( !(shadow_l4e_get_flags(*sl4p) & _PAGE_PRESENT) )
        return 0;
    sl3p = sh_linear_l3_table(v) + shadow_l3_linear_offset(vaddr);
    if ( !(shadow_l3e_get_flags(*sl3p) & _PAGE_PRESENT) )
        return 0;
#elif SHADOW_PAGING_LEVELS == 3
    sl3p = ((shadow_l3e_t *) v->arch.paging.shadow.l3table) 
        + shadow_l3_linear_offset(vaddr);
    if ( !(shadow_l3e_get_flags(*sl3p) & _PAGE_PRESENT) )
        return 0;
#endif
    sl2p = sh_linear_l2_table(v) + shadow_l2_linear_offset(vaddr);
    if ( !(shadow_l2e_get_flags(*sl2p) & _PAGE_PRESENT) )
        return 0;
    sl1p = sh_linear_l1_table(v) + shadow_l1_linear_offset(vaddr);
    sl1e = *sl1p;
    if ( ((shadow_l1e_get_flags(sl1e) & (_PAGE_PRESENT|_PAGE_RW))
          != (_PAGE_PRESENT|_PAGE_RW))
         || (mfn_x(shadow_l1e_get_mfn(sl1e)) != mfn_x(gmfn)) )
        return 0;

    /* Found it!  Need to remove its write permissions. */
    sl1mfn = shadow_l2e_get_mfn(*sl2p);
    sl1e = shadow_l1e_remove_flags(sl1e, _PAGE_RW);
    r = shadow_set_l1e(v, sl1p, sl1e, sl1mfn);
    ASSERT( !(r & SHADOW_SET_ERROR) );
    return 1;
}
#endif

int sh_rm_write_access_from_l1(struct vcpu *v, mfn_t sl1mfn,
                               mfn_t readonly_mfn)
/* Excises all writeable mappings to readonly_mfn from this l1 shadow table */
{
    shadow_l1e_t *sl1e;
    int done = 0;
    int flags;
    mfn_t base_sl1mfn = sl1mfn; /* Because sl1mfn changes in the foreach */
    
    SHADOW_FOREACH_L1E(sl1mfn, sl1e, 0, done, 
    {
        flags = shadow_l1e_get_flags(*sl1e);
        if ( (flags & _PAGE_PRESENT) 
             && (flags & _PAGE_RW) 
             && (mfn_x(shadow_l1e_get_mfn(*sl1e)) == mfn_x(readonly_mfn)) )
        {
            shadow_l1e_t ro_sl1e = shadow_l1e_remove_flags(*sl1e, _PAGE_RW);
            (void) shadow_set_l1e(v, sl1e, ro_sl1e, sl1mfn);
#if SHADOW_OPTIMIZATIONS & SHOPT_WRITABLE_HEURISTIC 
            /* Remember the last shadow that we shot a writeable mapping in */
            v->arch.paging.shadow.last_writeable_pte_smfn = mfn_x(base_sl1mfn);
#endif
            if ( (mfn_to_page(readonly_mfn)->u.inuse.type_info
                  & PGT_count_mask) == 0 )
                /* This breaks us cleanly out of the FOREACH macro */
                done = 1;
        }
    });
    return done;
}


int sh_rm_mappings_from_l1(struct vcpu *v, mfn_t sl1mfn, mfn_t target_mfn)
/* Excises all mappings to guest frame from this shadow l1 table */
{
    shadow_l1e_t *sl1e;
    int done = 0;
    int flags;
    
    SHADOW_FOREACH_L1E(sl1mfn, sl1e, 0, done, 
    {
        flags = shadow_l1e_get_flags(*sl1e);
        if ( (flags & _PAGE_PRESENT) 
             && (mfn_x(shadow_l1e_get_mfn(*sl1e)) == mfn_x(target_mfn)) )
        {
            (void) shadow_set_l1e(v, sl1e, shadow_l1e_empty(), sl1mfn);
            if ( (mfn_to_page(target_mfn)->count_info & PGC_count_mask) == 0 )
                /* This breaks us cleanly out of the FOREACH macro */
                done = 1;
        }
    });
    return done;
}

/**************************************************************************/
/* Functions to excise all pointers to shadows from higher-level shadows. */

void sh_clear_shadow_entry(struct vcpu *v, void *ep, mfn_t smfn)
/* Blank out a single shadow entry */
{
    switch ( mfn_to_shadow_page(smfn)->type )
    {
    case SH_type_l1_shadow:
        (void) shadow_set_l1e(v, ep, shadow_l1e_empty(), smfn); break;
    case SH_type_l2_shadow:
#if GUEST_PAGING_LEVELS >= 3
    case SH_type_l2h_shadow:
#endif
        (void) shadow_set_l2e(v, ep, shadow_l2e_empty(), smfn); break;
#if GUEST_PAGING_LEVELS >= 4
    case SH_type_l3_shadow:
        (void) shadow_set_l3e(v, ep, shadow_l3e_empty(), smfn); break;
    case SH_type_l4_shadow:
        (void) shadow_set_l4e(v, ep, shadow_l4e_empty(), smfn); break;
#endif
    default: BUG(); /* Called with the wrong kind of shadow. */
    }
}

int sh_remove_l1_shadow(struct vcpu *v, mfn_t sl2mfn, mfn_t sl1mfn)
/* Remove all mappings of this l1 shadow from this l2 shadow */
{
    shadow_l2e_t *sl2e;
    int done = 0;
    int flags;
    
    SHADOW_FOREACH_L2E(sl2mfn, sl2e, 0, done, v->domain, 
    {
        flags = shadow_l2e_get_flags(*sl2e);
        if ( (flags & _PAGE_PRESENT) 
             && (mfn_x(shadow_l2e_get_mfn(*sl2e)) == mfn_x(sl1mfn)) )
        {
            (void) shadow_set_l2e(v, sl2e, shadow_l2e_empty(), sl2mfn);
            if ( mfn_to_shadow_page(sl1mfn)->type == 0 )
                /* This breaks us cleanly out of the FOREACH macro */
                done = 1;
        }
    });
    return done;
}

#if GUEST_PAGING_LEVELS >= 4
int sh_remove_l2_shadow(struct vcpu *v, mfn_t sl3mfn, mfn_t sl2mfn)
/* Remove all mappings of this l2 shadow from this l3 shadow */
{
    shadow_l3e_t *sl3e;
    int done = 0;
    int flags;
    
    SHADOW_FOREACH_L3E(sl3mfn, sl3e, 0, done, 
    {
        flags = shadow_l3e_get_flags(*sl3e);
        if ( (flags & _PAGE_PRESENT) 
             && (mfn_x(shadow_l3e_get_mfn(*sl3e)) == mfn_x(sl2mfn)) )
        {
            (void) shadow_set_l3e(v, sl3e, shadow_l3e_empty(), sl3mfn);
            if ( mfn_to_shadow_page(sl2mfn)->type == 0 )
                /* This breaks us cleanly out of the FOREACH macro */
                done = 1;
        }
    });
    return done;
}

int sh_remove_l3_shadow(struct vcpu *v, mfn_t sl4mfn, mfn_t sl3mfn)
/* Remove all mappings of this l3 shadow from this l4 shadow */
{
    shadow_l4e_t *sl4e;
    int done = 0;
    int flags;
    
    SHADOW_FOREACH_L4E(sl4mfn, sl4e, 0, done, v->domain,
    {
        flags = shadow_l4e_get_flags(*sl4e);
        if ( (flags & _PAGE_PRESENT) 
             && (mfn_x(shadow_l4e_get_mfn(*sl4e)) == mfn_x(sl3mfn)) )
        {
            (void) shadow_set_l4e(v, sl4e, shadow_l4e_empty(), sl4mfn);
            if ( mfn_to_shadow_page(sl3mfn)->type == 0 )
                /* This breaks us cleanly out of the FOREACH macro */
                done = 1;
        }
    });
    return done;
}
#endif /* 64bit guest */ 

/**************************************************************************/
/* Handling HVM guest writes to pagetables  */

/* Translate a VA to an MFN, injecting a page-fault if we fail */
#define BAD_GVA_TO_GFN (~0UL)
#define BAD_GFN_TO_MFN (~1UL)
static mfn_t emulate_gva_to_mfn(struct vcpu *v,
                                unsigned long vaddr,
                                struct sh_emulate_ctxt *sh_ctxt)
{
    unsigned long gfn;
    mfn_t mfn;
    p2m_type_t p2mt;
    uint32_t pfec = PFEC_page_present | PFEC_write_access;

    /* Translate the VA to a GFN */
    gfn = sh_gva_to_gfn(v, vaddr, &pfec);
    if ( gfn == INVALID_GFN ) 
    {
        if ( is_hvm_vcpu(v) )
            hvm_inject_exception(TRAP_page_fault, pfec, vaddr);
        else
            propagate_page_fault(vaddr, pfec);
        return _mfn(BAD_GVA_TO_GFN);
    }

    /* Translate the GFN to an MFN */
    mfn = gfn_to_mfn(v->domain, _gfn(gfn), &p2mt);
    if ( p2m_is_ram(p2mt) )
    {
        ASSERT(mfn_valid(mfn));
        v->arch.paging.last_write_was_pt = !!sh_mfn_is_a_page_table(mfn);
        return mfn;
    }
 
    return _mfn(BAD_GFN_TO_MFN);
}

/* Check that the user is allowed to perform this write. 
 * Returns a mapped pointer to write to, or NULL for error. */
#define MAPPING_UNHANDLEABLE ((void *)0)
#define MAPPING_EXCEPTION    ((void *)1)
#define emulate_map_dest_failed(rc) ((unsigned long)(rc) <= 1)
static void *emulate_map_dest(struct vcpu *v,
                              unsigned long vaddr,
                              u32 bytes,
                              struct sh_emulate_ctxt *sh_ctxt)
{
    struct segment_register *sreg;
    unsigned long offset;
    void *map = NULL;

    /* We don't emulate user-mode writes to page tables */
    sreg = hvm_get_seg_reg(x86_seg_ss, sh_ctxt);
    if ( sreg->attr.fields.dpl == 3 )
        return MAPPING_UNHANDLEABLE;

    sh_ctxt->mfn1 = emulate_gva_to_mfn(v, vaddr, sh_ctxt);
    if ( !mfn_valid(sh_ctxt->mfn1) ) 
        return ((mfn_x(sh_ctxt->mfn1) == BAD_GVA_TO_GFN) ?
                MAPPING_EXCEPTION : MAPPING_UNHANDLEABLE);

    /* Unaligned writes mean probably this isn't a pagetable */
    if ( vaddr & (bytes - 1) )
        sh_remove_shadows(v, sh_ctxt->mfn1, 0, 0 /* Slow, can fail */ );

    if ( likely(((vaddr + bytes - 1) & PAGE_MASK) == (vaddr & PAGE_MASK)) )
    {
        /* Whole write fits on a single page */
        sh_ctxt->mfn2 = _mfn(INVALID_MFN);
        map = sh_map_domain_page(sh_ctxt->mfn1) + (vaddr & ~PAGE_MASK);
    }
    else 
    {
        /* Cross-page emulated writes are only supported for HVM guests; 
         * PV guests ought to know better */
        if ( !is_hvm_vcpu(v) )
            return MAPPING_UNHANDLEABLE;

        /* This write crosses a page boundary.  Translate the second page */
        sh_ctxt->mfn2 = emulate_gva_to_mfn(v, (vaddr + bytes - 1) & PAGE_MASK,
                                           sh_ctxt);
        if ( !mfn_valid(sh_ctxt->mfn2) ) 
            return ((mfn_x(sh_ctxt->mfn2) == BAD_GVA_TO_GFN) ?
                    MAPPING_EXCEPTION : MAPPING_UNHANDLEABLE);

        /* Cross-page writes mean probably not a pagetable */
        sh_remove_shadows(v, sh_ctxt->mfn2, 0, 0 /* Slow, can fail */ );
        
        /* Hack: we map the pages into the vcpu's LDT space, since we
         * know that we're not going to need the LDT for HVM guests, 
         * and only HVM guests are allowed unaligned writes. */
        ASSERT(is_hvm_vcpu(v));
        map = (void *)LDT_VIRT_START(v);
        offset = l1_linear_offset((unsigned long) map);
        l1e_write(&__linear_l1_table[offset],
                  l1e_from_pfn(mfn_x(sh_ctxt->mfn1), __PAGE_HYPERVISOR));
        l1e_write(&__linear_l1_table[offset + 1],
                  l1e_from_pfn(mfn_x(sh_ctxt->mfn2), __PAGE_HYPERVISOR));
        flush_tlb_local();
        map += (vaddr & ~PAGE_MASK);
    }

#if (SHADOW_OPTIMIZATIONS & SHOPT_SKIP_VERIFY)
    /* Remember if the bottom bit was clear, so we can choose not to run
     * the change through the verify code if it's still clear afterwards */
    sh_ctxt->low_bit_was_clear = map != NULL && !(*(u8 *)map & _PAGE_PRESENT);
#endif

    return map;
}

/* Tidy up after the emulated write: mark pages dirty, verify the new
 * contents, and undo the mapping */
static void emulate_unmap_dest(struct vcpu *v,
                               void *addr,
                               u32 bytes,
                               struct sh_emulate_ctxt *sh_ctxt)
{
    u32 b1 = bytes, b2 = 0, shflags;

    ASSERT(mfn_valid(sh_ctxt->mfn1));

    /* If we are writing lots of PTE-aligned zeros, might want to unshadow */
    if ( likely(bytes >= 4)
         && (*(u32 *)addr == 0)
         && ((unsigned long) addr & ((sizeof (guest_intpte_t)) - 1)) == 0 )
        check_for_early_unshadow(v, sh_ctxt->mfn1);
    else
        reset_early_unshadow(v);

    /* We can avoid re-verifying the page contents after the write if:
     *  - it was no larger than the PTE type of this pagetable;
     *  - it was aligned to the PTE boundaries; and
     *  - _PAGE_PRESENT was clear before and after the write. */
    shflags = mfn_to_page(sh_ctxt->mfn1)->shadow_flags;
#if (SHADOW_OPTIMIZATIONS & SHOPT_SKIP_VERIFY)
    if ( sh_ctxt->low_bit_was_clear
         && !(*(u8 *)addr & _PAGE_PRESENT)
         && ((!(shflags & SHF_32)
              /* Not shadowed 32-bit: aligned 64-bit writes that leave
               * the present bit unset are safe to ignore. */
              && ((unsigned long)addr & 7) == 0
              && bytes <= 8)
             ||
             (!(shflags & (SHF_PAE|SHF_64))
              /* Not shadowed PAE/64-bit: aligned 32-bit writes that
               * leave the present bit unset are safe to ignore. */
              && ((unsigned long)addr & 3) == 0
              && bytes <= 4)) )
    {
        /* Writes with this alignment constraint can't possibly cross pages */
        ASSERT(!mfn_valid(sh_ctxt->mfn2)); 
    }
    else 
#endif /* SHADOW_OPTIMIZATIONS & SHOPT_SKIP_VERIFY */
    {        
        if ( unlikely(mfn_valid(sh_ctxt->mfn2)) )
        {
            /* Validate as two writes, one to each page */
            b1 = PAGE_SIZE - (((unsigned long)addr) & ~PAGE_MASK);
            b2 = bytes - b1;
            ASSERT(b2 < bytes);
        }
        if ( likely(b1 > 0) )
            sh_validate_guest_pt_write(v, sh_ctxt->mfn1, addr, b1);
        if ( unlikely(b2 > 0) )
            sh_validate_guest_pt_write(v, sh_ctxt->mfn2, addr + b1, b2);
    }

    paging_mark_dirty(v->domain, mfn_x(sh_ctxt->mfn1));

    if ( unlikely(mfn_valid(sh_ctxt->mfn2)) )
    {
        unsigned long offset;
        paging_mark_dirty(v->domain, mfn_x(sh_ctxt->mfn2));
        /* Undo the hacky two-frame contiguous map. */
        ASSERT(((unsigned long) addr & PAGE_MASK) == LDT_VIRT_START(v));
        offset = l1_linear_offset((unsigned long) addr);
        l1e_write(&__linear_l1_table[offset], l1e_empty());
        l1e_write(&__linear_l1_table[offset + 1], l1e_empty());
        flush_tlb_all();
    }
    else 
        sh_unmap_domain_page(addr);
}

int
sh_x86_emulate_write(struct vcpu *v, unsigned long vaddr, void *src,
                      u32 bytes, struct sh_emulate_ctxt *sh_ctxt)
{
    void *addr;

    /* Unaligned writes are only acceptable on HVM */
    if ( (vaddr & (bytes - 1)) && !is_hvm_vcpu(v)  )
        return X86EMUL_UNHANDLEABLE;

    shadow_lock(v->domain);
    addr = emulate_map_dest(v, vaddr, bytes, sh_ctxt);
    if ( emulate_map_dest_failed(addr) )
    {
        shadow_unlock(v->domain);
        return ((addr == MAPPING_EXCEPTION) ?
                X86EMUL_EXCEPTION : X86EMUL_UNHANDLEABLE);
    }

    /* Do CoW before write occurs */
    cow_copy_page(v->domain, sh_ctxt->mfn1);
    cow_copy_page(v->domain, sh_ctxt->mfn2);

    memcpy(addr, src, bytes);

    emulate_unmap_dest(v, addr, bytes, sh_ctxt);
    shadow_audit_tables(v);
    shadow_unlock(v->domain);
    return X86EMUL_OKAY;
}

int
sh_x86_emulate_cmpxchg(struct vcpu *v, unsigned long vaddr, 
                        unsigned long old, unsigned long new,
                        unsigned int bytes, struct sh_emulate_ctxt *sh_ctxt)
{
    void *addr;
    unsigned long prev;
    int rv = X86EMUL_OKAY;

    /* Unaligned writes are only acceptable on HVM */
    if ( (vaddr & (bytes - 1)) && !is_hvm_vcpu(v)  )
        return X86EMUL_UNHANDLEABLE;

    shadow_lock(v->domain);

    addr = emulate_map_dest(v, vaddr, bytes, sh_ctxt);
    if ( emulate_map_dest_failed(addr) )
    {
        shadow_unlock(v->domain);
        return ((addr == MAPPING_EXCEPTION) ?
                X86EMUL_EXCEPTION : X86EMUL_UNHANDLEABLE);
    }

    /* Do CoW before write occurs */
    cow_copy_page(v->domain, sh_ctxt->mfn1);
    cow_copy_page(v->domain, sh_ctxt->mfn2);

    switch ( bytes )
    {
    case 1: prev = cmpxchg(((u8 *)addr), old, new);  break;
    case 2: prev = cmpxchg(((u16 *)addr), old, new); break;
    case 4: prev = cmpxchg(((u32 *)addr), old, new); break;
    case 8: prev = cmpxchg(((u64 *)addr), old, new); break;
    default:
        SHADOW_PRINTK("cmpxchg of size %i is not supported\n", bytes);
        prev = ~old;
    }

    if ( prev != old ) 
        rv = X86EMUL_CMPXCHG_FAILED;

    SHADOW_DEBUG(EMULATE, "va %#lx was %#lx expected %#lx"
                  " wanted %#lx now %#lx bytes %u\n",
                  vaddr, prev, old, new, *(unsigned long *)addr, bytes);

    emulate_unmap_dest(v, addr, bytes, sh_ctxt);
    shadow_audit_tables(v);
    shadow_unlock(v->domain);
    return rv;
}

int
sh_x86_emulate_cmpxchg8b(struct vcpu *v, unsigned long vaddr, 
                          unsigned long old_lo, unsigned long old_hi,
                          unsigned long new_lo, unsigned long new_hi,
                          struct sh_emulate_ctxt *sh_ctxt)
{
    void *addr;
    u64 old, new, prev;
    int rv = X86EMUL_OKAY;

    /* Unaligned writes are only acceptable on HVM */
    if ( (vaddr & 7) && !is_hvm_vcpu(v) )
        return X86EMUL_UNHANDLEABLE;

    shadow_lock(v->domain);

    addr = emulate_map_dest(v, vaddr, 8, sh_ctxt);
    if ( emulate_map_dest_failed(addr) )
    {
        shadow_unlock(v->domain);
        return ((addr == MAPPING_EXCEPTION) ?
                X86EMUL_EXCEPTION : X86EMUL_UNHANDLEABLE);
    }

    /* Do CoW before write occurs */
    cow_copy_page(v->domain, sh_ctxt->mfn1);
    cow_copy_page(v->domain, sh_ctxt->mfn2);

    old = (((u64) old_hi) << 32) | (u64) old_lo;
    new = (((u64) new_hi) << 32) | (u64) new_lo;
    prev = cmpxchg(((u64 *)addr), old, new);

    if ( prev != old )
        rv = X86EMUL_CMPXCHG_FAILED;

    emulate_unmap_dest(v, addr, 8, sh_ctxt);
    shadow_audit_tables(v);
    shadow_unlock(v->domain);
    return rv;
}


/**************************************************************************/
/* Audit tools */

#if SHADOW_AUDIT & SHADOW_AUDIT_ENTRIES

#define AUDIT_FAIL(_level, _fmt, _a...) do {                               \
    printk("Shadow %u-on-%u audit failed at level %i, index %i\n"         \
           "gl" #_level "mfn = %" PRI_mfn                              \
           " sl" #_level "mfn = %" PRI_mfn                             \
           " &gl" #_level "e = %p &sl" #_level "e = %p"                    \
           " gl" #_level "e = %" SH_PRI_gpte                              \
           " sl" #_level "e = %" SH_PRI_pte "\nError: " _fmt "\n",        \
           GUEST_PAGING_LEVELS, SHADOW_PAGING_LEVELS,                      \
           _level, guest_index(gl ## _level ## e),                         \
           mfn_x(gl ## _level ## mfn), mfn_x(sl ## _level ## mfn),         \
           gl ## _level ## e, sl ## _level ## e,                           \
           gl ## _level ## e->l ## _level, sl ## _level ## e->l ## _level, \
           ##_a);                                                          \
    BUG();                                                                 \
    done = 1;                                                              \
} while (0)


static char * sh_audit_flags(struct vcpu *v, int level,
                              int gflags, int sflags) 
/* Common code for auditing flag bits */
{
    if ( (sflags & _PAGE_PRESENT) && !(gflags & _PAGE_PRESENT) )
        return "shadow is present but guest is not present";
    if ( (sflags & _PAGE_GLOBAL) && !is_hvm_vcpu(v) ) 
        return "global bit set in PV shadow";
    if ( level == 2 && (sflags & _PAGE_PSE) )
        return "PS bit set in shadow";
#if SHADOW_PAGING_LEVELS == 3
    if ( level == 3 ) return NULL; /* All the other bits are blank in PAEl3 */
#endif
    if ( (sflags & _PAGE_PRESENT) && !(gflags & _PAGE_ACCESSED) ) 
        return "accessed bit not propagated";
    if ( (level == 1 || (level == 2 && (gflags & _PAGE_PSE)))
         && ((sflags & _PAGE_RW) && !(gflags & _PAGE_DIRTY)) ) 
        return "dirty bit not propagated";
    if ( (sflags & _PAGE_USER) != (gflags & _PAGE_USER) ) 
        return "user/supervisor bit does not match";
    if ( (sflags & _PAGE_NX_BIT) != (gflags & _PAGE_NX_BIT) ) 
        return "NX bit does not match";
    if ( (sflags & _PAGE_RW) && !(gflags & _PAGE_RW) ) 
        return "shadow grants write access but guest does not";
    return NULL;
}

static inline mfn_t
audit_gfn_to_mfn(struct vcpu *v, gfn_t gfn, mfn_t gmfn)
/* Convert this gfn to an mfn in the manner appropriate for the
 * guest pagetable it's used in (gmfn) */ 
{
    p2m_type_t p2mt;
    if ( !shadow_mode_translate(v->domain) )
        return _mfn(gfn_x(gfn));
    
    if ( (mfn_to_page(gmfn)->u.inuse.type_info & PGT_type_mask)
         != PGT_writable_page ) 
        return _mfn(gfn_x(gfn)); /* This is a paging-disabled shadow */
    else 
        return gfn_to_mfn(v->domain, gfn, &p2mt);
} 


int sh_audit_l1_table(struct vcpu *v, mfn_t sl1mfn, mfn_t x)
{
    guest_l1e_t *gl1e, *gp;
    shadow_l1e_t *sl1e;
    mfn_t mfn, gmfn, gl1mfn;
    gfn_t gfn;
    char *s;
    int done = 0;
    
    /* Follow the backpointer */
    gl1mfn = _mfn(mfn_to_shadow_page(sl1mfn)->backpointer);
    gl1e = gp = sh_map_domain_page(gl1mfn);
    SHADOW_FOREACH_L1E(sl1mfn, sl1e, &gl1e, done, {

        if ( sh_l1e_is_magic(*sl1e) ) 
        {
#if (SHADOW_OPTIMIZATIONS & SHOPT_FAST_FAULT_PATH) && SHADOW_PAGING_LEVELS > 2
            if ( sh_l1e_is_gnp(*sl1e) )
            {
                if ( guest_l1e_get_flags(*gl1e) & _PAGE_PRESENT )
                    AUDIT_FAIL(1, "shadow is GNP magic but guest is present");
            } 
            else 
            {
                ASSERT(sh_l1e_is_mmio(*sl1e));
                gfn = sh_l1e_mmio_get_gfn(*sl1e);
                if ( gfn_x(gfn) != gfn_x(guest_l1e_get_gfn(*gl1e)) )
                    AUDIT_FAIL(1, "shadow MMIO gfn is %" SH_PRI_gfn 
                               " but guest gfn is %" SH_PRI_gfn,
                               gfn_x(gfn),
                               gfn_x(guest_l1e_get_gfn(*gl1e)));
            }
#endif
        }
        else 
        {
            s = sh_audit_flags(v, 1, guest_l1e_get_flags(*gl1e),
                               shadow_l1e_get_flags(*sl1e));
            if ( s ) AUDIT_FAIL(1, "%s", s);
            
            if ( SHADOW_AUDIT & SHADOW_AUDIT_ENTRIES_MFNS )
            {
                gfn = guest_l1e_get_gfn(*gl1e);
                mfn = shadow_l1e_get_mfn(*sl1e);
                gmfn = audit_gfn_to_mfn(v, gfn, gl1mfn);
                if ( mfn_x(gmfn) != mfn_x(mfn) )
                    AUDIT_FAIL(1, "bad translation: gfn %" SH_PRI_gfn
                               " --> %" PRI_mfn " != mfn %" PRI_mfn,
                               gfn_x(gfn), mfn_x(gmfn), mfn_x(mfn));
            }
        }
    });
    sh_unmap_domain_page(gp);
    return done;
}

int sh_audit_fl1_table(struct vcpu *v, mfn_t sl1mfn, mfn_t x)
{
    guest_l1e_t *gl1e, e;
    shadow_l1e_t *sl1e;
    mfn_t gl1mfn = _mfn(INVALID_MFN);
    int f;
    int done = 0;

    /* fl1 has no useful backpointer: all we can check are flags */
    e = guest_l1e_from_gfn(_gfn(0), 0); gl1e = &e; /* Needed for macro */
    SHADOW_FOREACH_L1E(sl1mfn, sl1e, 0, done, {
        f = shadow_l1e_get_flags(*sl1e);
        f &= ~(_PAGE_AVAIL0|_PAGE_AVAIL1|_PAGE_AVAIL2);
        if ( !(f == 0 
               || f == (_PAGE_PRESENT|_PAGE_USER|_PAGE_RW|
                        _PAGE_ACCESSED|_PAGE_DIRTY) 
               || f == (_PAGE_PRESENT|_PAGE_USER|_PAGE_ACCESSED|_PAGE_DIRTY)
               || sh_l1e_is_magic(*sl1e)) )
            AUDIT_FAIL(1, "fl1e has bad flags");
    });
    return 0;
}

int sh_audit_l2_table(struct vcpu *v, mfn_t sl2mfn, mfn_t x)
{
    guest_l2e_t *gl2e, *gp;
    shadow_l2e_t *sl2e;
    mfn_t mfn, gmfn, gl2mfn;
    gfn_t gfn;
    char *s;
    int done = 0;

    /* Follow the backpointer */
    gl2mfn = _mfn(mfn_to_shadow_page(sl2mfn)->backpointer);
    gl2e = gp = sh_map_domain_page(gl2mfn);
    SHADOW_FOREACH_L2E(sl2mfn, sl2e, &gl2e, done, v->domain, {

        s = sh_audit_flags(v, 2, guest_l2e_get_flags(*gl2e),
                            shadow_l2e_get_flags(*sl2e));
        if ( s ) AUDIT_FAIL(2, "%s", s);

        if ( SHADOW_AUDIT & SHADOW_AUDIT_ENTRIES_MFNS )
        {
            gfn = guest_l2e_get_gfn(*gl2e);
            mfn = shadow_l2e_get_mfn(*sl2e);
            gmfn = (guest_l2e_get_flags(*gl2e) & _PAGE_PSE)  
                ? get_fl1_shadow_status(v, gfn)
                : get_shadow_status(v, audit_gfn_to_mfn(v, gfn, gl2mfn), 
                                    SH_type_l1_shadow);
            if ( mfn_x(gmfn) != mfn_x(mfn) )
                AUDIT_FAIL(2, "bad translation: gfn %" SH_PRI_gfn
                           " (--> %" PRI_mfn ")"
                           " --> %" PRI_mfn " != mfn %" PRI_mfn,
                           gfn_x(gfn), 
                           (guest_l2e_get_flags(*gl2e) & _PAGE_PSE) ? 0
                           : mfn_x(audit_gfn_to_mfn(v, gfn, gl2mfn)),
                           mfn_x(gmfn), mfn_x(mfn));
        }
    });
    sh_unmap_domain_page(gp);
    return 0;
}

#if GUEST_PAGING_LEVELS >= 4
int sh_audit_l3_table(struct vcpu *v, mfn_t sl3mfn, mfn_t x)
{
    guest_l3e_t *gl3e, *gp;
    shadow_l3e_t *sl3e;
    mfn_t mfn, gmfn, gl3mfn;
    gfn_t gfn;
    char *s;
    int done = 0;

    /* Follow the backpointer */
    gl3mfn = _mfn(mfn_to_shadow_page(sl3mfn)->backpointer);
    gl3e = gp = sh_map_domain_page(gl3mfn);
    SHADOW_FOREACH_L3E(sl3mfn, sl3e, &gl3e, done, {

        s = sh_audit_flags(v, 3, guest_l3e_get_flags(*gl3e),
                            shadow_l3e_get_flags(*sl3e));
        if ( s ) AUDIT_FAIL(3, "%s", s);

        if ( SHADOW_AUDIT & SHADOW_AUDIT_ENTRIES_MFNS )
        {
            gfn = guest_l3e_get_gfn(*gl3e);
            mfn = shadow_l3e_get_mfn(*sl3e);
            gmfn = get_shadow_status(v, audit_gfn_to_mfn(v, gfn, gl3mfn), 
                                     ((GUEST_PAGING_LEVELS == 3 ||
                                       is_pv_32on64_vcpu(v))
                                      && !shadow_mode_external(v->domain)
                                      && (guest_index(gl3e) % 4) == 3)
                                     ? SH_type_l2h_shadow
                                     : SH_type_l2_shadow);
            if ( mfn_x(gmfn) != mfn_x(mfn) )
                AUDIT_FAIL(3, "bad translation: gfn %" SH_PRI_gfn
                           " --> %" PRI_mfn " != mfn %" PRI_mfn,
                           gfn_x(gfn), mfn_x(gmfn), mfn_x(mfn));
        }
    });
    sh_unmap_domain_page(gp);
    return 0;
}

int sh_audit_l4_table(struct vcpu *v, mfn_t sl4mfn, mfn_t x)
{
    guest_l4e_t *gl4e, *gp;
    shadow_l4e_t *sl4e;
    mfn_t mfn, gmfn, gl4mfn;
    gfn_t gfn;
    char *s;
    int done = 0;

    /* Follow the backpointer */
    gl4mfn = _mfn(mfn_to_shadow_page(sl4mfn)->backpointer);
    gl4e = gp = sh_map_domain_page(gl4mfn);
    SHADOW_FOREACH_L4E(sl4mfn, sl4e, &gl4e, done, v->domain,
    {
        s = sh_audit_flags(v, 4, guest_l4e_get_flags(*gl4e),
                            shadow_l4e_get_flags(*sl4e));
        if ( s ) AUDIT_FAIL(4, "%s", s);

        if ( SHADOW_AUDIT & SHADOW_AUDIT_ENTRIES_MFNS )
        {
            gfn = guest_l4e_get_gfn(*gl4e);
            mfn = shadow_l4e_get_mfn(*sl4e);
            gmfn = get_shadow_status(v, audit_gfn_to_mfn(v, gfn, gl4mfn), 
                                     SH_type_l3_shadow);
            if ( mfn_x(gmfn) != mfn_x(mfn) )
                AUDIT_FAIL(4, "bad translation: gfn %" SH_PRI_gfn
                           " --> %" PRI_mfn " != mfn %" PRI_mfn,
                           gfn_x(gfn), mfn_x(gmfn), mfn_x(mfn));
        }
    });
    sh_unmap_domain_page(gp);
    return 0;
}
#endif /* GUEST_PAGING_LEVELS >= 4 */


#undef AUDIT_FAIL

#endif /* Audit code */

/**************************************************************************/
/* Entry points into this mode of the shadow code.
 * This will all be mangled by the preprocessor to uniquify everything. */
struct paging_mode sh_paging_mode = {
    .page_fault                    = sh_page_fault, 
    .invlpg                        = sh_invlpg,
    .gva_to_gfn                    = sh_gva_to_gfn,
    .update_cr3                    = sh_update_cr3,
    .update_paging_modes           = shadow_update_paging_modes,
    .write_p2m_entry               = shadow_write_p2m_entry,
    .write_guest_entry             = shadow_write_guest_entry,
    .cmpxchg_guest_entry           = shadow_cmpxchg_guest_entry,
    .guest_map_l1e                 = sh_guest_map_l1e,
    .guest_get_eff_l1e             = sh_guest_get_eff_l1e,
    .guest_levels                  = GUEST_PAGING_LEVELS,
    .shadow.detach_old_tables      = sh_detach_old_tables,
    .shadow.x86_emulate_write      = sh_x86_emulate_write,
    .shadow.x86_emulate_cmpxchg    = sh_x86_emulate_cmpxchg,
    .shadow.x86_emulate_cmpxchg8b  = sh_x86_emulate_cmpxchg8b,
    .shadow.make_monitor_table     = sh_make_monitor_table,
    .shadow.destroy_monitor_table  = sh_destroy_monitor_table,
#if SHADOW_OPTIMIZATIONS & SHOPT_WRITABLE_HEURISTIC
    .shadow.guess_wrmap            = sh_guess_wrmap,
#endif
    .shadow.shadow_levels          = SHADOW_PAGING_LEVELS,
};

/* synchronize shadow l1pte from corresponding guest l1pte */
void cow_update_shadows(struct vcpu *v, mfn_t gl2mfn)
{
    guest_l1e_t *gl1e, *gp;
    shadow_l2e_t *sl2e;
    shadow_l1e_t *sl1e;
    int do_locking, done_l2 = 0, done_l1 = 0;
    int flags_l2, flags_l1;
    mfn_t sl2mfn = _mfn(INVALID_MFN);
    mfn_t gl1mfn = _mfn(INVALID_MFN);
    mfn_t sl1mfn = _mfn(INVALID_MFN);
    mfn_t mfn;
    unsigned long pfn;

    if (gl2mfn == INVALID_MFN)
        return;

    do_locking = !shadow_locked_by_me(v->domain);
    if (do_locking)
    {
        shadow_lock(v->domain);
        if (unlikely(!paging_mode_log_dirty(v->domain)))
        {
            shadow_unlock(v->domain);
            return;
        }
    }

    sl2mfn = get_shadow_status(v, gl2mfn, SH_type_l2_shadow);
    
    if (sl2mfn == INVALID_MFN)
        goto out;

    if (mfn_to_shadow_page(sl2mfn)->type != SH_type_l2_shadow)
        goto out;

    SHADOW_FOREACH_L2E(sl2mfn, sl2e, 0, done_l2, v->domain,
    {
        flags_l2 = shadow_l2e_get_flags(*sl2e);
        sl1mfn = shadow_l2e_get_mfn(*sl2e);
        if ((flags_l2 & _PAGE_PRESENT) &&
            (mfn_to_shadow_page(sl1mfn)->type == SH_type_l1_shadow))
        {
            gl1mfn = _mfn(mfn_to_shadow_page(sl1mfn)->backpointer);
            gl1e = gp = sh_map_domain_page(gl1mfn);
            
            SHADOW_FOREACH_L1E(sl1mfn, sl1e, &gl1e, done_l1,
            {
                flags_l1 = shadow_l1e_get_flags(*sl1e);
                if ((flags_l1 & _PAGE_PRESENT) && !(flags_l1 & _PAGE_RW))
                {
                    struct page_info *page;
                    mfn = shadow_l1e_get_mfn(*sl1e);
                    page = mfn_to_page(mfn);
                    pfn = mfn_to_gfn(v->domain, mfn);

                    log_dirty_lock(v->domain);
                    if (mfn_valid(mfn) && 
                        VALID_M2P(pfn) &&
                        sh_mfn_is_dirty(v->domain, mfn) &&
                        !sh_mfn_is_a_page_table(mfn) &&
                        ((page->u.inuse.type_info & PGT_type_mask) 
                            == PGT_writable_page) &&
                        ((page->u.inuse.type_info & PGT_count_mask) == 0))
                    {
                         if (guest_l1e_get_flags(*gl1e) & _PAGE_RW)
                         {
                             int flags = 
                                 __validate_gl1e(v, gl1e, sl1mfn, sl1e, 1);
                             if (flags & SHADOW_SET_CHANGED)
                                cow.made_rw_count++;
                         }
                    }
                    log_dirty_unlock(v->domain);
                }
            });
            sh_unmap_domain_page(gp);
        }
    });
 
    /* flush it all down the drain */
    vtlb_flush(v);
    flush_tlb_all();

out:
    if (do_locking) 
        shadow_unlock(v->domain);
}

/* walk through given address space and mark hot pfns */
void cow_determine_hot(struct vcpu *v, mfn_t gl2mfn)
{
    shadow_l2e_t *sl2e;
    shadow_l1e_t *sl1e;
    int do_locking, done_l2 = 0, done_l1 = 0;
    int flags_l2, flags_l1;
    mfn_t sl1mfn = _mfn(INVALID_MFN);
    mfn_t mfn, sl2mfn;
    unsigned long pfn;

    if (gl2mfn == INVALID_MFN)
        return;

    do_locking = !shadow_locked_by_me(v->domain);
    if (do_locking)
        shadow_lock(v->domain);

    sl2mfn = get_shadow_status(v,
                               gl2mfn,
                               SH_type_l2_shadow);
    if (sl2mfn == INVALID_MFN)
        goto out;

    if (mfn_to_shadow_page(sl2mfn)->type != SH_type_l2_shadow)
        goto out;

    SHADOW_FOREACH_L2E(sl2mfn, sl2e, 0, done_l2, v->domain,
    {
        flags_l2 = shadow_l2e_get_flags(*sl2e);
        sl1mfn = shadow_l2e_get_mfn(*sl2e);
        if (flags_l2 & _PAGE_PRESENT &&
            (mfn_to_shadow_page(sl1mfn)->type == SH_type_l1_shadow))
        {
            SHADOW_FOREACH_L1E(sl1mfn, sl1e, 0, done_l1,
            {
                flags_l1 = shadow_l1e_get_flags(*sl1e);
                if ((flags_l1 & _PAGE_PRESENT) && 
                    (flags_l1 & _PAGE_DIRTY) &&
                    (flags_l1 & _PAGE_RW))
                {
                    mfn = shadow_l1e_get_mfn(*sl1e);
                    if (mfn_valid(mfn) && !sh_mfn_is_a_page_table(mfn))
                    {
                        pfn = mfn_to_gfn(v->domain, mfn);
                        if (VALID_M2P(pfn) && 
                            (gmfn_to_mfn(v->domain, pfn) == mfn))
                        {
                            /* Don't need to check log_dirty_bitmap since */
                            /* we haven't turned on log dirty mode yet */
                            cow.hot_count++;
                            cow_set_bit(pfn, cow.hot_bitmap);
                        }
                    }
                }
            });
        }
    });

out:
    if (do_locking)
        shadow_unlock(v->domain);
}

#ifdef COW_INVERSE_MAP
/* add write access to shadow L1 PTEs mapping for the given mfn */
/* using inverted mappings.  doesn't work right now. */
void cow_add_writeable_mappings(struct vcpu *v, mfn_t mfn)
{
    struct invert_sh_entry *entry;
    struct shadow_page_info *cur;
    int do_locking;

    do_locking = !shadow_locked_by_me(v->domain);
    if (do_locking)
    {
        shadow_lock(v->domain);
        if (unlikely(!paging_mode_log_dirty(v->domain)))
        {
            shadow_unlock(v->domain);
            return;
        }
    }
    
    entry = invert_sh_table_lookup(mfn);
    
    cur = entry->sl1_list;
    while (cur != NULL)
    {
        shadow_l1e_t *sl1e;
        int done = 0, flags;
        mfn_t sl1_mfn = shadow_page_to_mfn(cur);
        unsigned long pfn;
        
        SHADOW_FOREACH_L1E(sl1_mfn, sl1e, 0, done,
        {
            flags = shadow_l1e_get_flags(*sl1e);
            if ((flags & _PAGE_PRESENT) && (flags & _PAGE_RW) && 
                (shadow_l1e_get_mfn(*sl1e) == mfn))
            {
                if (mfn_valid(mfn))
                {
                    struct page_info *page = mfn_to_page(mfn);
                    if (((page->u.inuse.type_info & PGT_type_mask) ==
                            PGT_writable_page)
                        && ((page->u.inuse.type_info & PGT_count_mask) == 0))
                    {
                        pfn = mfn_to_gfn(v->domain, mfn);
                        if (VALID_M2P(pfn) && 
                           (gmfn_to_mfn(v->domain, pfn) == mfn))
                        {
                            log_dirty_lock(v->domain);
                            if (sh_mfn_is_dirty(v->domain, mfn)) 
                            {
                                shadow_l1e_t rw_sl1e;
                                rw_sl1e = shadow_l1e_add_flags(*sl1e, _PAGE_RW);
                                __shadow_set_l1e(v, sl1e, rw_sl1e, sl1_mfn, 1);
                                cow.made_rw_count++;
                            }
                            log_dirty_unlock(v->domain);
                        }
                    }
                }
            }
        });
        cur = cur->next_entry;
    }
    flush_tlb_all();
    vtlb_flush();

    if (do_locking) 
        shadow_unlock(v->domain);
}
#endif




/*
 * Local variables:
 * mode: C
 * c-set-style: "BSD"
 * c-basic-offset: 4
 * indent-tabs-mode: nil
 * End: 
 */
