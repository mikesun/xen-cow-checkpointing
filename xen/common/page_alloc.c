/******************************************************************************
 * page_alloc.c
 * 
 * Simple buddy heap allocator for Xen.
 * 
 * Copyright (c) 2002-2004 K A Fraser
 * Copyright (c) 2006 IBM Ryan Harper <ryanh@us.ibm.com>
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
#include <xen/init.h>
#include <xen/types.h>
#include <xen/lib.h>
#include <xen/sched.h>
#include <xen/spinlock.h>
#include <xen/mm.h>
#include <xen/irq.h>
#include <xen/softirq.h>
#include <xen/domain_page.h>
#include <xen/keyhandler.h>
#include <xen/perfc.h>
#include <xen/numa.h>
#include <xen/nodemask.h>
#include <asm/page.h>
#include <asm/flushtlb.h>

/*
 * Comma-separated list of hexadecimal page numbers containing bad bytes.
 * e.g. 'badpage=0x3f45,0x8a321'.
 */
static char opt_badpage[100] = "";
string_param("badpage", opt_badpage);

/*
 * no-bootscrub -> Free pages are not zeroed during boot.
 */
static int opt_bootscrub __initdata = 1;
boolean_param("bootscrub", opt_bootscrub);

/*
 * Bit width of the DMA heap.
 */
static unsigned int dma_bitsize = CONFIG_DMA_BITSIZE;
static void __init parse_dma_bits(char *s)
{
    unsigned int v = simple_strtol(s, NULL, 0);
    if ( v >= (BITS_PER_LONG + PAGE_SHIFT) )
        dma_bitsize = BITS_PER_LONG + PAGE_SHIFT;
    else if ( v > PAGE_SHIFT + 1 )
        dma_bitsize = v;
    else
        printk("Invalid dma_bits value of %u ignored.\n", v);
}
custom_param("dma_bits", parse_dma_bits);

/*
 * Amount of memory to reserve in a low-memory (<4GB) pool for specific
 * allocation requests. Ordinary requests will not fall back to the
 * lowmem emergency pool.
 */
static unsigned long dma_emergency_pool_pages;
static void __init parse_dma_emergency_pool(char *s)
{
    unsigned long long bytes;
    bytes = parse_size_and_unit(s, NULL);
    dma_emergency_pool_pages = bytes >> PAGE_SHIFT;
}
custom_param("dma_emergency_pool", parse_dma_emergency_pool);

#define round_pgdown(_p)  ((_p)&PAGE_MASK)
#define round_pgup(_p)    (((_p)+(PAGE_SIZE-1))&PAGE_MASK)

#ifndef NDEBUG
/* Avoid callers relying on allocations returning zeroed pages. */
#define scrub_page(p) memset((p), 0xc2, PAGE_SIZE)
#else
/* For a production build, clear_page() is the fastest way to scrub. */
#define scrub_page(p) clear_page(p)
#endif

static DEFINE_SPINLOCK(page_scrub_lock);
LIST_HEAD(page_scrub_list);
static unsigned long scrub_pages;

/*********************
 * ALLOCATION BITMAP
 *  One bit per page of memory. Bit set => page is allocated.
 */

static unsigned long *alloc_bitmap;
#define PAGES_PER_MAPWORD (sizeof(unsigned long) * 8)

#define allocated_in_map(_pn)                       \
({  unsigned long ___pn = (_pn);                    \
    !!(alloc_bitmap[___pn/PAGES_PER_MAPWORD] &      \
       (1UL<<(___pn&(PAGES_PER_MAPWORD-1)))); })

/*
 * Hint regarding bitwise arithmetic in map_{alloc,free}:
 *  -(1<<n)  sets all bits >= n. 
 *  (1<<n)-1 sets all bits <  n.
 * Variable names in map_{alloc,free}:
 *  *_idx == Index into `alloc_bitmap' array.
 *  *_off == Bit offset within an element of the `alloc_bitmap' array.
 */

static void map_alloc(unsigned long first_page, unsigned long nr_pages)
{
    unsigned long start_off, end_off, curr_idx, end_idx;

#ifndef NDEBUG
    unsigned long i;
    /* Check that the block isn't already allocated. */
    for ( i = 0; i < nr_pages; i++ )
        ASSERT(!allocated_in_map(first_page + i));
#endif

    curr_idx  = first_page / PAGES_PER_MAPWORD;
    start_off = first_page & (PAGES_PER_MAPWORD-1);
    end_idx   = (first_page + nr_pages) / PAGES_PER_MAPWORD;
    end_off   = (first_page + nr_pages) & (PAGES_PER_MAPWORD-1);

    if ( curr_idx == end_idx )
    {
        alloc_bitmap[curr_idx] |= ((1UL<<end_off)-1) & -(1UL<<start_off);
    }
    else 
    {
        alloc_bitmap[curr_idx] |= -(1UL<<start_off);
        while ( ++curr_idx < end_idx ) alloc_bitmap[curr_idx] = ~0UL;
        alloc_bitmap[curr_idx] |= (1UL<<end_off)-1;
    }
}

static void map_free(unsigned long first_page, unsigned long nr_pages)
{
    unsigned long start_off, end_off, curr_idx, end_idx;

#ifndef NDEBUG
    unsigned long i;
    /* Check that the block isn't already freed. */
    for ( i = 0; i < nr_pages; i++ )
        ASSERT(allocated_in_map(first_page + i));
#endif

    curr_idx  = first_page / PAGES_PER_MAPWORD;
    start_off = first_page & (PAGES_PER_MAPWORD-1);
    end_idx   = (first_page + nr_pages) / PAGES_PER_MAPWORD;
    end_off   = (first_page + nr_pages) & (PAGES_PER_MAPWORD-1);

    if ( curr_idx == end_idx )
    {
        alloc_bitmap[curr_idx] &= -(1UL<<end_off) | ((1UL<<start_off)-1);
    }
    else 
    {
        alloc_bitmap[curr_idx] &= (1UL<<start_off)-1;
        while ( ++curr_idx != end_idx ) alloc_bitmap[curr_idx] = 0;
        alloc_bitmap[curr_idx] &= -(1UL<<end_off);
    }
}



/*************************
 * BOOT-TIME ALLOCATOR
 */

static unsigned long first_valid_mfn = ~0UL;

/* Initialise allocator to handle up to @max_page pages. */
paddr_t __init init_boot_allocator(paddr_t bitmap_start)
{
    unsigned long bitmap_size;

    bitmap_start = round_pgup(bitmap_start);

    /*
     * Allocate space for the allocation bitmap. Include an extra longword
     * of padding for possible overrun in map_alloc and map_free.
     */
    bitmap_size  = max_page / 8;
    bitmap_size += sizeof(unsigned long);
    bitmap_size  = round_pgup(bitmap_size);
    alloc_bitmap = (unsigned long *)maddr_to_virt(bitmap_start);

    /* All allocated by default. */
    memset(alloc_bitmap, ~0, bitmap_size);

    return bitmap_start + bitmap_size;
}

void __init init_boot_pages(paddr_t ps, paddr_t pe)
{
    unsigned long bad_spfn, bad_epfn, i;
    const char *p;

    ps = round_pgup(ps);
    pe = round_pgdown(pe);
    if ( pe <= ps )
        return;

    first_valid_mfn = min_t(unsigned long, ps >> PAGE_SHIFT, first_valid_mfn);

    map_free(ps >> PAGE_SHIFT, (pe - ps) >> PAGE_SHIFT);

    /* Check new pages against the bad-page list. */
    p = opt_badpage;
    while ( *p != '\0' )
    {
        bad_spfn = simple_strtoul(p, &p, 0);
        bad_epfn = bad_spfn;

        if ( *p == '-' )
        {
            p++;
            bad_epfn = simple_strtoul(p, &p, 0);
            if ( bad_epfn < bad_spfn )
                bad_epfn = bad_spfn;
        }

        if ( *p == ',' )
            p++;
        else if ( *p != '\0' )
            break;

        if ( bad_epfn == bad_spfn )
            printk("Marking page %lx as bad\n", bad_spfn);
        else
            printk("Marking pages %lx through %lx as bad\n",
                   bad_spfn, bad_epfn);

        for ( i = bad_spfn; i <= bad_epfn; i++ )
            if ( (i < max_page) && !allocated_in_map(i) )
                map_alloc(i, 1);
    }
}

unsigned long __init alloc_boot_pages(
    unsigned long nr_pfns, unsigned long pfn_align)
{
    unsigned long pg, i;

    /* Search backwards to obtain highest available range. */
    for ( pg = (max_page - nr_pfns) & ~(pfn_align - 1);
          pg >= first_valid_mfn;
          pg = (pg + i - nr_pfns) & ~(pfn_align - 1) )
    {
        for ( i = 0; i < nr_pfns; i++ )
            if ( allocated_in_map(pg+i) )
                break;
        if ( i == nr_pfns )
        {
            map_alloc(pg, nr_pfns);
            return pg;
        }
    }

    return 0;
}



/*************************
 * BINARY BUDDY ALLOCATOR
 */

#define MEMZONE_XEN 0
#ifdef PADDR_BITS
#define NR_ZONES    (PADDR_BITS - PAGE_SHIFT)
#else
#define NR_ZONES    (BITS_PER_LONG - PAGE_SHIFT)
#endif

#define pfn_dom_zone_type(_pfn) (fls(_pfn) - 1)

typedef struct list_head heap_by_zone_and_order_t[NR_ZONES][MAX_ORDER+1];
static heap_by_zone_and_order_t *_heap[MAX_NUMNODES];
#define heap(node, zone, order) ((*_heap[node])[zone][order])

static unsigned long *avail[MAX_NUMNODES];

static DEFINE_SPINLOCK(heap_lock);

static void init_node_heap(int node)
{
    /* First node to be discovered has its heap metadata statically alloced. */
    static heap_by_zone_and_order_t _heap_static;
    static unsigned long avail_static[NR_ZONES];
    static int first_node_initialised;

    int i, j;

    if ( !first_node_initialised )
    {
        _heap[node] = &_heap_static;
        avail[node] = avail_static;
        first_node_initialised = 1;
    }
    else
    {
        _heap[node] = xmalloc(heap_by_zone_and_order_t);
        avail[node] = xmalloc_array(unsigned long, NR_ZONES);
        BUG_ON(!_heap[node] || !avail[node]);
    }

    memset(avail[node], 0, NR_ZONES * sizeof(long));

    for ( i = 0; i < NR_ZONES; i++ )
        for ( j = 0; j <= MAX_ORDER; j++ )
            INIT_LIST_HEAD(&(*_heap[node])[i][j]);
}

/* Allocate 2^@order contiguous pages. */
static struct page_info *alloc_heap_pages(
    unsigned int zone_lo, unsigned int zone_hi,
    unsigned int cpu, unsigned int order)
{
    unsigned int i, j, zone;
    unsigned int node = cpu_to_node(cpu), num_nodes = num_online_nodes();
    unsigned long request = 1UL << order;
    cpumask_t extra_cpus_mask, mask;
    struct page_info *pg;

    ASSERT(node >= 0);
    ASSERT(node < num_nodes);
    ASSERT(zone_lo <= zone_hi);
    ASSERT(zone_hi < NR_ZONES);

    if ( unlikely(order > MAX_ORDER) )
        return NULL;

    spin_lock(&heap_lock);

    /*
     * Start with requested node, but exhaust all node memory in requested 
     * zone before failing, only calc new node value if we fail to find memory 
     * in target node, this avoids needless computation on fast-path.
     */
    for ( i = 0; i < num_nodes; i++ )
    {
        zone = zone_hi;
        do {
            /* Check if target node can support the allocation. */
            if ( !avail[node] || (avail[node][zone] < request) )
                continue;

            /* Find smallest order which can satisfy the request. */
            for ( j = order; j <= MAX_ORDER; j++ )
                if ( !list_empty(&heap(node, zone, j)) )
                    goto found;
        } while ( zone-- > zone_lo ); /* careful: unsigned zone may wrap */

        /* Pick next node, wrapping around if needed. */
        if ( ++node == num_nodes )
            node = 0;
    }

    /* No suitable memory blocks. Fail the request. */
    spin_unlock(&heap_lock);
    return NULL;

 found: 
    pg = list_entry(heap(node, zone, j).next, struct page_info, list);
    list_del(&pg->list);

    /* We may have to halve the chunk a number of times. */
    while ( j != order )
    {
        PFN_ORDER(pg) = --j;
        list_add_tail(&pg->list, &heap(node, zone, j));
        pg += 1 << j;
    }
    
    map_alloc(page_to_mfn(pg), request);
    ASSERT(avail[node][zone] >= request);
    avail[node][zone] -= request;

    spin_unlock(&heap_lock);

    cpus_clear(mask);

    for ( i = 0; i < (1 << order); i++ )
    {
        /* Reference count must continuously be zero for free pages. */
        BUG_ON(pg[i].count_info != 0);

        /* Add in any extra CPUs that need flushing because of this page. */
        cpus_andnot(extra_cpus_mask, pg[i].u.free.cpumask, mask);
        tlbflush_filter(extra_cpus_mask, pg[i].tlbflush_timestamp);
        cpus_or(mask, mask, extra_cpus_mask);

        /* Initialise fields which have other uses for free pages. */
        pg[i].u.inuse.type_info = 0;
        page_set_owner(&pg[i], NULL);
    }

    if ( unlikely(!cpus_empty(mask)) )
    {
        perfc_incr(need_flush_tlb_flush);
        flush_tlb_mask(mask);
    }

    return pg;
}

/* Free 2^@order set of pages. */
static void free_heap_pages(
    unsigned int zone, struct page_info *pg, unsigned int order)
{
    unsigned long mask;
    unsigned int i, node = phys_to_nid(page_to_maddr(pg));
    struct domain *d;

    ASSERT(zone < NR_ZONES);
    ASSERT(order <= MAX_ORDER);
    ASSERT(node >= 0);
    ASSERT(node < num_online_nodes());

    for ( i = 0; i < (1 << order); i++ )
    {
        /*
         * Cannot assume that count_info == 0, as there are some corner cases
         * where it isn't the case and yet it isn't a bug:
         *  1. page_get_owner() is NULL
         *  2. page_get_owner() is a domain that was never accessible by
         *     its domid (e.g., failed to fully construct the domain).
         *  3. page was never addressable by the guest (e.g., it's an
         *     auto-translate-physmap guest and the page was never included
         *     in its pseudophysical address space).
         * In all the above cases there can be no guest mappings of this page.
         */
        pg[i].count_info = 0;

        if ( (d = page_get_owner(&pg[i])) != NULL )
        {
            pg[i].tlbflush_timestamp = tlbflush_current_time();
            pg[i].u.free.cpumask     = d->domain_dirty_cpumask;
        }
        else
        {
            cpus_clear(pg[i].u.free.cpumask);
        }
    }

    spin_lock(&heap_lock);

    map_free(page_to_mfn(pg), 1 << order);
    avail[node][zone] += 1 << order;

    /* Merge chunks as far as possible. */
    while ( order < MAX_ORDER )
    {
        mask = 1UL << order;

        if ( (page_to_mfn(pg) & mask) )
        {
            /* Merge with predecessor block? */
            if ( allocated_in_map(page_to_mfn(pg)-mask) ||
                 (PFN_ORDER(pg-mask) != order) )
                break;
            list_del(&(pg-mask)->list);
            pg -= mask;
        }
        else
        {
            /* Merge with successor block? */
            if ( allocated_in_map(page_to_mfn(pg)+mask) ||
                 (PFN_ORDER(pg+mask) != order) )
                break;
            list_del(&(pg+mask)->list);
        }
        
        order++;

        /* After merging, pg should remain in the same node. */
        ASSERT(phys_to_nid(page_to_maddr(pg)) == node);
    }

    PFN_ORDER(pg) = order;
    list_add_tail(&pg->list, &heap(node, zone, order));

    spin_unlock(&heap_lock);
}

/*
 * Hand the specified arbitrary page range to the specified heap zone
 * checking the node_id of the previous page.  If they differ and the
 * latter is not on a MAX_ORDER boundary, then we reserve the page by
 * not freeing it to the buddy allocator.
 */
#define MAX_ORDER_ALIGNED (1UL << (MAX_ORDER))
static void init_heap_pages(
    unsigned int zone, struct page_info *pg, unsigned long nr_pages)
{
    unsigned int nid_curr, nid_prev;
    unsigned long i;

    ASSERT(zone < NR_ZONES);

    if ( likely(page_to_mfn(pg) != 0) )
        nid_prev = phys_to_nid(page_to_maddr(pg-1));
    else
        nid_prev = phys_to_nid(page_to_maddr(pg));

    for ( i = 0; i < nr_pages; i++ )
    {
        nid_curr = phys_to_nid(page_to_maddr(pg+i));

        if ( unlikely(!avail[nid_curr]) )
            init_node_heap(nid_curr);

        /*
         * free pages of the same node, or if they differ, but are on a
         * MAX_ORDER alignement boundary (which already get reserved)
         */
         if ( (nid_curr == nid_prev) || (page_to_maddr(pg+i) &
                                         MAX_ORDER_ALIGNED) )
             free_heap_pages(zone, pg+i, 0);
         else
             printk("Reserving non-aligned node boundary @ mfn %lu\n",
                    page_to_mfn(pg+i));

        nid_prev = nid_curr;
    }
}

static unsigned long avail_heap_pages(
    unsigned int zone_lo, unsigned int zone_hi, unsigned int node)
{
    unsigned int i, zone, num_nodes = num_online_nodes();
    unsigned long free_pages = 0;

    if ( zone_hi >= NR_ZONES )
        zone_hi = NR_ZONES - 1;

    for ( i = 0; i < num_nodes; i++ )
    {
        if ( !avail[i] )
            continue;
        for ( zone = zone_lo; zone <= zone_hi; zone++ )
            if ( (node == -1) || (node == i) )
                free_pages += avail[i][zone];
    }

    return free_pages;
}

#define avail_for_domheap(mfn) !(allocated_in_map(mfn) || is_xen_heap_mfn(mfn))
void __init end_boot_allocator(void)
{
    unsigned long i;
    int curr_free, next_free;

    /* Pages that are free now go to the domain sub-allocator. */
    if ( (curr_free = next_free = avail_for_domheap(first_valid_mfn)) )
        map_alloc(first_valid_mfn, 1);
    for ( i = first_valid_mfn; i < max_page; i++ )
    {
        curr_free = next_free;
        next_free = avail_for_domheap(i+1);
        if ( next_free )
            map_alloc(i+1, 1); /* prevent merging in free_heap_pages() */
        if ( curr_free )
            init_heap_pages(pfn_dom_zone_type(i), mfn_to_page(i), 1);
    }

    printk("Domain heap initialised: DMA width %u bits\n", dma_bitsize);
}
#undef avail_for_domheap

/*
 * Scrub all unallocated pages in all heap zones. This function is more
 * convoluted than appears necessary because we do not want to continuously
 * hold the lock while scrubbing very large memory areas.
 */
void __init scrub_heap_pages(void)
{
    void *p;
    unsigned long mfn;

    if ( !opt_bootscrub )
        return;

    printk("Scrubbing Free RAM: ");

    for ( mfn = first_valid_mfn; mfn < max_page; mfn++ )
    {
        process_pending_timers();

        /* Quick lock-free check. */
        if ( allocated_in_map(mfn) )
            continue;

        /* Every 100MB, print a progress dot. */
        if ( (mfn % ((100*1024*1024)/PAGE_SIZE)) == 0 )
            printk(".");

        spin_lock(&heap_lock);

        /* Re-check page status with lock held. */
        if ( !allocated_in_map(mfn) )
        {
            if ( is_xen_heap_mfn(mfn) )
            {
                p = page_to_virt(mfn_to_page(mfn));
                memguard_unguard_range(p, PAGE_SIZE);
                scrub_page(p);
                memguard_guard_range(p, PAGE_SIZE);
            }
            else
            {
                p = map_domain_page(mfn);
                scrub_page(p);
                unmap_domain_page(p);
            }
        }

        spin_unlock(&heap_lock);
    }

    printk("done.\n");
}



/*************************
 * XEN-HEAP SUB-ALLOCATOR
 */

void init_xenheap_pages(paddr_t ps, paddr_t pe)
{
    ps = round_pgup(ps);
    pe = round_pgdown(pe);
    if ( pe <= ps )
        return;

    memguard_guard_range(maddr_to_virt(ps), pe - ps);

    /*
     * Yuk! Ensure there is a one-page buffer between Xen and Dom zones, to
     * prevent merging of power-of-two blocks across the zone boundary.
     */
    if ( ps && !is_xen_heap_mfn(paddr_to_pfn(ps)-1) )
        ps += PAGE_SIZE;
    if ( !is_xen_heap_mfn(paddr_to_pfn(pe)) )
        pe -= PAGE_SIZE;

    init_heap_pages(MEMZONE_XEN, maddr_to_page(ps), (pe - ps) >> PAGE_SHIFT);
}


void *alloc_xenheap_pages(unsigned int order)
{
    struct page_info *pg;

    ASSERT(!in_irq());

    pg = alloc_heap_pages(MEMZONE_XEN, MEMZONE_XEN, smp_processor_id(), order);
    if ( unlikely(pg == NULL) )
        goto no_memory;

    memguard_unguard_range(page_to_virt(pg), 1 << (order + PAGE_SHIFT));

    return page_to_virt(pg);

 no_memory:
    printk("Cannot handle page request order %d!\n", order);
    return NULL;
}


void free_xenheap_pages(void *v, unsigned int order)
{
    ASSERT(!in_irq());

    if ( v == NULL )
        return;

    memguard_guard_range(v, 1 << (order + PAGE_SHIFT));

    free_heap_pages(MEMZONE_XEN, virt_to_page(v), order);
}



/*************************
 * DOMAIN-HEAP SUB-ALLOCATOR
 */

void init_domheap_pages(paddr_t ps, paddr_t pe)
{
    unsigned long s_tot, e_tot;
    unsigned int zone;

    ASSERT(!in_irq());

    s_tot = round_pgup(ps) >> PAGE_SHIFT;
    e_tot = round_pgdown(pe) >> PAGE_SHIFT;

    zone = fls(s_tot);
    BUG_ON(zone <= MEMZONE_XEN + 1);
    for ( --zone; s_tot < e_tot; ++zone )
    {
        unsigned long end = e_tot;

        BUILD_BUG_ON(NR_ZONES > BITS_PER_LONG);
        if ( zone < BITS_PER_LONG - 1 && end > 1UL << (zone + 1) )
            end = 1UL << (zone + 1);
        init_heap_pages(zone, mfn_to_page(s_tot), end - s_tot);
        s_tot = end;
    }
}


int assign_pages(
    struct domain *d,
    struct page_info *pg,
    unsigned int order,
    unsigned int memflags)
{
    unsigned long i;

    spin_lock(&d->page_alloc_lock);

    if ( unlikely(d->is_dying) )
    {
        gdprintk(XENLOG_INFO, "Cannot assign page to domain%d -- dying.\n",
                d->domain_id);
        goto fail;
    }

    if ( !(memflags & MEMF_no_refcount) )
    {
        if ( unlikely((d->tot_pages + (1 << order)) > d->max_pages) )
        {
            gdprintk(XENLOG_INFO, "Over-allocation for domain %u: %u > %u\n",
                    d->domain_id, d->tot_pages + (1 << order), d->max_pages);
            goto fail;
        }

        if ( unlikely(d->tot_pages == 0) )
            get_knownalive_domain(d);

        d->tot_pages += 1 << order;
    }

    for ( i = 0; i < (1 << order); i++ )
    {
        ASSERT(page_get_owner(&pg[i]) == NULL);
        ASSERT((pg[i].count_info & ~(PGC_allocated | 1)) == 0);
        page_set_owner(&pg[i], d);
        wmb(); /* Domain pointer must be visible before updating refcnt. */
        pg[i].count_info = PGC_allocated | 1;
        list_add_tail(&pg[i].list, &d->page_list);
    }

    spin_unlock(&d->page_alloc_lock);
    return 0;

 fail:
    spin_unlock(&d->page_alloc_lock);
    return -1;
}


struct page_info *__alloc_domheap_pages(
    struct domain *d, unsigned int cpu, unsigned int order, 
    unsigned int memflags)
{
    struct page_info *pg = NULL;
    unsigned int bits = memflags >> _MEMF_bits, zone_hi = NR_ZONES - 1;

    ASSERT(!in_irq());

    bits = domain_clamp_alloc_bitsize(d, bits ? : (BITS_PER_LONG+PAGE_SHIFT));
    if ( bits <= (PAGE_SHIFT + 1) )
        return NULL;

    bits -= PAGE_SHIFT + 1;
    if ( bits < zone_hi )
        zone_hi = bits;

    if ( (zone_hi + PAGE_SHIFT) >= dma_bitsize )
    {
        pg = alloc_heap_pages(dma_bitsize - PAGE_SHIFT, zone_hi, cpu, order);

        /* Failure? Then check if we can fall back to the DMA pool. */
        if ( unlikely(pg == NULL) &&
             ((order > MAX_ORDER) ||
              (avail_heap_pages(MEMZONE_XEN + 1,
                                dma_bitsize - PAGE_SHIFT - 1,
                                -1) <
               (dma_emergency_pool_pages + (1UL << order)))) )
            return NULL;
    }

    if ( (pg == NULL) &&
         ((pg = alloc_heap_pages(MEMZONE_XEN + 1, zone_hi,
                                 cpu, order)) == NULL) )
         return NULL;

    if ( (d != NULL) && assign_pages(d, pg, order, memflags) )
    {
        free_heap_pages(pfn_dom_zone_type(page_to_mfn(pg)), pg, order);
        return NULL;
    }
    
    return pg;
}

struct page_info *alloc_domheap_pages(
    struct domain *d, unsigned int order, unsigned int flags)
{
    return __alloc_domheap_pages(d, smp_processor_id(), order, flags);
}

void free_domheap_pages(struct page_info *pg, unsigned int order)
{
    int            i, drop_dom_ref;
    struct domain *d = page_get_owner(pg);

    ASSERT(!in_irq());

    if ( unlikely(is_xen_heap_page(pg)) )
    {
        /* NB. May recursively lock from relinquish_memory(). */
        spin_lock_recursive(&d->page_alloc_lock);

        for ( i = 0; i < (1 << order); i++ )
            list_del(&pg[i].list);

        d->xenheap_pages -= 1 << order;
        drop_dom_ref = (d->xenheap_pages == 0);

        spin_unlock_recursive(&d->page_alloc_lock);
    }
    else if ( likely(d != NULL) )
    {
        /* NB. May recursively lock from relinquish_memory(). */
        spin_lock_recursive(&d->page_alloc_lock);

        for ( i = 0; i < (1 << order); i++ )
        {
            BUG_ON((pg[i].u.inuse.type_info & PGT_count_mask) != 0);
            list_del(&pg[i].list);
        }

        d->tot_pages -= 1 << order;
        drop_dom_ref = (d->tot_pages == 0);

        spin_unlock_recursive(&d->page_alloc_lock);

        if ( likely(!d->is_dying) )
        {
            free_heap_pages(pfn_dom_zone_type(page_to_mfn(pg)), pg, order);
        }
        else
        {
            /*
             * Normally we expect a domain to clear pages before freeing them,
             * if it cares about the secrecy of their contents. However, after
             * a domain has died we assume responsibility for erasure.
             */
            for ( i = 0; i < (1 << order); i++ )
            {
                page_set_owner(&pg[i], NULL);
                spin_lock(&page_scrub_lock);
                list_add(&pg[i].list, &page_scrub_list);
                scrub_pages++;
                spin_unlock(&page_scrub_lock);
            }
        }
    }
    else
    {
        /* Freeing anonymous domain-heap pages. */
        free_heap_pages(pfn_dom_zone_type(page_to_mfn(pg)), pg, order);
        drop_dom_ref = 0;
    }

    if ( drop_dom_ref )
        put_domain(d);
}

unsigned long avail_domheap_pages_region(
    unsigned int node, unsigned int min_width, unsigned int max_width)
{
    int zone_lo, zone_hi;

    zone_lo = min_width ? (min_width - (PAGE_SHIFT + 1)) : (MEMZONE_XEN + 1);
    zone_lo = max_t(int, MEMZONE_XEN + 1, zone_lo);
    zone_lo = min_t(int, NR_ZONES - 1, zone_lo);

    zone_hi = max_width ? (max_width - (PAGE_SHIFT + 1)) : (NR_ZONES - 1);
    zone_hi = max_t(int, MEMZONE_XEN + 1, zone_hi);
    zone_hi = min_t(int, NR_ZONES - 1, zone_hi);

    return avail_heap_pages(zone_lo, zone_hi, node);
}

unsigned long avail_domheap_pages(void)
{
    unsigned long avail_nrm, avail_dma;
    
    avail_nrm = avail_heap_pages(dma_bitsize - PAGE_SHIFT,
                                 NR_ZONES - 1,
                                 -1);

    avail_dma = avail_heap_pages(MEMZONE_XEN + 1,
                                 dma_bitsize - PAGE_SHIFT - 1,
                                 -1);

    if ( avail_dma > dma_emergency_pool_pages )
        avail_dma -= dma_emergency_pool_pages;
    else
        avail_dma = 0;

    return avail_nrm + avail_dma;
}

static void pagealloc_keyhandler(unsigned char key)
{
    unsigned int zone = MEMZONE_XEN;
    unsigned long total = 0;

    printk("Physical memory information:\n");
    printk("    Xen heap: %lukB free\n",
           avail_heap_pages(zone, zone, -1) << (PAGE_SHIFT-10));

    while ( ++zone < NR_ZONES )
    {
        unsigned long n;

        if ( zone == dma_bitsize - PAGE_SHIFT )
        {
            printk("    DMA heap: %lukB free\n", total << (PAGE_SHIFT-10));
            total = 0;
        }

        if ( (n = avail_heap_pages(zone, zone, -1)) != 0 )
        {
            total += n;
            printk("    heap[%02u]: %lukB free\n", zone, n << (PAGE_SHIFT-10));
        }
    }

    printk("    Dom heap: %lukB free\n", total << (PAGE_SHIFT-10));
}


static __init int pagealloc_keyhandler_init(void)
{
    register_keyhandler('m', pagealloc_keyhandler, "memory info");
    return 0;
}
__initcall(pagealloc_keyhandler_init);



/*************************
 * PAGE SCRUBBING
 */

static DEFINE_PER_CPU(struct timer, page_scrub_timer);

static void page_scrub_softirq(void)
{
    struct list_head *ent;
    struct page_info  *pg;
    void             *p;
    int               i;
    s_time_t          start = NOW();

    /* Aim to do 1ms of work every 10ms. */
    do {
        spin_lock(&page_scrub_lock);

        if ( unlikely((ent = page_scrub_list.next) == &page_scrub_list) )
        {
            spin_unlock(&page_scrub_lock);
            return;
        }
        
        /* Peel up to 16 pages from the list. */
        for ( i = 0; i < 16; i++ )
        {
            if ( ent->next == &page_scrub_list )
                break;
            ent = ent->next;
        }
        
        /* Remove peeled pages from the list. */
        ent->next->prev = &page_scrub_list;
        page_scrub_list.next = ent->next;
        scrub_pages -= (i+1);

        spin_unlock(&page_scrub_lock);

        /* Working backwards, scrub each page in turn. */
        while ( ent != &page_scrub_list )
        {
            pg = list_entry(ent, struct page_info, list);
            ent = ent->prev;
            p = map_domain_page(page_to_mfn(pg));
            scrub_page(p);
            unmap_domain_page(p);
            free_heap_pages(pfn_dom_zone_type(page_to_mfn(pg)), pg, 0);
        }
    } while ( (NOW() - start) < MILLISECS(1) );

    set_timer(&this_cpu(page_scrub_timer), NOW() + MILLISECS(10));
}

static void page_scrub_timer_fn(void *unused)
{
    page_scrub_schedule_work();
}

unsigned long avail_scrub_pages(void)
{
    return scrub_pages;
}

static void dump_heap(unsigned char key)
{
    s_time_t      now = NOW();
    int           i, j;

    printk("'%c' pressed -> dumping heap info (now-0x%X:%08X)\n", key,
           (u32)(now>>32), (u32)now);

    for ( i = 0; i < MAX_NUMNODES; i++ )
    {
        if ( !avail[i] )
            continue;
        for ( j = 0; j < NR_ZONES; j++ )
            printk("heap[node=%d][zone=%d] -> %lu pages\n",
                   i, j, avail[i][j]);
    }
}

static __init int register_heap_trigger(void)
{
    register_keyhandler('H', dump_heap, "dump heap info");
    return 0;
}
__initcall(register_heap_trigger);


static __init int page_scrub_init(void)
{
    int cpu;
    for_each_cpu ( cpu )
        init_timer(&per_cpu(page_scrub_timer, cpu),
                   page_scrub_timer_fn, NULL, cpu);
    open_softirq(PAGE_SCRUB_SOFTIRQ, page_scrub_softirq);
    return 0;
}
__initcall(page_scrub_init);

/*
 * Local variables:
 * mode: C
 * c-set-style: "BSD"
 * c-basic-offset: 4
 * tab-width: 4
 * indent-tabs-mode: nil
 * End:
 */
