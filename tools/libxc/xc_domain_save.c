/******************************************************************************
 * xc_linux_save.c
 *
 * Modified for CoW by Mike Sun.
 *
 * Save the state of a running Linux session.
 *
 * Copyright (c) 2003, K A Fraser.
 */

#include <inttypes.h>
#include <time.h>
#include <stdlib.h>
#include <unistd.h>
#include <sys/time.h>
#include "xc_private.h"
#include "xc_dom.h"
#include "xg_private.h"
#include "xg_save_restore.h"
#include <xen/hvm/params.h>
#include "xc_e820.h"


/* file descriptor */
int fd;

/* max mfn of the whole machine */
static unsigned long max_mfn;

/* virtual starting address of the hypervisor */
static unsigned long hvirt_start;

/* # levels of page tables used by the current guest */
static unsigned int pt_levels;

/* HVM: shared-memory bitmaps for getting log-dirty bits from qemu-dm */
static unsigned long *qemu_bitmaps[2];
static int qemu_active;
static int qemu_non_active;

/* number of pfns this guest has (i.e. number of entries in the P2M) */
static unsigned long p2m_size;

/* Live mapping of the table mapping each PFN to its current MFN. */
static xen_pfn_t *live_p2m = NULL;

/* Live mapping of system MFN to PFN table. */
static xen_pfn_t *live_m2p = NULL;
static unsigned long m2p_mfn0;

/* Address size of the guest */
unsigned int guest_width;

/* grep fodder: machine_to_phys */

#define mfn_to_pfn(_mfn)  (live_m2p[(_mfn)])

#define pfn_to_mfn(_pfn)                                            \
  ((xen_pfn_t) ((guest_width==8)                                    \
                ? (((uint64_t *)live_p2m)[(_pfn)])                  \
                : ((((uint32_t *)live_p2m)[(_pfn)]) == 0xffffffffU  \
                   ? (-1UL) : (((uint32_t *)live_p2m)[(_pfn)]))))

/*
 * Returns TRUE if the given machine frame number has a unique mapping
 * in the guest's pseudophysical map.
 */
#define MFN_IS_IN_PSEUDOPHYS_MAP(_mfn)          \
    (((_mfn) < (max_mfn)) &&                    \
     ((mfn_to_pfn(_mfn) < (p2m_size)) &&        \
      (pfn_to_mfn(mfn_to_pfn(_mfn)) == (_mfn))))

#define BITS_PER_LONG (sizeof(unsigned long) * 8)
#define BITS_TO_LONGS(bits) (((bits)+BITS_PER_LONG-1)/BITS_PER_LONG)
#define BITMAP_SIZE   (BITS_TO_LONGS(p2m_size) * sizeof(unsigned long))

#define BITMAP_ENTRY(_nr,_bmap) \
   ((volatile unsigned long *)(_bmap))[(_nr)/BITS_PER_LONG]

#define BITMAP_SHIFT(_nr) ((_nr) % BITS_PER_LONG)

static inline int test_bit (int nr, volatile void * addr)
{
    return (BITMAP_ENTRY(nr, addr) >> BITMAP_SHIFT(nr)) & 1;
}

static inline void clear_bit (int nr, volatile void * addr)
{
    BITMAP_ENTRY(nr, addr) &= ~(1UL << BITMAP_SHIFT(nr));
}

static inline void set_bit ( int nr, volatile void * addr)
{
    BITMAP_ENTRY(nr, addr) |= (1UL << BITMAP_SHIFT(nr));
}

static int noncached_write(int fd, void *buffer, int len) 
{
    static int write_count = 0;
    int rc = (write_exact(fd, buffer, len) == 0) ? len : -1;

    write_count += len;
    if ( write_count >= (MAX_PAGECACHE_USAGE * PAGE_SIZE) )
    {
        /* Time to discard cache - dont care if this fails */
        discard_file_cache(fd, 0 /* no flush */);
        write_count = 0;
    }
    return rc;
}

/* Can we just pause this? */
static int suspend_and_state(int (*suspend)(int), int xc_handle, int io_fd,
                             int dom, xc_dominfo_t *info)
{
    int i = 0;

    if ( !(*suspend)(dom) )
    {
        ERROR("Suspend request failed");
        return -1;
    }

 retry:

    if ( xc_domain_getinfo(xc_handle, dom, 1, info) != 1 )
    {
        ERROR("Could not get domain info");
        return -1;
    }

    if ( info->dying )
    {
        ERROR("domain is dying");
        return -1;
    }

    if ( info->crashed )
    {
        ERROR("domain has crashed");
        return -1;
    }

    if ( info->shutdown )
    {
        switch ( info->shutdown_reason )
        {
            case SHUTDOWN_poweroff:
            case SHUTDOWN_reboot:
                ERROR("domain has shut down");
                return -1;
            case SHUTDOWN_suspend:
                return 0;
            case SHUTDOWN_crash:
                ERROR("domain has crashed");
                return -1;
        }
    }

    if ( info->paused )
    {
        /* Try unpausing domain, wait, and retest. */
        xc_domain_unpause( xc_handle, dom );
        ERROR("Domain was paused. Wait and re-test.");
        usleep(10000); /* 10ms */
        goto retry;
    }

    if ( ++i < 100 )
    {
        ERROR("Retry suspend domain");
        usleep(10000); /* 10ms */
        goto retry;
    }

    ERROR("Unable to suspend domain.");

    return -1;
}

static int restart_and_state(int (*restart)(int), int xc_handle, int io_fd,
                             int dom, xc_dominfo_t *info)
{
    if ( !(*restart)(dom) )
    {
        ERROR("Restart request failed");
        return -1;
    }
    usleep(1000000); /* 1s */

    /* FIX */
    return 0;
}

/*
** During transfer (or in the state file), all page-table pages must be
** converted into a 'canonical' form where references to actual mfns
** are replaced with references to the corresponding pfns.
**
** This function performs the appropriate conversion, taking into account
** which entries do not require canonicalization (in particular, those
** entries which map the virtual address reserved for the hypervisor).
*/
static int canonicalize_pagetable(unsigned long type, unsigned long pfn,
                           const void *spage, void *dpage)
{

    int i, pte_last, xen_start, xen_end, race = 0; 
    uint64_t pte;

    DPRINTF("canonicalize_pagetable()\n");

    /*
    ** We need to determine which entries in this page table hold
    ** reserved hypervisor mappings. This depends on the current
    ** page table type as well as the number of paging levels.
    */
    xen_start = xen_end = pte_last = PAGE_SIZE / ((pt_levels == 2) ? 4 : 8);

    if ( (pt_levels == 2) && (type == XEN_DOMCTL_PFINFO_L2TAB) )
        xen_start = (hvirt_start >> L2_PAGETABLE_SHIFT);

    if ( (pt_levels == 3) && (type == XEN_DOMCTL_PFINFO_L3TAB) )
        xen_start = L3_PAGETABLE_ENTRIES_PAE;

    /*
    ** In PAE only the L2 mapping the top 1GB contains Xen mappings.
    ** We can spot this by looking for the guest's mappingof the m2p.
    ** Guests must ensure that this check will fail for other L2s.
    */
    if ( (pt_levels == 3) && (type == XEN_DOMCTL_PFINFO_L2TAB) )
    {
        int hstart;
        uint64_t he;

        hstart = (hvirt_start >> L2_PAGETABLE_SHIFT_PAE) & 0x1ff;
        he = ((const uint64_t *) spage)[hstart];

        if ( ((he >> PAGE_SHIFT) & MFN_MASK_X86) == m2p_mfn0 )
        {
            /* hvirt starts with xen stuff... */
            xen_start = hstart;
        }
        else if ( hvirt_start != 0xf5800000 )
        {
            /* old L2s from before hole was shrunk... */
            hstart = (0xf5800000 >> L2_PAGETABLE_SHIFT_PAE) & 0x1ff;
            he = ((const uint64_t *) spage)[hstart];
            if ( ((he >> PAGE_SHIFT) & MFN_MASK_X86) == m2p_mfn0 )
                xen_start = hstart;
        }
    }

    if ( (pt_levels == 4) && (type == XEN_DOMCTL_PFINFO_L4TAB) )
    {
        /*
        ** XXX SMH: should compute these from hvirt_start (which we have)
        ** and hvirt_end (which we don't)
        */
        xen_start = 256;
        xen_end   = 272;
    }

    /* Now iterate through the page table, canonicalizing each PTE */
    for (i = 0; i < pte_last; i++ )
    {
        unsigned long pfn, mfn;

        if ( pt_levels == 2 )
            pte = ((const uint32_t*)spage)[i];
        else
            pte = ((const uint64_t*)spage)[i];

        if ( (i >= xen_start) && (i < xen_end) )
            pte = 0;

        if ( pte & _PAGE_PRESENT )
        {
            DPRINTF("page present in canonicalize\n");
            mfn = (pte >> PAGE_SHIFT) & MFN_MASK_X86;
            if ( !MFN_IS_IN_PSEUDOPHYS_MAP(mfn) )
            {
                /* This will happen if the type info is stale which
                   is quite feasible under live migration */
                pfn  = 0;  /* zap it - we'll retransmit this page later */
                /* XXX: We can't spot Xen mappings in compat-mode L2es 
                 * from 64-bit tools, but the only thing in them is the
                 * compat m2p, so we quietly zap them.  This doesn't
                 * count as a race, so don't report it. */
                if ( !(type == XEN_DOMCTL_PFINFO_L2TAB 
                       && sizeof (unsigned long) > guest_width) )
                     race = 1;  /* inform the caller; fatal if !live */ 
            }
            else
                pfn = mfn_to_pfn(mfn);

            pte &= ~MADDR_MASK_X86;
            pte |= (uint64_t)pfn << PAGE_SHIFT;

            /*
             * PAE guest L3Es can contain these flags when running on
             * a 64bit hypervisor. We zap these here to avoid any
             * surprise at restore time...
             */
            if ( (pt_levels == 3) &&
                 (type == XEN_DOMCTL_PFINFO_L3TAB) &&
                 (pte & (_PAGE_USER|_PAGE_RW|_PAGE_ACCESSED)) )
                pte &= ~(_PAGE_USER|_PAGE_RW|_PAGE_ACCESSED);
        }

        if ( pt_levels == 2 )
            ((uint32_t*)dpage)[i] = pte;
        else
            ((uint64_t*)dpage)[i] = pte;
    }
    if (memcmp(spage, dpage, PAGE_SIZE) == 0)
        DPRINTF("Canonicalized pages are same\n");

    return race;
}

int xc_domain_save(int xc_handle, int io_fd, uint32_t dom, uint32_t max_iters,
                   uint32_t max_factor, uint32_t flags, int (*suspend)(int),
                   int (*restart)(int), 
                   int hvm, void *(*init_qemu_maps)(int, unsigned), 
                   void (*qemu_flip_buffer)(int, int))
{
    int rc = 1, i, j;
    unsigned int fn, bcounter;
    
    /* Array of pfn + type for a batch */
    unsigned long *pfn_type = NULL;

    /* A copy of one frame of guest memory. */
    char page[PAGE_SIZE];

    /* CoW buffers. */
    unsigned long *cow_pfn_types = NULL;
    char *cow_pages = NULL;
    unsigned long cow_count = 0;
    unsigned long cow_buffers_size = 0;

    /* Base of the region in which domain memory is mapped */
    unsigned char *region_base = NULL;

    /* HVM: a buffer for holding HVM context */
    uint32_t hvm_buf_size = 0;
    uint8_t *hvm_buf = NULL;
    uint32_t rec_size; 

    /* HVM: magic frames for ioreqs and xenstore comms. */
    uint64_t magic_pfns[3]; /* ioreq_pfn, bufioreq_pfn, store_pfn */

    /* VCPU info */
    uint64_t vcpumap = 1ULL;
    xc_dominfo_t info;
    struct {
            int minustwo;
            int max_vcpu_id;
            uint64_t vcpumap;
    } chunk;

    unsigned long *cow_bitmap = NULL;

    unsigned int hfn;
    unsigned long *hot_bitmap = NULL;


    /* 
     * Get platform and runtime information
     */
    if (!get_platform_info(xc_handle, dom,
                           &max_mfn, &hvirt_start, &pt_levels, &guest_width))
    {
        ERROR("Unable to get platform info.");
        return 1;
    }

    if (xc_domain_getinfo(xc_handle, dom, 1, &info) != 1)
    {
        ERROR("Could not get domain info");
        return 1;
    }
    chunk.minustwo = -2;
    chunk.max_vcpu_id = info.max_vcpu_id;

    p2m_size = xc_memory_op(xc_handle, XENMEM_maximum_gpfn, &dom) + 1;
    cow_buffers_size = 
         xc_memory_op(xc_handle, XENMEM_maximum_reservation, &dom) + 1;

    
    /*
     * Allocate buffers for holding checkpoint state
     */

    /* buffer for HVM context */
    hvm_buf_size = xc_domain_hvm_getcontext(xc_handle, dom, 0, 0);
    if ( hvm_buf_size == -1 )
    {
        ERROR("Couldn't get HVM context size from Xen");
        goto out;
    }
    hvm_buf = malloc(hvm_buf_size);
    if ( !hvm_buf )
    {
        ERROR("Couldn't allocate memory");
        goto out;
    }

    /* CoW buffers */
    cow_pages = xg_memalign(PAGE_SIZE, PAGE_SIZE * cow_buffers_size); 
    if (cow_pages == NULL)
    {
        ERROR("Failed to alloc memory for cow_pages");
        goto out;
    }
    memset(cow_pages, 0, PAGE_SIZE * cow_buffers_size);
    if (lock_pages(cow_pages, PAGE_SIZE * cow_buffers_size))
    {
        ERROR("Unable to lock/pin cow_pages");
        goto out;
    }

    cow_pfn_types = xg_memalign(PAGE_SIZE,
                                ROUNDUP(sizeof(unsigned long) * 
                                        cow_buffers_size, PAGE_SHIFT));
    if (cow_pfn_types == NULL)
    {
        ERROR("Failed to alloc memory for cow_pfn_types");
        goto out;
    }
    memset(cow_pfn_types, 0, ROUNDUP(sizeof(unsigned long) *
                                     cow_buffers_size, PAGE_SHIFT));
    if (lock_pages(cow_pfn_types, sizeof(unsigned long) * 
                                  cow_buffers_size))
    {
        ERROR("Unable to lock/pin cow_pfn_types");
        goto out;
    }

    /* Batch pfn_type array */
    pfn_type = xg_memalign(PAGE_SIZE,
        ROUNDUP(MAX_BATCH_SIZE * sizeof(*pfn_type), PAGE_SHIFT));
    if (pfn_type == NULL)
    {
        ERROR("failed to alloc memory for pfn_type array");
        errno = ENOMEM;
        goto out;
    }
    memset(pfn_type, 0,
           ROUNDUP(MAX_BATCH_SIZE * sizeof(*pfn_type), PAGE_SHIFT));
    if (lock_pages(pfn_type, MAX_BATCH_SIZE * sizeof(*pfn_type)))
    {
        ERROR("Unable to lock pfn_type array");
        goto out;
    }

    /* hot bitmap */
    hot_bitmap = xg_memalign(PAGE_SIZE, ROUNDUP(BITMAP_SIZE, PAGE_SHIFT));
    memset(hot_bitmap, 0, BITMAP_SIZE);
    if (lock_pages(hot_bitmap, BITMAP_SIZE))
    {
        ERROR("Unable to lock hot_bitmap");
        goto out;
    }

    /* cow bitmap */
    cow_bitmap = xg_memalign(PAGE_SIZE, ROUNDUP(BITMAP_SIZE, PAGE_SHIFT));
    memset(cow_bitmap, 0, BITMAP_SIZE);
    if (lock_pages(cow_bitmap, BITMAP_SIZE))
    {
        ERROR("Unable to lock cow_bitmap");
        goto out;
    }


    /*
     * Start writing saved-domain record
     */
    if (write_exact(io_fd, &p2m_size, sizeof(unsigned long)))
    {
        ERROR("write: p2m_size");
        goto out;
    }


    /*
     * Suspend domain
     */
    DPRINTF("suspend_and_state() begin\n");
    if (suspend_and_state(suspend, xc_handle, io_fd, dom, &info))
    {
        ERROR("Domain appears not to have suspended");
        goto out;
    }


    /* 
     * Copy critical state before restarting domain 
     */

    /* VCPU data */
    if ( info.max_vcpu_id >= 64 )
    {
        ERROR("Too many VCPUS in guest!");
        goto out;
    }

    for (i = 1; i <= info.max_vcpu_id; i++)
    {
        xc_vcpuinfo_t vinfo;
        if ((xc_vcpu_getinfo(xc_handle, dom, i, &vinfo) == 0) && vinfo.online)
            vcpumap |= 1ULL << i;
    }
    chunk.vcpumap = vcpumap;

    /* magic-page locations */
    memset(magic_pfns, 0, sizeof(magic_pfns));
    xc_get_hvm_param(xc_handle, dom, HVM_PARAM_IOREQ_PFN, 
                     (unsigned long *)&magic_pfns[0]);
    xc_get_hvm_param(xc_handle, dom, HVM_PARAM_BUFIOREQ_PFN,
                     (unsigned long *)&magic_pfns[1]);
    xc_get_hvm_param(xc_handle, dom, HVM_PARAM_STORE_PFN,
                     (unsigned long *)&magic_pfns[2]);

    /* HVM context */
    if ((rec_size = xc_domain_hvm_getcontext(xc_handle, dom, hvm_buf, 
                                              hvm_buf_size)) == -1)
    {
        ERROR("HVM:Could not get hvm buffer");
        goto out;
    }


    /*
     * Turn on CoW + shadow-log-dirty-mode
     */
    DPRINTF("Turning on CoW mode\n");
    if (xc_cow_shadow_control(xc_handle, dom,
                              XEN_DOMCTL_SHADOW_COW_ON,
                              (unsigned long *) hot_bitmap,
                              (unsigned long *) cow_pages,
                              (unsigned long *) cow_pfn_types,
                              NULL,
                              NULL,
                              cow_buffers_size, 0, 0) < 0)
    {
        ERROR("Could not enable CoW mode");
        goto out;
    }
    else 
    {
        /* Get qemu-dm to log-dirty  */
        void *seg = init_qemu_maps(dom, BITMAP_SIZE);
        qemu_bitmaps[0] = seg;
        qemu_bitmaps[1] = seg + BITMAP_SIZE;
        qemu_active = 0;
        qemu_non_active = 1;
    }


    /*
     * Restart domain
     */
    DPRINTF("Restarting domain...\n");
    if (restart_and_state(restart, xc_handle, io_fd, dom, &info))
    {
        ERROR("Domain appears not to have restarted");
        goto out;
    }


    /*
     * Copy memory pages of running VM
     */
    /* Can also just copy those pages not already dirtied with peek op */
    for (fn = 0, hfn = 0; fn < p2m_size;)
    {
        bcounter = 0;

        /* go through hot pages first */
        for (; (bcounter < MAX_BATCH_SIZE) && (hfn < p2m_size); hfn++)
        {
            if (((hfn >= 0xa0 && hfn < 0xc0) /* VGA hole */
                 || (hfn >= (HVM_BELOW_4G_MMIO_START >> PAGE_SHIFT)
                        && hfn < (1ULL<<32) >> PAGE_SHIFT)) /* MMIO */)
                continue;

            if (test_bit(hfn, hot_bitmap) && 
                !test_bit(hfn, cow_bitmap) &&
                !test_bit(hfn, qemu_bitmaps[qemu_active]))
            {
                pfn_type[bcounter] = hfn;
                bcounter++;
            }
        }
        if (bcounter == MAX_BATCH_SIZE)
            ERROR("more hot pages than a batch");

        /* go through sequentially pfn address space */
        for (; (bcounter < MAX_BATCH_SIZE) && (fn < p2m_size); fn++)
        {
            /* Skip PFNs that aren't really there */
            if (((fn >= 0xa0 && fn < 0xc0) /* VGA hole */
                 || (fn >= (HVM_BELOW_4G_MMIO_START >> PAGE_SHIFT) 
                        && fn < (1ULL<<32) >> PAGE_SHIFT)) /* MMIO */)
                continue;

            /* Skip PFNs we have already copied */
            if (!test_bit(fn, hot_bitmap) && 
                !test_bit(fn, cow_bitmap) &&
                !test_bit(hfn, qemu_bitmaps[qemu_active]))
            {
                pfn_type[bcounter] = fn;
                bcounter++;
            }
        }

        /* nothing to copy, empty batch */
        if (bcounter == 0)
        {
            DPRINTF("bcounter == 0\n");
            goto copy_done;
        }

        /* Map batch of pages through hypervisor call */
        region_base = xc_map_foreign_batch(xc_handle, dom, PROT_READ,
                                           pfn_type, bcounter);
        if (region_base == NULL)
        {
            ERROR("Mapping of page failed");
            goto out;
        }

        /* Write pfn_type array out to saved_domain record */
        if (write_exact(io_fd, &bcounter, sizeof(unsigned int)))
        {
            ERROR("Error when writing to state file (2)");
            goto out;
        }
        if (write_exact(io_fd, pfn_type, sizeof(unsigned long) * bcounter))
        {
            ERROR("Error when writing to state file (3)");
            goto out;
        }

        /* Write batch of pages out to checkpoint */
        for (j = 0; j < bcounter; j++)
        {
            unsigned long pfn, pagetype;
            void *spage = (char *) region_base + (PAGE_SIZE * j);

            pfn = pfn_type[j] & ~XEN_DOMCTL_PFINFO_LTAB_MASK;
            pagetype = pfn_type[j] & XEN_DOMCTL_PFINFO_LTAB_MASK;

            if (pagetype == XEN_DOMCTL_PFINFO_XTAB)
                continue;

            pagetype &= XEN_DOMCTL_PFINFO_LTABTYPE_MASK;
            if ((pagetype >= XEN_DOMCTL_PFINFO_L1TAB) &&
                (pagetype <= XEN_DOMCTL_PFINFO_L4TAB))
            {
                DPRINTF("pagetable page 1\n");
                /* We have a pagetable page: need to rewrite it. */
                if (canonicalize_pagetable(pagetype, pfn,
                                           spage, page))
                {
                    ERROR("Fatal PT race (pfn %lx, type %lx)", pfn, pagetype);
                    goto out;
                }
                if (noncached_write(io_fd, page, PAGE_SIZE) != PAGE_SIZE)
                {
                    ERROR("Error when writing to state file (4)"
                          " (errno %d)", errno);
                    goto out;
                }
            }
            else
            {
                /* We have a normal page: just write it directly. */
                if (noncached_write(io_fd, spage, PAGE_SIZE) != PAGE_SIZE)
                {
                    ERROR("Error when writing to state file (5)"
                          " (errno %d)", errno);
                    goto out;
                }
            }
        }

        /* Unmap batch of pages */
        munmap(region_base, bcounter * PAGE_SIZE);

        /* Mark batch of pages dirty, so they can be writable again */
        if (xc_cow_shadow_control(xc_handle, 
                                  dom,
                                  XEN_DOMCTL_SHADOW_COW_MARK_DIRTY,
                                  NULL,
                                  NULL,
                                  pfn_type, 
                                  NULL,
                                  cow_bitmap, 
                                  bcounter, 0, 0) < 0)
        {
            ERROR("Could not mark batch of copied pages dirty/writable");
            goto out;
        }
    }
copy_done:


    /*
     * Turn off CoW/log-dirty
     */
    DPRINTF("Turning off CoW\n");
    if (xc_cow_shadow_control(xc_handle, 
                              dom, 
                              XEN_DOMCTL_SHADOW_COW_OFF,
                              NULL,
                              NULL, 
                              NULL, 
                              &cow_count,
                              NULL,
                              0, 0, 0) < 0)
    {
        ERROR("Could not disable CoW mode");
        goto out;
    }

    /*
     * Inform QEMU that log-dirty mode off
     * This can be improved via shared channel between hyp and ioemu
     */
    /* pseudo turn off qemu logdirty by making all dirty */


    /*
     * Write pages from CoW buffer to saved_record
     */
    DPRINTF("Writing CoW pages...\n");
    for (i = 0; i < cow_count; i += bcounter)
    {
        bcounter = MAX_BATCH_SIZE;
        if (bcounter + i > cow_count)
            bcounter = cow_count - i;

        if (write_exact(io_fd, &bcounter, sizeof(unsigned int)))
        {
            ERROR("Error when writing to state file (2)");
            goto out;
        }
        if (write_exact(io_fd, &(cow_pfn_types[i]), 
                        sizeof(unsigned long) * bcounter))
        {
            ERROR("Error when writing to state file (3)");
            goto out;
        }

        for (j = i; j < i + bcounter; j++)
        {
            unsigned long pfn, pagetype;

            pfn = cow_pfn_types[j] & ~XEN_DOMCTL_PFINFO_LTAB_MASK;
            pagetype = cow_pfn_types[j] & XEN_DOMCTL_PFINFO_LTAB_MASK;

            if (pagetype == XEN_DOMCTL_PFINFO_XTAB)
                continue;

            pagetype &= XEN_DOMCTL_PFINFO_LTABTYPE_MASK;

            if ((pagetype >= XEN_DOMCTL_PFINFO_L1TAB) &&
                (pagetype <= XEN_DOMCTL_PFINFO_L4TAB))
            {
                DPRINTF("pagetable page 2\n");
                /* We have a pagetable page: need to rewrite it. */
                if (canonicalize_pagetable(pagetype, 
                                           pfn, 
                                           &cow_pages[PAGE_SIZE * j], 
                                           page))
                {
                    ERROR("Fatal PT race (pfn %lx, type %lx)", pfn, pagetype);
                    goto out;
                }
                if (noncached_write(io_fd, page, PAGE_SIZE) != PAGE_SIZE)
                {
                    ERROR("Error when writing to state file (4) "
                          "(errno %d)", errno);
                    goto out;
                }
            }
            else
            {
                /* We have a normal page: just write it directly. */
                if (noncached_write(io_fd, 
                                    &cow_pages[PAGE_SIZE * j], 
                                    PAGE_SIZE) != PAGE_SIZE)
                {
                    ERROR("Error when writing to state file (5)"
                          " (errno %d)", errno);
                    goto out;
                }
            }
        }
    }
    
    /* Write chunk */
    DPRINTF("Writing chunk\n");
    if (write_exact(io_fd, &chunk, sizeof(chunk)))
    {
        ERROR("Error when writing to state file (errno %d)", errno);
        goto out;
    }

    /* Zero terminate */
    i = 0;
    if (write_exact(io_fd, &i, sizeof(int)))
    {
        ERROR("Error when writing to state file (6') (errno %d)", errno);
        goto out;
    }
    
    /* Save magic-page locations */
    DPRINTF("Writing magic_pfns, rec_size, hvm_buf\n");
    if (write_exact(io_fd, magic_pfns, sizeof(magic_pfns)))
    {
        ERROR("Error when writing to state file (7)");
        goto out;
    }

    /* Save HVM context */
    if (write_exact(io_fd, &rec_size, sizeof(uint32_t)))
    {
        ERROR("error write hvm buffer size");
        goto out;
    }
    if (write_exact(io_fd, hvm_buf, rec_size))
    {
        ERROR("write HVM info failed!\n");
        goto out;
    }


    /* 
     * Done and checkpoint successful 
     */
    DPRINTF("Checkpoint completed successfully.\n");
    rc = 0;

out:
    /* pseudo turn off qemu logdirty by making all dirty */
    qemu_active = qemu_non_active;
    qemu_non_active = qemu_active ? 0 : 1;
    qemu_flip_buffer(dom, qemu_active);
    for (j = 0; j < BITMAP_SIZE / sizeof(unsigned long); j++)
    {
        qemu_bitmaps[qemu_active][j] = 0xffffffff;
        qemu_bitmaps[qemu_non_active][j] = 0;
    }

    /* Flush last write and discard cache for file. */
    discard_file_cache(io_fd, 1 /* flush */);

    /* Free memory structures */
    free(hvm_buf);
    free(pfn_type);
    free(cow_pages);
    free(cow_pfn_types);
    free(hot_bitmap);   
    free(cow_bitmap);

    DPRINTF("Save exit rc=%d\n",rc);
    return !!rc;
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
