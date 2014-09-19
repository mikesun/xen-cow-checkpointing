/******************************************************************************
 * xc_domain_restore.c
 *
 * Restore the state of a guest session.
 *
 * Copyright (c) 2003, K A Fraser.
 * Copyright (c) 2006, Intel Corporation
 * Copyright (c) 2007, XenSource Inc.
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
 *
 */

#include <stdlib.h>
#include <unistd.h>

#include "xg_private.h"
#include "xg_save_restore.h"
#include "xc_dom.h"

#include <xen/hvm/ioreq.h>
#include <xen/hvm/params.h>

/* max mfn of the current host machine */
static unsigned long max_mfn;

/* virtual starting address of the hypervisor */
static unsigned long hvirt_start;

/* #levels of page tables used by the current guest */
static unsigned int pt_levels;

/* number of pfns this guest has (i.e. number of entries in the P2M) */
static unsigned long p2m_size;

/* number of 'in use' pfns in the guest (i.e. #P2M entries with a valid mfn) */
static unsigned long nr_pfns;

/* Live mapping of the table mapping each PFN to its current MFN. */
static xen_pfn_t *live_p2m = NULL;

/* A table mapping each PFN to its new MFN. */
static xen_pfn_t *p2m = NULL;

/* A table of P2M mappings in the current region */
static xen_pfn_t *p2m_batch = NULL;

/* Address size of the guest, in bytes */
unsigned int guest_width;

/*
** In the state file (or during transfer), all page-table pages are
** converted into a 'canonical' form where references to actual mfns
** are replaced with references to the corresponding pfns.
** This function inverts that operation, replacing the pfn values with
** the (now known) appropriate mfn values.
*/
static int uncanonicalize_pagetable(int xc_handle, uint32_t dom, 
                                    unsigned long type, void *page)
{
    int i, pte_last;
    unsigned long pfn;
    uint64_t pte;
    int nr_mfns = 0; 

    pte_last = PAGE_SIZE / ((pt_levels == 2)? 4 : 8);

    /* First pass: work out how many (if any) MFNs we need to alloc */
    for ( i = 0; i < pte_last; i++ )
    {
        if ( pt_levels == 2 )
            pte = ((uint32_t *)page)[i];
        else
            pte = ((uint64_t *)page)[i];

        /* XXX SMH: below needs fixing for PROT_NONE etc */
        if ( !(pte & _PAGE_PRESENT) )
            continue;
        
        pfn = (pte >> PAGE_SHIFT) & MFN_MASK_X86;
        
        if ( pfn >= p2m_size )
        {
            /* This "page table page" is probably not one; bail. */
            ERROR("Frame number in type %lu page table is out of range: "
                  "i=%d pfn=0x%lx p2m_size=%lu",
                  type >> 28, i, pfn, p2m_size);
            return 0;
        }
        
        if ( p2m[pfn] == INVALID_P2M_ENTRY )
        {
            /* Have a 'valid' PFN without a matching MFN - need to alloc */
            p2m_batch[nr_mfns++] = pfn; 
            p2m[pfn]--;
        }
    }

    /* Allocate the requisite number of mfns. */
    if ( nr_mfns &&
         (xc_domain_memory_populate_physmap(xc_handle, dom, nr_mfns, 0, 0,
                                            p2m_batch) != 0) )
    { 
        ERROR("Failed to allocate memory for batch.!\n"); 
        errno = ENOMEM;
        return 0; 
    }
    
    /* Second pass: uncanonicalize each present PTE */
    nr_mfns = 0;
    for ( i = 0; i < pte_last; i++ )
    {
        if ( pt_levels == 2 )
            pte = ((uint32_t *)page)[i];
        else
            pte = ((uint64_t *)page)[i];
        
        /* XXX SMH: below needs fixing for PROT_NONE etc */
        if ( !(pte & _PAGE_PRESENT) )
            continue;
        
        pfn = (pte >> PAGE_SHIFT) & MFN_MASK_X86;

        if ( p2m[pfn] == (INVALID_P2M_ENTRY-1) )
            p2m[pfn] = p2m_batch[nr_mfns++];

        pte &= ~MADDR_MASK_X86;
        pte |= (uint64_t)p2m[pfn] << PAGE_SHIFT;

        if ( pt_levels == 2 )
            ((uint32_t *)page)[i] = (uint32_t)pte;
        else
            ((uint64_t *)page)[i] = (uint64_t)pte;
    }

    return 1;
}


/* Load the p2m frame list, plus potential extended info chunk */
static xen_pfn_t *load_p2m_frame_list(
    int io_fd, int *pae_extended_cr3, int *ext_vcpucontext)
{
    xen_pfn_t *p2m_frame_list;
    vcpu_guest_context_either_t ctxt;
    xen_pfn_t p2m_fl_zero;

    /* Read first entry of P2M list, or extended-info signature (~0UL). */
    if ( read_exact(io_fd, &p2m_fl_zero, sizeof(long)) )
    {
        ERROR("read extended-info signature failed");
        return NULL;
    }
    
    if ( p2m_fl_zero == ~0UL )
    {
        uint32_t tot_bytes;
        
        /* Next 4 bytes: total size of following extended info. */
        if ( read_exact(io_fd, &tot_bytes, sizeof(tot_bytes)) )
        {
            ERROR("read extended-info size failed");
            return NULL;
        }
        
        while ( tot_bytes )
        {
            uint32_t chunk_bytes;
            char     chunk_sig[4];
            
            /* 4-character chunk signature + 4-byte remaining chunk size. */
            if ( read_exact(io_fd, chunk_sig, sizeof(chunk_sig)) ||
                 read_exact(io_fd, &chunk_bytes, sizeof(chunk_bytes)) ||
                 (tot_bytes < (chunk_bytes + 8)) )
            {
                ERROR("read extended-info chunk signature failed");
                return NULL;
            }
            tot_bytes -= 8;

            /* VCPU context structure? */
            if ( !strncmp(chunk_sig, "vcpu", 4) )
            {
                /* Pick a guest word-size and PT depth from the ctxt size */
                if ( chunk_bytes == sizeof (ctxt.x32) )
                {
                    guest_width = 4;
                    if ( pt_levels > 2 ) 
                        pt_levels = 3; 
                }
                else if ( chunk_bytes == sizeof (ctxt.x64) )
                {
                    guest_width = 8;
                    pt_levels = 4;
                }
                else 
                {
                    ERROR("bad extended-info context size %d", chunk_bytes);
                    return NULL;
                }

                if ( read_exact(io_fd, &ctxt, chunk_bytes) )
                {
                    ERROR("read extended-info vcpu context failed");
                    return NULL;
                }
                tot_bytes -= chunk_bytes;
                chunk_bytes = 0;

                if ( GET_FIELD(&ctxt, vm_assist) 
                     & (1UL << VMASST_TYPE_pae_extended_cr3) )
                    *pae_extended_cr3 = 1;
            }
            else if ( !strncmp(chunk_sig, "extv", 4) )
            {
                *ext_vcpucontext = 1;
            }
            
            /* Any remaining bytes of this chunk: read and discard. */
            while ( chunk_bytes )
            {
                unsigned long sz = MIN(chunk_bytes, sizeof(xen_pfn_t));
                if ( read_exact(io_fd, &p2m_fl_zero, sz) )
                {
                    ERROR("read-and-discard extended-info chunk bytes failed");
                    return NULL;
                }
                chunk_bytes -= sz;
                tot_bytes   -= sz;
            }
        }

        /* Now read the real first entry of P2M list. */
        if ( read_exact(io_fd, &p2m_fl_zero, sizeof(xen_pfn_t)) )
        {
            ERROR("read first entry of p2m_frame_list failed");
            return NULL;
        }
    }

    /* Now that we know the guest's word-size, can safely allocate 
     * the p2m frame list */
    if ( (p2m_frame_list = malloc(P2M_TOOLS_FL_SIZE)) == NULL )
    {
        ERROR("Couldn't allocate p2m_frame_list array");
        return NULL;
    }

    /* First entry has already been read. */
    p2m_frame_list[0] = p2m_fl_zero;
    if ( read_exact(io_fd, &p2m_frame_list[1], 
                    (P2M_FL_ENTRIES - 1) * sizeof(xen_pfn_t)) )
    {
        ERROR("read p2m_frame_list failed");
        return NULL;
    }
    
    return p2m_frame_list;
}

int xc_domain_restore(int xc_handle, int io_fd, uint32_t dom,
                      unsigned int store_evtchn, unsigned long *store_mfn,
                      unsigned int console_evtchn, unsigned long *console_mfn,
                      unsigned int hvm, unsigned int pae)
{
    DECLARE_DOMCTL;
    int rc = 1, frc, i, j, n, m, pae_extended_cr3 = 0, ext_vcpucontext = 0;
    unsigned long mfn, pfn;
    unsigned int prev_pc, this_pc;
    int verify = 0;
    int nraces = 0;

    /* The new domain's shared-info frame number. */
    unsigned long shared_info_frame;
    unsigned char shared_info_page[PAGE_SIZE]; /* saved contents from file */
    shared_info_either_t *old_shared_info = 
        (shared_info_either_t *)shared_info_page;
    shared_info_either_t *new_shared_info;

    /* A copy of the CPU context of the guest. */
    vcpu_guest_context_either_t ctxt;

    /* A table containing the type of each PFN (/not/ MFN!). */
    unsigned long *pfn_type = NULL;

    /* A table of MFNs to map in the current region */
    xen_pfn_t *region_mfn = NULL;

    /* Types of the pfns in the current region */
    unsigned long region_pfn_type[MAX_BATCH_SIZE];

    /* A copy of the pfn-to-mfn table frame list. */
    xen_pfn_t *p2m_frame_list = NULL;
    
    /* A temporary mapping of the guest's start_info page. */
    start_info_either_t *start_info;

    /* Our mapping of the current region (batch) */
    char *region_base;

    struct xc_mmu *mmu = NULL;

    /* used by debug verify code */
    unsigned long buf[PAGE_SIZE/sizeof(unsigned long)];

    struct mmuext_op pin[MAX_PIN_BATCH];
    unsigned int nr_pins;

    uint64_t vcpumap = 1ULL;
    unsigned int max_vcpu_id = 0;
    int new_ctxt_format = 0;

    /* Magic frames in HVM guests: ioreqs and xenstore comms. */
    uint64_t magic_pfns[3]; /* ioreq_pfn, bufioreq_pfn, store_pfn */

    /* Buffer for holding HVM context */
    uint8_t *hvm_buf = NULL;

    /* For info only */
    nr_pfns = 0;

    if ( read_exact(io_fd, &p2m_size, sizeof(unsigned long)) )
    {
        ERROR("read: p2m_size");
        goto out;
    }
    DPRINTF("xc_domain_restore start: p2m_size = %lx\n", p2m_size);

    if ( !get_platform_info(xc_handle, dom,
                            &max_mfn, &hvirt_start, &pt_levels, &guest_width) )
    {
        ERROR("Unable to get platform info.");
        return 1;
    }
    
    /* The *current* word size of the guest isn't very interesting; for now
     * assume the guest will be the same as we are.  We'll fix that later
     * if we discover otherwise. */
    guest_width = sizeof(unsigned long);
    pt_levels = (guest_width == 8) ? 4 : (pt_levels == 2) ? 2 : 3; 
    
    if ( !hvm ) 
    {
        /* Load the p2m frame list, plus potential extended info chunk */
        p2m_frame_list = load_p2m_frame_list(
            io_fd, &pae_extended_cr3, &ext_vcpucontext);
        if ( !p2m_frame_list )
            goto out;

        /* Now that we know the word size, tell Xen about it */
        memset(&domctl, 0, sizeof(domctl));
        domctl.domain = dom;
        domctl.cmd    = XEN_DOMCTL_set_address_size;
        domctl.u.address_size.size = guest_width * 8;
        frc = do_domctl(xc_handle, &domctl);
        if ( frc != 0 )
        {
            ERROR("Unable to set guest address size.");
            goto out;
        }
    }

    /* We want zeroed memory so use calloc rather than malloc. */
    p2m        = calloc(p2m_size, sizeof(xen_pfn_t));
    pfn_type   = calloc(p2m_size, sizeof(unsigned long));

    region_mfn = xg_memalign(PAGE_SIZE, ROUNDUP(
                              MAX_BATCH_SIZE * sizeof(xen_pfn_t), PAGE_SHIFT));
    p2m_batch  = xg_memalign(PAGE_SIZE, ROUNDUP(
                              MAX_BATCH_SIZE * sizeof(xen_pfn_t), PAGE_SHIFT));

    if ( (p2m == NULL) || (pfn_type == NULL) ||
         (region_mfn == NULL) || (p2m_batch == NULL) )
    {
        ERROR("memory alloc failed");
        errno = ENOMEM;
        goto out;
    }

    memset(region_mfn, 0,
           ROUNDUP(MAX_BATCH_SIZE * sizeof(xen_pfn_t), PAGE_SHIFT)); 
    memset(p2m_batch, 0,
           ROUNDUP(MAX_BATCH_SIZE * sizeof(xen_pfn_t), PAGE_SHIFT)); 

    if ( lock_pages(region_mfn, sizeof(xen_pfn_t) * MAX_BATCH_SIZE) )
    {
        ERROR("Could not lock region_mfn");
        goto out;
    }

    if ( lock_pages(p2m_batch, sizeof(xen_pfn_t) * MAX_BATCH_SIZE) )
    {
        ERROR("Could not lock p2m_batch");
        goto out;
    }

    /* Get the domain's shared-info frame. */
    domctl.cmd = XEN_DOMCTL_getdomaininfo;
    domctl.domain = (domid_t)dom;
    if ( xc_domctl(xc_handle, &domctl) < 0 )
    {
        ERROR("Could not get information on new domain");
        goto out;
    }
    shared_info_frame = domctl.u.getdomaininfo.shared_info_frame;

    /* Mark all PFNs as invalid; we allocate on demand */
    for ( pfn = 0; pfn < p2m_size; pfn++ )
        p2m[pfn] = INVALID_P2M_ENTRY;

    mmu = xc_alloc_mmu_updates(xc_handle, dom);
    if ( mmu == NULL )
    {
        ERROR("Could not initialise for MMU updates");
        goto out;
    }

    DPRINTF("Reloading memory pages:   0%%\n");

    /*
     * Now simply read each saved frame into its new machine frame.
     * We uncanonicalise page tables as we go.
     */
    prev_pc = 0;

    n = m = 0;
    for ( ; ; )
    {
        int j, nr_mfns = 0; 

        this_pc = (n * 100) / p2m_size;
        if ( (this_pc - prev_pc) >= 5 )
        {
            PPRINTF("\b\b\b\b%3d%%", this_pc);
            prev_pc = this_pc;
        }

        if ( read_exact(io_fd, &j, sizeof(int)) )
        {
            ERROR("Error when reading batch size");
            goto out;
        }

        PPRINTF("batch %d\n",j);

        if ( j == -1 )
        {
            verify = 1;
            DPRINTF("Entering page verify mode\n");
            continue;
        }

        if ( j == -2 )
        {
            new_ctxt_format = 1;
            if ( read_exact(io_fd, &max_vcpu_id, sizeof(int)) ||
                 (max_vcpu_id >= 64) ||
                 read_exact(io_fd, &vcpumap, sizeof(uint64_t)) )
            {
                ERROR("Error when reading max_vcpu_id");
                goto out;
            }
            continue;
        }

        if ( j == 0 )
            break;  /* our work here is done */

        if ( (j > MAX_BATCH_SIZE) || (j < 0) )
        {
            ERROR("Max batch size exceeded. Giving up.");
            goto out;
        }

        if ( read_exact(io_fd, region_pfn_type, j*sizeof(unsigned long)) )
        {
            ERROR("Error when reading region pfn types");
            goto out;
        }

        /* First pass for this batch: work out how much memory to alloc */
        nr_mfns = 0; 
        for ( i = 0; i < j; i++ )
        {
            unsigned long pfn, pagetype;
            pfn      = region_pfn_type[i] & ~XEN_DOMCTL_PFINFO_LTAB_MASK;
            pagetype = region_pfn_type[i] &  XEN_DOMCTL_PFINFO_LTAB_MASK;

            if ( (pagetype != XEN_DOMCTL_PFINFO_XTAB) && 
                 (p2m[pfn] == INVALID_P2M_ENTRY) )
            {
                /* Have a live PFN which hasn't had an MFN allocated */
                p2m_batch[nr_mfns++] = pfn; 
                p2m[pfn]--;
            }
        } 

        /* Now allocate a bunch of mfns for this batch */
        if ( nr_mfns &&
             (xc_domain_memory_populate_physmap(xc_handle, dom, nr_mfns, 0,
                                                0, p2m_batch) != 0) )
        { 
            ERROR("Failed to allocate memory for batch.!\n"); 
            errno = ENOMEM;
            goto out;
        }

        /* Second pass for this batch: update p2m[] and region_mfn[] */
        nr_mfns = 0; 
        for ( i = 0; i < j; i++ )
        {
            unsigned long pfn, pagetype;
            pfn      = region_pfn_type[i] & ~XEN_DOMCTL_PFINFO_LTAB_MASK;
            pagetype = region_pfn_type[i] &  XEN_DOMCTL_PFINFO_LTAB_MASK;

            if ( pagetype == XEN_DOMCTL_PFINFO_XTAB )
                region_mfn[i] = ~0UL; /* map will fail but we don't care */
            else 
            {
                if ( p2m[pfn] == (INVALID_P2M_ENTRY-1) )
                {
                    /* We just allocated a new mfn above; update p2m */
                    p2m[pfn] = p2m_batch[nr_mfns++]; 
                    nr_pfns++; 
                }

                /* setup region_mfn[] for batch map.
                 * For HVM guests, this interface takes PFNs, not MFNs */
                region_mfn[i] = hvm ? pfn : p2m[pfn]; 
            }
        } 

        /* Map relevant mfns */
        region_base = xc_map_foreign_batch(
            xc_handle, dom, PROT_WRITE, region_mfn, j);

        if ( region_base == NULL )
        {
            ERROR("map batch failed");
            goto out;
        }

        for ( i = 0; i < j; i++ )
        {
            void *page;
            unsigned long pagetype;

            pfn      = region_pfn_type[i] & ~XEN_DOMCTL_PFINFO_LTAB_MASK;
            pagetype = region_pfn_type[i] &  XEN_DOMCTL_PFINFO_LTAB_MASK;

            if ( pagetype == XEN_DOMCTL_PFINFO_XTAB )
                /* a bogus/unmapped page: skip it */
                continue;

            if ( pfn > p2m_size )
            {
                ERROR("pfn out of range");
                goto out;
            }

            pfn_type[pfn] = pagetype;

            mfn = p2m[pfn];

            /* In verify mode, we use a copy; otherwise we work in place */
            page = verify ? (void *)buf : (region_base + i*PAGE_SIZE);

            if ( read_exact(io_fd, page, PAGE_SIZE) )
            {
                ERROR("Error when reading page (type was %lx)", pagetype);
                goto out;
            }

            pagetype &= XEN_DOMCTL_PFINFO_LTABTYPE_MASK;

            if ( (pagetype >= XEN_DOMCTL_PFINFO_L1TAB) && 
                 (pagetype <= XEN_DOMCTL_PFINFO_L4TAB) )
            {
                /*
                ** A page table page - need to 'uncanonicalize' it, i.e.
                ** replace all the references to pfns with the corresponding
                ** mfns for the new domain.
                **
                ** On PAE we need to ensure that PGDs are in MFNs < 4G, and
                ** so we may need to update the p2m after the main loop.
                ** Hence we defer canonicalization of L1s until then.
                */
                if ((pt_levels != 3) ||
                    pae_extended_cr3 ||
                    (pagetype != XEN_DOMCTL_PFINFO_L1TAB)) {

                    if (!uncanonicalize_pagetable(xc_handle, dom, 
                                                  pagetype, page)) {
                        /*
                        ** Failing to uncanonicalize a page table can be ok
                        ** under live migration since the pages type may have
                        ** changed by now (and we'll get an update later).
                        */
                        DPRINTF("PT L%ld race on pfn=%08lx mfn=%08lx\n",
                                pagetype >> 28, pfn, mfn);
                        nraces++;
                        continue;
                    } 
                }
            }
            else if ( pagetype != XEN_DOMCTL_PFINFO_NOTAB )
            {
                ERROR("Bogus page type %lx page table is out of range: "
                    "i=%d p2m_size=%lu", pagetype, i, p2m_size);
                goto out;

            }

            if ( verify )
            {
                int res = memcmp(buf, (region_base + i*PAGE_SIZE), PAGE_SIZE);
                if ( res )
                {
                    int v;

                    DPRINTF("************** pfn=%lx type=%lx gotcs=%08lx "
                            "actualcs=%08lx\n", pfn, pfn_type[pfn],
                            csum_page(region_base + i*PAGE_SIZE),
                            csum_page(buf));

                    for ( v = 0; v < 4; v++ )
                    {
                        unsigned long *p = (unsigned long *)
                            (region_base + i*PAGE_SIZE);
                        if ( buf[v] != p[v] )
                            DPRINTF("    %d: %08lx %08lx\n", v, buf[v], p[v]);
                    }
                }
            }

            if ( !hvm &&
                 xc_add_mmu_update(xc_handle, mmu,
                                   (((unsigned long long)mfn) << PAGE_SHIFT)
                                   | MMU_MACHPHYS_UPDATE, pfn) )
            {
                ERROR("failed machpys update mfn=%lx pfn=%lx", mfn, pfn);
                goto out;
            }
        } /* end of 'batch' for loop */

        munmap(region_base, j*PAGE_SIZE);
        n+= j; /* crude stats */

        /* 
         * Discard cache for portion of file read so far up to last
         *  page boundary every 16MB or so.
         */
        m += j;
        if ( m > MAX_PAGECACHE_USAGE )
        {
            discard_file_cache(io_fd, 0 /* no flush */);
            m = 0;
        }
    }

    /*
     * Ensure we flush all machphys updates before potential PAE-specific
     * reallocations below.
     */
    if ( !hvm && xc_flush_mmu_updates(xc_handle, mmu) )
    {
        ERROR("Error doing flush_mmu_updates()");
        goto out;
    }

    DPRINTF("Received all pages (%d races)\n", nraces);

    if ( hvm ) 
    {
        uint32_t rec_len;

        /* Set HVM-specific parameters */
        if ( read_exact(io_fd, magic_pfns, sizeof(magic_pfns)) )
        {
            ERROR("error reading magic page addresses");
            goto out;
        }
        
        /* These comms pages need to be zeroed at the start of day */
        if ( xc_clear_domain_page(xc_handle, dom, magic_pfns[0]) ||
             xc_clear_domain_page(xc_handle, dom, magic_pfns[1]) ||
             xc_clear_domain_page(xc_handle, dom, magic_pfns[2]) )
        {
            ERROR("error zeroing magic pages");
            goto out;
        }
                
        if ( (frc = xc_set_hvm_param(xc_handle, dom, 
                                     HVM_PARAM_IOREQ_PFN, magic_pfns[0]))
             || (frc = xc_set_hvm_param(xc_handle, dom, 
                                        HVM_PARAM_BUFIOREQ_PFN, magic_pfns[1]))
             || (frc = xc_set_hvm_param(xc_handle, dom, 
                                        HVM_PARAM_STORE_PFN, magic_pfns[2]))
             || (frc = xc_set_hvm_param(xc_handle, dom, 
                                        HVM_PARAM_PAE_ENABLED, pae))
             || (frc = xc_set_hvm_param(xc_handle, dom, 
                                        HVM_PARAM_STORE_EVTCHN,
                                        store_evtchn)) )
        {
            ERROR("error setting HVM params: %i", frc);
            goto out;
        }
        *store_mfn = magic_pfns[2];

        /* Read HVM context */
        if ( read_exact(io_fd, &rec_len, sizeof(uint32_t)) )
        {
            ERROR("error read hvm context size!\n");
            goto out;
        }
        
        hvm_buf = malloc(rec_len);
        if ( hvm_buf == NULL )
        {
            ERROR("memory alloc for hvm context buffer failed");
            errno = ENOMEM;
            goto out;
        }
        
        if ( read_exact(io_fd, hvm_buf, rec_len) )
        {
            ERROR("error loading the HVM context");
            goto out;
        }
        
        frc = xc_domain_hvm_setcontext(xc_handle, dom, hvm_buf, rec_len);
        if ( frc )
        {
            ERROR("error setting the HVM context");
            goto out;
        }

        /* HVM success! */
        rc = 0;
        goto out;
    }

    /* Non-HVM guests only from here on */

    if ( (pt_levels == 3) && !pae_extended_cr3 )
    {
        /*
        ** XXX SMH on PAE we need to ensure PGDs are in MFNs < 4G. This
        ** is a little awkward and involves (a) finding all such PGDs and
        ** replacing them with 'lowmem' versions; (b) upating the p2m[]
        ** with the new info; and (c) canonicalizing all the L1s using the
        ** (potentially updated) p2m[].
        **
        ** This is relatively slow (and currently involves two passes through
        ** the pfn_type[] array), but at least seems to be correct. May wish
        ** to consider more complex approaches to optimize this later.
        */

        int j, k;
        
        /* First pass: find all L3TABs current in > 4G mfns and get new mfns */
        for ( i = 0; i < p2m_size; i++ )
        {
            if ( ((pfn_type[i] & XEN_DOMCTL_PFINFO_LTABTYPE_MASK) ==
                  XEN_DOMCTL_PFINFO_L3TAB) &&
                 (p2m[i] > 0xfffffUL) )
            {
                unsigned long new_mfn;
                uint64_t l3ptes[4];
                uint64_t *l3tab;

                l3tab = (uint64_t *)
                    xc_map_foreign_range(xc_handle, dom, PAGE_SIZE,
                                         PROT_READ, p2m[i]);

                for ( j = 0; j < 4; j++ )
                    l3ptes[j] = l3tab[j];

                munmap(l3tab, PAGE_SIZE);

                new_mfn = xc_make_page_below_4G(xc_handle, dom, p2m[i]);
                if ( !new_mfn )
                {
                    ERROR("Couldn't get a page below 4GB :-(");
                    goto out;
                }

                p2m[i] = new_mfn;
                if ( xc_add_mmu_update(xc_handle, mmu,
                                       (((unsigned long long)new_mfn)
                                        << PAGE_SHIFT) |
                                       MMU_MACHPHYS_UPDATE, i) )
                {
                    ERROR("Couldn't m2p on PAE root pgdir");
                    goto out;
                }

                l3tab = (uint64_t *)
                    xc_map_foreign_range(xc_handle, dom, PAGE_SIZE,
                                         PROT_READ | PROT_WRITE, p2m[i]);

                for ( j = 0; j < 4; j++ )
                    l3tab[j] = l3ptes[j];

                munmap(l3tab, PAGE_SIZE);
            }
        }

        /* Second pass: find all L1TABs and uncanonicalize them */
        j = 0;

        for ( i = 0; i < p2m_size; i++ )
        {
            if ( ((pfn_type[i] & XEN_DOMCTL_PFINFO_LTABTYPE_MASK) ==
                  XEN_DOMCTL_PFINFO_L1TAB) )
            {
                region_mfn[j] = p2m[i];
                j++;
            }

            if ( (i == (p2m_size-1)) || (j == MAX_BATCH_SIZE) )
            {
                region_base = xc_map_foreign_batch(
                    xc_handle, dom, PROT_READ | PROT_WRITE, region_mfn, j);
                if ( region_base == NULL )
                {
                    ERROR("map batch failed");
                    goto out;
                }

                for ( k = 0; k < j; k++ )
                {
                    if ( !uncanonicalize_pagetable(
                        xc_handle, dom, XEN_DOMCTL_PFINFO_L1TAB,
                        region_base + k*PAGE_SIZE) )
                    {
                        ERROR("failed uncanonicalize pt!");
                        goto out;
                    }
                }

                munmap(region_base, j*PAGE_SIZE);
                j = 0;
            }
        }

        if ( xc_flush_mmu_updates(xc_handle, mmu) )
        {
            ERROR("Error doing xc_flush_mmu_updates()");
            goto out;
        }
    }

    /*
     * Pin page tables. Do this after writing to them as otherwise Xen
     * will barf when doing the type-checking.
     */
    nr_pins = 0;
    for ( i = 0; i < p2m_size; i++ )
    {
        if ( (pfn_type[i] & XEN_DOMCTL_PFINFO_LPINTAB) == 0 )
            continue;

        switch ( pfn_type[i] & XEN_DOMCTL_PFINFO_LTABTYPE_MASK )
        {
        case XEN_DOMCTL_PFINFO_L1TAB:
            pin[nr_pins].cmd = MMUEXT_PIN_L1_TABLE;
            break;

        case XEN_DOMCTL_PFINFO_L2TAB:
            pin[nr_pins].cmd = MMUEXT_PIN_L2_TABLE;
            break;

        case XEN_DOMCTL_PFINFO_L3TAB:
            pin[nr_pins].cmd = MMUEXT_PIN_L3_TABLE;
            break;

        case XEN_DOMCTL_PFINFO_L4TAB:
            pin[nr_pins].cmd = MMUEXT_PIN_L4_TABLE;
            break;

        default:
            continue;
        }

        pin[nr_pins].arg1.mfn = p2m[i];
        nr_pins++;

        /* Batch full? Then flush. */
        if ( nr_pins == MAX_PIN_BATCH )
        {
            if ( xc_mmuext_op(xc_handle, pin, nr_pins, dom) < 0 )
            {
                ERROR("Failed to pin batch of %d page tables", nr_pins);
                goto out;
            }
            nr_pins = 0;
        }
    }

    /* Flush final partial batch. */
    if ( (nr_pins != 0) && (xc_mmuext_op(xc_handle, pin, nr_pins, dom) < 0) )
    {
        ERROR("Failed to pin batch of %d page tables", nr_pins);
        goto out;
    }

    DPRINTF("\b\b\b\b100%%\n");
    DPRINTF("Memory reloaded (%ld pages)\n", nr_pfns);

    /* Get the list of PFNs that are not in the psuedo-phys map */
    {
        unsigned int count = 0;
        unsigned long *pfntab;
        int nr_frees;

        if ( read_exact(io_fd, &count, sizeof(count)) ||
             (count > (1U << 28)) ) /* up to 1TB of address space */
        {
            ERROR("Error when reading pfn count (= %u)", count);
            goto out;
        }

        if ( !(pfntab = malloc(sizeof(unsigned long) * count)) )
        {
            ERROR("Out of memory");
            goto out;
        }

        if ( read_exact(io_fd, pfntab, sizeof(unsigned long)*count) )
        {
            ERROR("Error when reading pfntab");
            goto out;
        }

        nr_frees = 0; 
        for ( i = 0; i < count; i++ )
        {
            unsigned long pfn = pfntab[i];

            if ( p2m[pfn] != INVALID_P2M_ENTRY )
            {
                /* pfn is not in physmap now, but was at some point during 
                   the save/migration process - need to free it */
                pfntab[nr_frees++] = p2m[pfn];
                p2m[pfn]  = INVALID_P2M_ENTRY; /* not in pseudo-physical map */
            }
        }

        if ( nr_frees > 0 )
        {
            struct xen_memory_reservation reservation = {
                .nr_extents   = nr_frees,
                .extent_order = 0,
                .domid        = dom
            };
            set_xen_guest_handle(reservation.extent_start, pfntab);

            if ( (frc = xc_memory_op(xc_handle, XENMEM_decrease_reservation,
                                     &reservation)) != nr_frees )
            {
                ERROR("Could not decrease reservation : %d", frc);
                goto out;
            }
            else
                DPRINTF("Decreased reservation by %d pages\n", count);
        }
    }

    if ( lock_pages(&ctxt, sizeof(ctxt)) )
    {
        ERROR("Unable to lock ctxt");
        return 1;
    }

    for ( i = 0; i <= max_vcpu_id; i++ )
    {
        if ( !(vcpumap & (1ULL << i)) )
            continue;

        if ( read_exact(io_fd, &ctxt, ((guest_width == 8)
                                       ? sizeof(ctxt.x64)
                                       : sizeof(ctxt.x32))) )
        {
            ERROR("Error when reading ctxt %d", i);
            goto out;
        }

        if ( !new_ctxt_format )
            SET_FIELD(&ctxt, flags, GET_FIELD(&ctxt, flags) | VGCF_online);

        if ( i == 0 )
        {
            /*
             * Uncanonicalise the suspend-record frame number and poke
             * resume record.
             */
            pfn = GET_FIELD(&ctxt, user_regs.edx);
            if ( (pfn >= p2m_size) ||
                 (pfn_type[pfn] != XEN_DOMCTL_PFINFO_NOTAB) )
            {
                ERROR("Suspend record frame number is bad");
                goto out;
            }
            mfn = p2m[pfn];
            SET_FIELD(&ctxt, user_regs.edx, mfn);
            start_info = xc_map_foreign_range(
                xc_handle, dom, PAGE_SIZE, PROT_READ | PROT_WRITE, mfn);
            SET_FIELD(start_info, nr_pages, p2m_size);
            SET_FIELD(start_info, shared_info, shared_info_frame<<PAGE_SHIFT);
            SET_FIELD(start_info, flags, 0);
            *store_mfn = p2m[GET_FIELD(start_info, store_mfn)];
            SET_FIELD(start_info, store_mfn, *store_mfn);
            SET_FIELD(start_info, store_evtchn, store_evtchn);
            *console_mfn = p2m[GET_FIELD(start_info, console.domU.mfn)];
            SET_FIELD(start_info, console.domU.mfn, *console_mfn);
            SET_FIELD(start_info, console.domU.evtchn, console_evtchn);
            munmap(start_info, PAGE_SIZE);
        }
        /* Uncanonicalise each GDT frame number. */
        if ( GET_FIELD(&ctxt, gdt_ents) > 8192 )
        {
            ERROR("GDT entry count out of range");
            goto out;
        }

        for ( j = 0; (512*j) < GET_FIELD(&ctxt, gdt_ents); j++ )
        {
            pfn = GET_FIELD(&ctxt, gdt_frames[j]);
            if ( (pfn >= p2m_size) ||
                 (pfn_type[pfn] != XEN_DOMCTL_PFINFO_NOTAB) )
            {
                ERROR("GDT frame number %i (0x%lx) is bad", 
                      j, (unsigned long)pfn);
                goto out;
            }
            SET_FIELD(&ctxt, gdt_frames[j], p2m[pfn]);
        }
        /* Uncanonicalise the page table base pointer. */
        pfn = UNFOLD_CR3(GET_FIELD(&ctxt, ctrlreg[3]));

        if ( pfn >= p2m_size )
        {
            ERROR("PT base is bad: pfn=%lu p2m_size=%lu type=%08lx",
                  pfn, p2m_size, pfn_type[pfn]);
            goto out;
        }

        if ( (pfn_type[pfn] & XEN_DOMCTL_PFINFO_LTABTYPE_MASK) !=
             ((unsigned long)pt_levels<<XEN_DOMCTL_PFINFO_LTAB_SHIFT) )
        {
            ERROR("PT base is bad. pfn=%lu nr=%lu type=%08lx %08lx",
                  pfn, p2m_size, pfn_type[pfn],
                  (unsigned long)pt_levels<<XEN_DOMCTL_PFINFO_LTAB_SHIFT);
            goto out;
        }
        SET_FIELD(&ctxt, ctrlreg[3], FOLD_CR3(p2m[pfn]));

        /* Guest pagetable (x86/64) stored in otherwise-unused CR1. */
        if ( (pt_levels == 4) && (ctxt.x64.ctrlreg[1] & 1) )
        {
            pfn = UNFOLD_CR3(ctxt.x64.ctrlreg[1] & ~1);
            if ( pfn >= p2m_size )
            {
                ERROR("User PT base is bad: pfn=%lu p2m_size=%lu",
                      pfn, p2m_size);
                goto out;
            }
            if ( (pfn_type[pfn] & XEN_DOMCTL_PFINFO_LTABTYPE_MASK) !=
                 ((unsigned long)pt_levels<<XEN_DOMCTL_PFINFO_LTAB_SHIFT) )
            {
                ERROR("User PT base is bad. pfn=%lu nr=%lu type=%08lx %08lx",
                      pfn, p2m_size, pfn_type[pfn],
                      (unsigned long)pt_levels<<XEN_DOMCTL_PFINFO_LTAB_SHIFT);
                goto out;
            }
            ctxt.x64.ctrlreg[1] = FOLD_CR3(p2m[pfn]);
        }
        domctl.cmd = XEN_DOMCTL_setvcpucontext;
        domctl.domain = (domid_t)dom;
        domctl.u.vcpucontext.vcpu = i;
        set_xen_guest_handle(domctl.u.vcpucontext.ctxt, &ctxt.c);
        frc = xc_domctl(xc_handle, &domctl);
        if ( frc != 0 )
        {
            ERROR("Couldn't build vcpu%d", i);
            goto out;
        }

        if ( !ext_vcpucontext )
            continue;
        if ( read_exact(io_fd, &domctl.u.ext_vcpucontext, 128) ||
             (domctl.u.ext_vcpucontext.vcpu != i) )
        {
            ERROR("Error when reading extended ctxt %d", i);
            goto out;
        }
        domctl.cmd = XEN_DOMCTL_set_ext_vcpucontext;
        domctl.domain = dom;
        frc = xc_domctl(xc_handle, &domctl);
        if ( frc != 0 )
        {
            ERROR("Couldn't set extended vcpu%d info\n", i);
            goto out;
        }
    }

    if ( read_exact(io_fd, shared_info_page, PAGE_SIZE) )
    {
        ERROR("Error when reading shared info page");
        goto out;
    }

    /* Restore contents of shared-info page. No checking needed. */
    new_shared_info = xc_map_foreign_range(
        xc_handle, dom, PAGE_SIZE, PROT_WRITE, shared_info_frame);

    /* restore saved vcpu_info and arch specific info */
    MEMCPY_FIELD(new_shared_info, old_shared_info, vcpu_info);
    MEMCPY_FIELD(new_shared_info, old_shared_info, arch);

    /* clear any pending events and the selector */
    MEMSET_ARRAY_FIELD(new_shared_info, evtchn_pending, 0);
    for ( i = 0; i < MAX_VIRT_CPUS; i++ )
	    SET_FIELD(new_shared_info, vcpu_info[i].evtchn_pending_sel, 0);

    /* mask event channels */
    MEMSET_ARRAY_FIELD(new_shared_info, evtchn_mask, 0xff);

    /* leave wallclock time. set by hypervisor */
    munmap(new_shared_info, PAGE_SIZE);

    /* Uncanonicalise the pfn-to-mfn table frame-number list. */
    for ( i = 0; i < P2M_FL_ENTRIES; i++ )
    {
        pfn = p2m_frame_list[i];
        if ( (pfn >= p2m_size) || (pfn_type[pfn] != XEN_DOMCTL_PFINFO_NOTAB) )
        {
            ERROR("PFN-to-MFN frame number %i (%#lx) is bad", i, pfn);
            goto out;
        }
        p2m_frame_list[i] = p2m[pfn];
    }

    /* Copy the P2M we've constructed to the 'live' P2M */
    if ( !(live_p2m = xc_map_foreign_batch(xc_handle, dom, PROT_WRITE,
                                           p2m_frame_list, P2M_FL_ENTRIES)) )
    {
        ERROR("Couldn't map p2m table");
        goto out;
    }

    /* If the domain we're restoring has a different word size to ours,
     * we need to adjust the live_p2m assignment appropriately */
    if ( guest_width > sizeof (xen_pfn_t) )
        for ( i = p2m_size - 1; i >= 0; i-- )
            ((uint64_t *)live_p2m)[i] = p2m[i];
    else if ( guest_width < sizeof (xen_pfn_t) )
        for ( i = 0; i < p2m_size; i++ )   
            ((uint32_t *)live_p2m)[i] = p2m[i];
    else
        memcpy(live_p2m, p2m, p2m_size * sizeof(xen_pfn_t));
    munmap(live_p2m, P2M_FL_ENTRIES * PAGE_SIZE);

    DPRINTF("Domain ready to be built.\n");
    rc = 0;

 out:
    if ( (rc != 0) && (dom != 0) )
        xc_domain_destroy(xc_handle, dom);
    free(mmu);
    free(p2m);
    free(pfn_type);
    free(hvm_buf);

    /* discard cache for save file  */
    discard_file_cache(io_fd, 1 /*flush*/);

    DPRINTF("Restore exit with rc=%d\n", rc);
    
    return rc;
}
