/******************************************************************************
 * xc_hvm_build.c
 */

#include <stddef.h>
#include <inttypes.h>
#include <stdlib.h>
#include <unistd.h>
#include <zlib.h>

#include "xg_private.h"
#include "xc_private.h"

#include <xen/foreign/x86_32.h>
#include <xen/foreign/x86_64.h>
#include <xen/hvm/hvm_info_table.h>
#include <xen/hvm/params.h>
#include "xc_e820.h"

#include <xen/libelf.h>

#define SCRATCH_PFN 0xFFFFF

static void build_e820map(void *e820_page, unsigned long long mem_size)
{
    struct e820entry *e820entry =
        (struct e820entry *)(((unsigned char *)e820_page) + HVM_E820_OFFSET);
    unsigned long long extra_mem_size = 0;
    unsigned char nr_map = 0;

    /*
     * Physical address space from HVM_BELOW_4G_RAM_END to 4G is reserved
     * for PCI devices MMIO. So if HVM has more than HVM_BELOW_4G_RAM_END
     * RAM, memory beyond HVM_BELOW_4G_RAM_END will go to 4G above.
     */
    if ( mem_size > HVM_BELOW_4G_RAM_END )
    {
        extra_mem_size = mem_size - HVM_BELOW_4G_RAM_END;
        mem_size = HVM_BELOW_4G_RAM_END;
    }

    /* 0x0-0x9FC00: Ordinary RAM. */
    e820entry[nr_map].addr = 0x0;
    e820entry[nr_map].size = 0x9FC00;
    e820entry[nr_map].type = E820_RAM;
    nr_map++;

    /* 0x9FC00-0xA0000: Extended BIOS Data Area (EBDA). */
    e820entry[nr_map].addr = 0x9FC00;
    e820entry[nr_map].size = 0x400;
    e820entry[nr_map].type = E820_RESERVED;
    nr_map++;

    /*
     * Following regions are standard regions of the PC memory map.
     * They are not covered by e820 regions. OSes will not use as RAM.
     * 0xA0000-0xC0000: VGA memory-mapped I/O. Not covered by E820.
     * 0xC0000-0xE0000: 16-bit devices, expansion ROMs (inc. vgabios).
     * TODO: hvmloader should free pages which turn out to be unused.
     */

    /*
     * 0xE0000-0x0F0000: PC-specific area. We place ACPI tables here.
     *                   We *cannot* mark as E820_ACPI, for two reasons:
     *                    1. ACPI spec. says that E820_ACPI regions below
     *                       16MB must clip INT15h 0x88 and 0xe801 queries.
     *                       Our rombios doesn't do this.
     *                    2. The OS is allowed to reclaim ACPI memory after
     *                       parsing the tables. But our FACS is in this
     *                       region and it must not be reclaimed (it contains
     *                       the ACPI global lock!).
     * 0xF0000-0x100000: System BIOS.
     * TODO: hvmloader should free pages which turn out to be unused.
     */
    e820entry[nr_map].addr = 0xE0000;
    e820entry[nr_map].size = 0x20000;
    e820entry[nr_map].type = E820_RESERVED;
    nr_map++;

    /*
     * Low RAM goes here. Remove 4 pages for: ioreq, bufioreq, and xenstore.
     *  1. Guard page.
     *  2. Buffered ioreq.
     *  3. Xenstore.
     *  4. Normal ioreq.
     */
    e820entry[nr_map].addr = 0x100000;
    e820entry[nr_map].size = mem_size - 0x100000 - PAGE_SIZE * 4;
    e820entry[nr_map].type = E820_RAM;
    nr_map++;

    /* Explicitly reserve space for special pages. */
    e820entry[nr_map].addr = mem_size - PAGE_SIZE * 3;
    e820entry[nr_map].size = PAGE_SIZE * 3;
    e820entry[nr_map].type = E820_RESERVED;
    nr_map++;

    if ( extra_mem_size )
    {
        e820entry[nr_map].addr = (1ULL << 32);
        e820entry[nr_map].size = extra_mem_size;
        e820entry[nr_map].type = E820_RAM;
        nr_map++;
    }

    *(((unsigned char *)e820_page) + HVM_E820_NR_OFFSET) = nr_map;
}

static int loadelfimage(
    struct elf_binary *elf, int xch, uint32_t dom, unsigned long *parray)
{
    privcmd_mmap_entry_t *entries = NULL;
    int pages = (elf->pend - elf->pstart + PAGE_SIZE - 1) >> PAGE_SHIFT;
    int i, rc = -1;

    /* Map address space for initial elf image. */
    entries = malloc(pages * sizeof(privcmd_mmap_entry_t));
    if ( entries == NULL )
        goto err;
    elf->dest = mmap(NULL, pages << PAGE_SHIFT, PROT_READ | PROT_WRITE,
                     MAP_SHARED, xch, 0);
    if ( elf->dest == MAP_FAILED )
        goto err;

    for ( i = 0; i < pages; i++ )
    {
        entries[i].va = (uintptr_t)elf->dest + (i << PAGE_SHIFT);
        entries[i].mfn = parray[(elf->pstart >> PAGE_SHIFT) + i];
        entries[i].npages = 1;
    }

    rc = xc_map_foreign_ranges(xch, dom, entries, pages);
    if ( rc < 0 )
        goto err;

    /* Load the initial elf image. */
    elf_load_binary(elf);
    rc = 0;

 err:
    if ( elf->dest )
    {
        munmap(elf->dest, pages << PAGE_SHIFT);
        elf->dest = NULL;
    }

    if ( entries )
        free(entries);

    return rc;
}

static int setup_guest(int xc_handle,
                       uint32_t dom, int memsize,
                       char *image, unsigned long image_size)
{
    xen_pfn_t *page_array = NULL;
    unsigned long i, nr_pages = (unsigned long)memsize << (20 - PAGE_SHIFT);
    unsigned long shared_page_nr, entry_eip, cur_pages;
    struct xen_add_to_physmap xatp;
    struct shared_info *shared_info;
    void *e820_page;
    struct elf_binary elf;
    uint64_t v_start, v_end;
    int rc;
    xen_capabilities_info_t caps;

    /* An HVM guest must be initialised with at least 2MB memory. */
    if ( memsize < 2 )
        goto error_out;

    if ( elf_init(&elf, image, image_size) != 0 )
        goto error_out;
    elf_parse_binary(&elf);
    v_start = 0;
    v_end = (unsigned long long)memsize << 20;

    if ( xc_version(xc_handle, XENVER_capabilities, &caps) != 0 )
    {
        PERROR("Could not get Xen capabilities\n");
        goto error_out;
    }

    if ( (elf.pstart & (PAGE_SIZE - 1)) != 0 )
    {
        PERROR("Guest OS must load to a page boundary.\n");
        goto error_out;
    }

    IPRINTF("VIRTUAL MEMORY ARRANGEMENT:\n"
            "  Loader:        %016"PRIx64"->%016"PRIx64"\n"
            "  TOTAL:         %016"PRIx64"->%016"PRIx64"\n"
            "  ENTRY ADDRESS: %016"PRIx64"\n",
            elf.pstart, elf.pend,
            v_start, v_end,
            elf_uval(&elf, elf.ehdr, e_entry));

    if ( (page_array = malloc(nr_pages * sizeof(xen_pfn_t))) == NULL )
    {
        PERROR("Could not allocate memory.\n");
        goto error_out;
    }

    for ( i = 0; i < nr_pages; i++ )
        page_array[i] = i;
    for ( i = HVM_BELOW_4G_RAM_END >> PAGE_SHIFT; i < nr_pages; i++ )
        page_array[i] += HVM_BELOW_4G_MMIO_LENGTH >> PAGE_SHIFT;

    /*
     * Allocate memory for HVM guest, skipping VGA hole 0xA0000-0xC0000.
     * We allocate pages in batches of no more than 2048 to ensure that
     * we can be preempted and hence dom0 remains responsive.
     */
    rc = xc_domain_memory_populate_physmap(
        xc_handle, dom, 0xa0, 0, 0, &page_array[0x00]);
    cur_pages = 0xc0;
    while ( (rc == 0) && (nr_pages > cur_pages) )
    {
        unsigned long count = nr_pages - cur_pages;
        if ( count > 2048 )
            count = 2048;
        rc = xc_domain_memory_populate_physmap(
            xc_handle, dom, count, 0, 0, &page_array[cur_pages]);
        cur_pages += count;
    }
    if ( rc != 0 )
    {
        PERROR("Could not allocate memory for HVM guest.\n");
        goto error_out;
    }

    if ( loadelfimage(&elf, xc_handle, dom, page_array) != 0 )
        goto error_out;

    if ( (e820_page = xc_map_foreign_range(
              xc_handle, dom, PAGE_SIZE, PROT_READ | PROT_WRITE,
              HVM_E820_PAGE >> PAGE_SHIFT)) == NULL )
        goto error_out;
    memset(e820_page, 0, PAGE_SIZE);
    build_e820map(e820_page, v_end);
    munmap(e820_page, PAGE_SIZE);

    /* Map and initialise shared_info page. */
    xatp.domid = dom;
    xatp.space = XENMAPSPACE_shared_info;
    xatp.idx   = 0;
    xatp.gpfn  = SCRATCH_PFN;
    if ( (xc_memory_op(xc_handle, XENMEM_add_to_physmap, &xatp) != 0) ||
         ((shared_info = xc_map_foreign_range(
             xc_handle, dom, PAGE_SIZE, PROT_READ | PROT_WRITE,
             SCRATCH_PFN)) == NULL) )
        goto error_out;
    memset(shared_info, 0, PAGE_SIZE);
    /* NB. evtchn_upcall_mask is unused: leave as zero. */
    memset(&shared_info->evtchn_mask[0], 0xff,
           sizeof(shared_info->evtchn_mask));
    munmap(shared_info, PAGE_SIZE);

    if ( v_end > HVM_BELOW_4G_RAM_END )
        shared_page_nr = (HVM_BELOW_4G_RAM_END >> PAGE_SHIFT) - 1;
    else
        shared_page_nr = (v_end >> PAGE_SHIFT) - 1;

    /* Free the guard page that separates low RAM from special pages. */
    rc = xc_domain_memory_decrease_reservation(
            xc_handle, dom, 1, 0, &page_array[shared_page_nr-3]);
    if ( rc != 0 )
    {
        PERROR("Could not deallocate guard page for HVM guest.\n");
        goto error_out;
    }

    /* Paranoia: clean pages. */
    if ( xc_clear_domain_page(xc_handle, dom, shared_page_nr) ||
         xc_clear_domain_page(xc_handle, dom, shared_page_nr-1) ||
         xc_clear_domain_page(xc_handle, dom, shared_page_nr-2) )
        goto error_out;

    xc_set_hvm_param(xc_handle, dom, HVM_PARAM_STORE_PFN, shared_page_nr-1);
    xc_set_hvm_param(xc_handle, dom, HVM_PARAM_BUFIOREQ_PFN, shared_page_nr-2);
    xc_set_hvm_param(xc_handle, dom, HVM_PARAM_IOREQ_PFN, shared_page_nr);

    /* Insert JMP <rel32> instruction at address 0x0 to reach entry point. */
    entry_eip = elf_uval(&elf, elf.ehdr, e_entry);
    if ( entry_eip != 0 )
    {
        char *page0 = xc_map_foreign_range(
            xc_handle, dom, PAGE_SIZE, PROT_READ | PROT_WRITE, 0);
        if ( page0 == NULL )
            goto error_out;
        page0[0] = 0xe9;
        *(uint32_t *)&page0[1] = entry_eip - 5;
        munmap(page0, PAGE_SIZE);
    }

    free(page_array);
    return 0;

 error_out:
    free(page_array);
    return -1;
}

static int xc_hvm_build_internal(int xc_handle,
                                 uint32_t domid,
                                 int memsize,
                                 char *image,
                                 unsigned long image_size)
{
    if ( (image == NULL) || (image_size == 0) )
    {
        ERROR("Image required");
        return -1;
    }

    return setup_guest(xc_handle, domid, memsize, image, image_size);
}

static inline int is_loadable_phdr(Elf32_Phdr *phdr)
{
    return ((phdr->p_type == PT_LOAD) &&
            ((phdr->p_flags & (PF_W|PF_X)) != 0));
}

/* xc_hvm_build:
 * Create a domain for a virtualized Linux, using files/filenames.
 */
int xc_hvm_build(int xc_handle,
                 uint32_t domid,
                 int memsize,
                 const char *image_name)
{
    char *image;
    int  sts;
    unsigned long image_size;

    if ( (image_name == NULL) ||
         ((image = xc_read_image(image_name, &image_size)) == NULL) )
        return -1;

    sts = xc_hvm_build_internal(xc_handle, domid, memsize, image, image_size);

    free(image);

    return sts;
}

/* xc_hvm_build_mem:
 * Create a domain for a virtualized Linux, using memory buffers.
 */
int xc_hvm_build_mem(int xc_handle,
                     uint32_t domid,
                     int memsize,
                     const char *image_buffer,
                     unsigned long image_size)
{
    int           sts;
    unsigned long img_len;
    char         *img;

    /* Validate that there is a kernel buffer */

    if ( (image_buffer == NULL) || (image_size == 0) )
    {
        ERROR("kernel image buffer not present");
        return -1;
    }

    img = xc_inflate_buffer(image_buffer, image_size, &img_len);
    if ( img == NULL )
    {
        ERROR("unable to inflate ram disk buffer");
        return -1;
    }

    sts = xc_hvm_build_internal(xc_handle, domid, memsize,
                                img, img_len);

    /* xc_inflate_buffer may return the original buffer pointer (for
       for already inflated buffers), so exercise some care in freeing */

    if ( (img != NULL) && (img != image_buffer) )
        free(img);

    return sts;
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
