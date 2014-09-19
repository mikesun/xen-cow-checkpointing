/*
 * Copyright (c) 2006, Intel Corporation.
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
 * Copyright (C) Ashok Raj <ashok.raj@intel.com>
 * Copyright (C) Shaohua Li <shaohua.li@intel.com>
 * Copyright (C) Allen Kay <allen.m.kay@intel.com> - adapted to xen
 */

#include <xen/init.h>
#include <xen/irq.h>
#include <xen/spinlock.h>
#include <xen/sched.h>
#include <xen/xmalloc.h>
#include <xen/domain_page.h>
#include <asm/delay.h>
#include <asm/string.h>
#include <asm/mm.h>
#include <asm/iommu.h>
#include <asm/hvm/vmx/intel-iommu.h>
#include "dmar.h"
#include "pci-direct.h"
#include "pci_regs.h"
#include "msi.h"

#define domain_iommu_domid(d) ((d)->arch.hvm_domain.hvm_iommu.iommu_domid)

extern void print_iommu_regs(struct acpi_drhd_unit *drhd);
extern void print_vtd_entries(struct domain *d, int bus, int devfn,
                              unsigned long gmfn);

void pdev_flr(u8 bus, u8 devfn);

static spinlock_t domid_bitmap_lock;    /* protect domain id bitmap */
static int domid_bitmap_size;           /* domain id bitmap size in bit */
static void *domid_bitmap;              /* iommu domain id bitmap */

#define DID_FIELD_WIDTH 16
#define DID_HIGH_OFFSET 8
static void context_set_domain_id(struct context_entry *context,
                                  struct domain *d)
{
    unsigned long flags;
    domid_t iommu_domid = domain_iommu_domid(d);

    if ( iommu_domid == 0 )
    {
        spin_lock_irqsave(&domid_bitmap_lock, flags);
        iommu_domid = find_first_zero_bit(domid_bitmap, domid_bitmap_size);
        set_bit(iommu_domid, domid_bitmap);
        spin_unlock_irqrestore(&domid_bitmap_lock, flags);
        d->arch.hvm_domain.hvm_iommu.iommu_domid = iommu_domid;
    }

    context->hi &= (1 << DID_HIGH_OFFSET) - 1;
    context->hi |= iommu_domid << DID_HIGH_OFFSET;
}

static void iommu_domid_release(struct domain *d)
{
    domid_t iommu_domid = domain_iommu_domid(d);

    if ( iommu_domid != 0 )
    {
        d->arch.hvm_domain.hvm_iommu.iommu_domid = 0;
        clear_bit(iommu_domid, domid_bitmap);
    }
}

static unsigned int x86_clflush_size;
static int iommus_incoherent;
static void __iommu_flush_cache(void *addr, int size)
{
    int i;

    if ( !iommus_incoherent )
        return;

    for ( i = 0; i < size; i += x86_clflush_size )
        clflush((char*)addr + i);
}

void iommu_flush_cache_entry(void *addr)
{
    __iommu_flush_cache(addr, 8);
}

void iommu_flush_cache_page(void *addr)
{
    __iommu_flush_cache(addr, PAGE_SIZE_4K);
}

int nr_iommus;
/* context entry handling */
static struct context_entry * device_to_context_entry(struct iommu *iommu,
                                                      u8 bus, u8 devfn)
{
    struct root_entry *root;
    struct context_entry *context;
    unsigned long phy_addr;
    unsigned long flags;

    spin_lock_irqsave(&iommu->lock, flags);
    root = &iommu->root_entry[bus];
    if ( !root_present(*root) )
    {
        phy_addr = (unsigned long) alloc_xenheap_page();
        if ( !phy_addr )
        {
            spin_unlock_irqrestore(&iommu->lock, flags);
            return NULL;
        }
        memset((void *) phy_addr, 0, PAGE_SIZE);
        iommu_flush_cache_page((void *)phy_addr);
        phy_addr = virt_to_maddr((void *)phy_addr);
        set_root_value(*root, phy_addr);
        set_root_present(*root);
        iommu_flush_cache_entry(root);
    }
    phy_addr = (unsigned long) get_context_addr(*root);
    context = (struct context_entry *)maddr_to_virt(phy_addr);
    spin_unlock_irqrestore(&iommu->lock, flags);
    return &context[devfn];
}

static int device_context_mapped(struct iommu *iommu, u8 bus, u8 devfn)
{
    struct root_entry *root;
    struct context_entry *context;
    unsigned long phy_addr;
    int ret;
    unsigned long flags;

    spin_lock_irqsave(&iommu->lock, flags);
    root = &iommu->root_entry[bus];
    if ( !root_present(*root) )
    {
        ret = 0;
        goto out;
    }
    phy_addr = get_context_addr(*root);
    context = (struct context_entry *)maddr_to_virt(phy_addr);
    ret = context_present(context[devfn]);
 out:
    spin_unlock_irqrestore(&iommu->lock, flags);
    return ret;
}

static struct page_info *addr_to_dma_page(struct domain *domain, u64 addr)
{
    struct hvm_iommu *hd = domain_hvm_iommu(domain);
    int addr_width = agaw_to_width(hd->agaw);
    struct dma_pte *parent, *pte = NULL, *pgd;
    int level = agaw_to_level(hd->agaw);
    int offset;
    unsigned long flags;
    struct page_info *pg = NULL;
    u64 *vaddr = NULL;

    addr &= (((u64)1) << addr_width) - 1;
    spin_lock_irqsave(&hd->mapping_lock, flags);
    if ( !hd->pgd )
    {
        pgd = (struct dma_pte *)alloc_xenheap_page();
        if ( !pgd )
        {
            spin_unlock_irqrestore(&hd->mapping_lock, flags);
            return NULL;
        }
        memset(pgd, 0, PAGE_SIZE);
        hd->pgd = pgd;
    }

    parent = hd->pgd;
    while ( level > 1 )
    {
        offset = address_level_offset(addr, level);
        pte = &parent[offset];

        if ( dma_pte_addr(*pte) == 0 )
        {
            pg = alloc_domheap_page(NULL);
            vaddr = map_domain_page(page_to_mfn(pg));
            if ( !vaddr )
            {
                spin_unlock_irqrestore(&hd->mapping_lock, flags);
                return NULL;
            }
            memset(vaddr, 0, PAGE_SIZE);
            iommu_flush_cache_page(vaddr);

            dma_set_pte_addr(*pte, page_to_maddr(pg));

            /*
             * high level table always sets r/w, last level
             * page table control read/write
             */
            dma_set_pte_readable(*pte);
            dma_set_pte_writable(*pte);
            iommu_flush_cache_entry(pte);
        }
        else
        {
            pg = maddr_to_page(pte->val);
            vaddr = map_domain_page(page_to_mfn(pg));
            if ( !vaddr )
            {
                spin_unlock_irqrestore(&hd->mapping_lock, flags);
                return NULL;
            }
        }

        if ( parent != hd->pgd )
            unmap_domain_page(parent);

        if ( level == 2 && vaddr )
        {
            unmap_domain_page(vaddr);
            break;
        }

        parent = (struct dma_pte *)vaddr;
        vaddr = NULL;
        level--;
    }

    spin_unlock_irqrestore(&hd->mapping_lock, flags);
    return pg;
}

/* return address's page at specific level */
static struct page_info *dma_addr_level_page(struct domain *domain,
                                             u64 addr, int level)
{
    struct hvm_iommu *hd = domain_hvm_iommu(domain);
    struct dma_pte *parent, *pte = NULL;
    int total = agaw_to_level(hd->agaw);
    int offset;
    struct page_info *pg = NULL;

    parent = hd->pgd;
    while ( level <= total )
    {
        offset = address_level_offset(addr, total);
        pte = &parent[offset];
        if ( dma_pte_addr(*pte) == 0 )
        {
            if ( parent != hd->pgd )
                unmap_domain_page(parent);
            break;
        }

        pg = maddr_to_page(pte->val);
        if ( parent != hd->pgd )
            unmap_domain_page(parent);

        if ( level == total )
            return pg;

        parent = map_domain_page(page_to_mfn(pg));
        total--;
    }

    return NULL;
}

static void iommu_flush_write_buffer(struct iommu *iommu)
{
    u32 val;
    unsigned long flag;
    unsigned long start_time;

    if ( !cap_rwbf(iommu->cap) )
        return;
    val = iommu->gcmd | DMA_GCMD_WBF;

    spin_lock_irqsave(&iommu->register_lock, flag);
    dmar_writel(iommu->reg, DMAR_GCMD_REG, val);

    /* Make sure hardware complete it */
    start_time = jiffies;
    for ( ; ; )
    {
        val = dmar_readl(iommu->reg, DMAR_GSTS_REG);
        if ( !(val & DMA_GSTS_WBFS) )
            break;
        if ( time_after(jiffies, start_time + DMAR_OPERATION_TIMEOUT) )
            panic("DMAR hardware is malfunctional,"
                  " please disable IOMMU\n");
        cpu_relax();
    }
    spin_unlock_irqrestore(&iommu->register_lock, flag);
}

/* return value determine if we need a write buffer flush */
static int __iommu_flush_context(
    struct iommu *iommu,
    u16 did, u16 source_id, u8 function_mask, u64 type,
    int non_present_entry_flush)
{
    u64 val = 0;
    unsigned long flag;
    unsigned long start_time;

    /*
     * In the non-present entry flush case, if hardware doesn't cache
     * non-present entry we do nothing and if hardware cache non-present
     * entry, we flush entries of domain 0 (the domain id is used to cache
     * any non-present entries)
     */
    if ( non_present_entry_flush )
    {
        if ( !cap_caching_mode(iommu->cap) )
            return 1;
        else
            did = 0;
    }

    /* use register invalidation */
    switch ( type )
    {
    case DMA_CCMD_GLOBAL_INVL:
        val = DMA_CCMD_GLOBAL_INVL;
        break;
    case DMA_CCMD_DOMAIN_INVL:
        val = DMA_CCMD_DOMAIN_INVL|DMA_CCMD_DID(did);
        break;
    case DMA_CCMD_DEVICE_INVL:
        val = DMA_CCMD_DEVICE_INVL|DMA_CCMD_DID(did)
            |DMA_CCMD_SID(source_id)|DMA_CCMD_FM(function_mask);
        break;
    default:
        BUG();
    }
    val |= DMA_CCMD_ICC;

    spin_lock_irqsave(&iommu->register_lock, flag);
    dmar_writeq(iommu->reg, DMAR_CCMD_REG, val);

    /* Make sure hardware complete it */
    start_time = jiffies;
    for ( ; ; )
    {
        val = dmar_readq(iommu->reg, DMAR_CCMD_REG);
        if ( !(val & DMA_CCMD_ICC) )
            break;
        if ( time_after(jiffies, start_time + DMAR_OPERATION_TIMEOUT) )
            panic("DMAR hardware is malfunctional, please disable IOMMU\n");
        cpu_relax();
    }
    spin_unlock_irqrestore(&iommu->register_lock, flag);
    /* flush context entry will implictly flush write buffer */
    return 0;
}

static int inline iommu_flush_context_global(
    struct iommu *iommu, int non_present_entry_flush)
{
    return __iommu_flush_context(iommu, 0, 0, 0, DMA_CCMD_GLOBAL_INVL,
                                 non_present_entry_flush);
}

static int inline iommu_flush_context_domain(
    struct iommu *iommu, u16 did, int non_present_entry_flush)
{
    return __iommu_flush_context(iommu, did, 0, 0, DMA_CCMD_DOMAIN_INVL,
                                 non_present_entry_flush);
}

static int inline iommu_flush_context_device(
    struct iommu *iommu, u16 did, u16 source_id,
    u8 function_mask, int non_present_entry_flush)
{
    return __iommu_flush_context(iommu, did, source_id, function_mask,
                                 DMA_CCMD_DEVICE_INVL,
                                 non_present_entry_flush);
}

/* return value determine if we need a write buffer flush */
static int __iommu_flush_iotlb(struct iommu *iommu, u16 did,
                               u64 addr, unsigned int size_order, u64 type,
                               int non_present_entry_flush)
{
    int tlb_offset = ecap_iotlb_offset(iommu->ecap);
    u64 val = 0, val_iva = 0;
    unsigned long flag;
    unsigned long start_time;

    /*
     * In the non-present entry flush case, if hardware doesn't cache
     * non-present entry we do nothing and if hardware cache non-present
     * entry, we flush entries of domain 0 (the domain id is used to cache
     * any non-present entries)
     */
    if ( non_present_entry_flush )
    {
        if ( !cap_caching_mode(iommu->cap) )
            return 1;
        else
            did = 0;
    }

    /* use register invalidation */
    switch ( type )
    {
    case DMA_TLB_GLOBAL_FLUSH:
        /* global flush doesn't need set IVA_REG */
        val = DMA_TLB_GLOBAL_FLUSH|DMA_TLB_IVT;
        break;
    case DMA_TLB_DSI_FLUSH:
        val = DMA_TLB_DSI_FLUSH|DMA_TLB_IVT|DMA_TLB_DID(did);
        break;
    case DMA_TLB_PSI_FLUSH:
        val = DMA_TLB_PSI_FLUSH|DMA_TLB_IVT|DMA_TLB_DID(did);
        /* Note: always flush non-leaf currently */
        val_iva = size_order | addr;
        break;
    default:
        BUG();
    }
    /* Note: set drain read/write */
    if ( cap_read_drain(iommu->cap) )
        val |= DMA_TLB_READ_DRAIN;
    if ( cap_write_drain(iommu->cap) )
        val |= DMA_TLB_WRITE_DRAIN;

    spin_lock_irqsave(&iommu->register_lock, flag);
    /* Note: Only uses first TLB reg currently */
    if ( val_iva )
        dmar_writeq(iommu->reg, tlb_offset, val_iva);
    dmar_writeq(iommu->reg, tlb_offset + 8, val);

    /* Make sure hardware complete it */
    start_time = jiffies;
    for ( ; ; )
    {
        val = dmar_readq(iommu->reg, tlb_offset + 8);
        if ( !(val & DMA_TLB_IVT) )
            break;
        if ( time_after(jiffies, start_time + DMAR_OPERATION_TIMEOUT) )
            panic("DMAR hardware is malfunctional, please disable IOMMU\n");
        cpu_relax();
    }
    spin_unlock_irqrestore(&iommu->register_lock, flag);

    /* check IOTLB invalidation granularity */
    if ( DMA_TLB_IAIG(val) == 0 )
        printk(KERN_ERR VTDPREFIX "IOMMU: flush IOTLB failed\n");
    if ( DMA_TLB_IAIG(val) != DMA_TLB_IIRG(type) )
        printk(KERN_ERR VTDPREFIX "IOMMU: tlb flush request %x, actual %x\n",
               (u32)DMA_TLB_IIRG(type), (u32)DMA_TLB_IAIG(val));
    /* flush context entry will implictly flush write buffer */
    return 0;
}

static int inline iommu_flush_iotlb_global(struct iommu *iommu,
                                           int non_present_entry_flush)
{
    return __iommu_flush_iotlb(iommu, 0, 0, 0, DMA_TLB_GLOBAL_FLUSH,
                               non_present_entry_flush);
}

static int inline iommu_flush_iotlb_dsi(struct iommu *iommu, u16 did,
                                        int non_present_entry_flush)
{
    return __iommu_flush_iotlb(iommu, did, 0, 0, DMA_TLB_DSI_FLUSH,
                               non_present_entry_flush);
}

static int inline get_alignment(u64 base, unsigned int size)
{
    int t = 0;
    u64 end;

    end = base + size - 1;
    while ( base != end )
    {
        t++;
        base >>= 1;
        end >>= 1;
    }
    return t;
}

static int inline iommu_flush_iotlb_psi(
    struct iommu *iommu, u16 did,
    u64 addr, unsigned int pages, int non_present_entry_flush)
{
    unsigned int align;

    BUG_ON(addr & (~PAGE_MASK_4K));
    BUG_ON(pages == 0);

    /* Fallback to domain selective flush if no PSI support */
    if ( !cap_pgsel_inv(iommu->cap) )
        return iommu_flush_iotlb_dsi(iommu, did,
                                     non_present_entry_flush);

    /*
     * PSI requires page size is 2 ^ x, and the base address is naturally
     * aligned to the size
     */
    align = get_alignment(addr >> PAGE_SHIFT_4K, pages);
    /* Fallback to domain selective flush if size is too big */
    if ( align > cap_max_amask_val(iommu->cap) )
        return iommu_flush_iotlb_dsi(iommu, did,
                                     non_present_entry_flush);

    addr >>= PAGE_SHIFT_4K + align;
    addr <<= PAGE_SHIFT_4K + align;

    return __iommu_flush_iotlb(iommu, did, addr, align,
                               DMA_TLB_PSI_FLUSH, non_present_entry_flush);
}

void iommu_flush_all(void)
{
    struct acpi_drhd_unit *drhd;
    struct iommu *iommu;

    wbinvd();
    for_each_drhd_unit ( drhd )
    {
        iommu = drhd->iommu;
        iommu_flush_context_global(iommu, 0);
        iommu_flush_iotlb_global(iommu, 0);
    }
}

/* clear one page's page table */
static void dma_pte_clear_one(struct domain *domain, u64 addr)
{
    struct hvm_iommu *hd = domain_hvm_iommu(domain);
    struct acpi_drhd_unit *drhd;
    struct iommu *iommu;
    struct dma_pte *pte = NULL;
    struct page_info *pg = NULL;

    /* get last level pte */
    pg = dma_addr_level_page(domain, addr, 1);
    if ( !pg )
        return;
    pte = (struct dma_pte *)map_domain_page(page_to_mfn(pg));
    pte += address_level_offset(addr, 1);
    if ( pte )
    {
        dma_clear_pte(*pte);
        iommu_flush_cache_entry(pte);

        for_each_drhd_unit ( drhd )
        {
            iommu = drhd->iommu;

            if ( !test_bit(iommu->index, &hd->iommu_bitmap) )
                continue;

            if ( cap_caching_mode(iommu->cap) )
                iommu_flush_iotlb_psi(iommu, domain_iommu_domid(domain),
                                      addr, 1, 0);
            else if (cap_rwbf(iommu->cap))
                iommu_flush_write_buffer(iommu);
        }
    }
    unmap_domain_page(pte);
}

/* clear last level pte, a tlb flush should be followed */
static void dma_pte_clear_range(struct domain *domain, u64 start, u64 end)
{
    struct hvm_iommu *hd = domain_hvm_iommu(domain);
    int addr_width = agaw_to_width(hd->agaw);

    start &= (((u64)1) << addr_width) - 1;
    end &= (((u64)1) << addr_width) - 1;
    /* in case it's partial page */
    start = PAGE_ALIGN_4K(start);
    end &= PAGE_MASK_4K;

    /* we don't need lock here, nobody else touches the iova range */
    while ( start < end )
    {
        dma_pte_clear_one(domain, start);
        start += PAGE_SIZE_4K;
    }
}

/* free page table pages. last level pte should already be cleared */
void dma_pte_free_pagetable(struct domain *domain, u64 start, u64 end)
{
    struct hvm_iommu *hd = domain_hvm_iommu(domain);
    int addr_width = agaw_to_width(hd->agaw);
    struct dma_pte *pte;
    int total = agaw_to_level(hd->agaw);
    int level;
    u64 tmp;
    struct page_info *pg = NULL;

    start &= (((u64)1) << addr_width) - 1;
    end &= (((u64)1) << addr_width) - 1;

    /* we don't need lock here, nobody else touches the iova range */
    level = 2;
    while ( level <= total )
    {
        tmp = align_to_level(start, level);
        if ( (tmp >= end) || ((tmp + level_size(level)) > end) )
            return;

        while ( tmp < end )
        {
            pg = dma_addr_level_page(domain, tmp, level);
            if ( !pg )
            {
                tmp += level_size(level);
                continue;
            }
            pte = (struct dma_pte *)map_domain_page(page_to_mfn(pg));
            pte += address_level_offset(tmp, level);
            dma_clear_pte(*pte);
            iommu_flush_cache_entry(pte);
            unmap_domain_page(pte);
            free_domheap_page(pg);

            tmp += level_size(level);
        }
        level++;
    }

    /* free pgd */
    if ( start == 0 && end == ((((u64)1) << addr_width) - 1) )
    {
        free_xenheap_page((void *)hd->pgd);
        hd->pgd = NULL;
    }
}

/* iommu handling */
static int iommu_set_root_entry(struct iommu *iommu)
{
    void *addr;
    u32 cmd, sts;
    struct root_entry *root;
    unsigned long flags;
    unsigned long start_time;

    if ( iommu == NULL )
    {
        gdprintk(XENLOG_ERR VTDPREFIX,
                 "iommu_set_root_entry: iommu == NULL\n");
        return -EINVAL;
    }

    if ( unlikely(!iommu->root_entry) )
    {
        root = (struct root_entry *)alloc_xenheap_page();
        if ( root == NULL )
            return -ENOMEM;

        memset((u8*)root, 0, PAGE_SIZE);
        iommu_flush_cache_page(root);

        if ( cmpxchg((unsigned long *)&iommu->root_entry,
                     0, (unsigned long)root) != 0 )
            free_xenheap_page((void *)root);
    }

    addr = iommu->root_entry;

    spin_lock_irqsave(&iommu->register_lock, flags);

    dmar_writeq(iommu->reg, DMAR_RTADDR_REG, virt_to_maddr(addr));
    cmd = iommu->gcmd | DMA_GCMD_SRTP;
    dmar_writel(iommu->reg, DMAR_GCMD_REG, cmd);

    /* Make sure hardware complete it */
    start_time = jiffies;
    for ( ; ; )
    {
        sts = dmar_readl(iommu->reg, DMAR_GSTS_REG);
        if ( sts & DMA_GSTS_RTPS )
            break;
        if ( time_after(jiffies, start_time + DMAR_OPERATION_TIMEOUT) )
            panic("DMAR hardware is malfunctional, please disable IOMMU\n");
        cpu_relax();
    }

    spin_unlock_irqrestore(&iommu->register_lock, flags);

    return 0;
}

static int iommu_enable_translation(struct iommu *iommu)
{
    u32 sts;
    unsigned long flags;
    unsigned long start_time;

    dprintk(XENLOG_INFO VTDPREFIX,
            "iommu_enable_translation: enabling vt-d translation\n");
    spin_lock_irqsave(&iommu->register_lock, flags);
    iommu->gcmd |= DMA_GCMD_TE;
    dmar_writel(iommu->reg, DMAR_GCMD_REG, iommu->gcmd);
    /* Make sure hardware complete it */
    start_time = jiffies;
    for ( ; ; )
    {
        sts = dmar_readl(iommu->reg, DMAR_GSTS_REG);
        if ( sts & DMA_GSTS_TES )
            break;
        if ( time_after(jiffies, start_time + DMAR_OPERATION_TIMEOUT) )
            panic("DMAR hardware is malfunctional, please disable IOMMU\n");
        cpu_relax();
    }

    /* Disable PMRs when VT-d engine takes effect per spec definition */
    disable_pmr(iommu);
    spin_unlock_irqrestore(&iommu->register_lock, flags);
    return 0;
}

int iommu_disable_translation(struct iommu *iommu)
{
    u32 sts;
    unsigned long flags;
    unsigned long start_time;

    spin_lock_irqsave(&iommu->register_lock, flags);
    iommu->gcmd &= ~ DMA_GCMD_TE;
    dmar_writel(iommu->reg, DMAR_GCMD_REG, iommu->gcmd);

    /* Make sure hardware complete it */
    start_time = jiffies;
    for ( ; ; )
    {
        sts = dmar_readl(iommu->reg, DMAR_GSTS_REG);
        if ( !(sts & DMA_GSTS_TES) )
            break;
        if ( time_after(jiffies, start_time + DMAR_OPERATION_TIMEOUT) )
            panic("DMAR hardware is malfunctional, please disable IOMMU\n");
        cpu_relax();
    }
    spin_unlock_irqrestore(&iommu->register_lock, flags);
    return 0;
}

static struct iommu *vector_to_iommu[NR_VECTORS];
static int iommu_page_fault_do_one(struct iommu *iommu, int type,
                                   u8 fault_reason, u16 source_id, u32 addr)
{
    dprintk(XENLOG_WARNING VTDPREFIX,
            "iommu_page_fault:%s: DEVICE %x:%x.%x addr %x REASON %x\n",
            (type ? "DMA Read" : "DMA Write"),
            (source_id >> 8), PCI_SLOT(source_id & 0xFF),
            PCI_FUNC(source_id & 0xFF), addr, fault_reason);

 /* For 32-bit Xen, maddr_to_virt() can not be used in print_vtd_entries()
  * since the pages (except the pgd) are allocated from domheap.
  */
#ifndef __i386__
    print_vtd_entries(current->domain, (source_id >> 8),(source_id & 0xff),
                      (addr >> PAGE_SHIFT)); 
#endif
    return 0;
}

#define PRIMARY_FAULT_REG_LEN (16)
static void iommu_page_fault(int vector, void *dev_id,
                             struct cpu_user_regs *regs)
{
    struct iommu *iommu = dev_id;
    int reg, fault_index;
    u32 fault_status;
    unsigned long flags;

    dprintk(XENLOG_WARNING VTDPREFIX,
            "iommu_page_fault: iommu->reg = %p\n", iommu->reg);

    spin_lock_irqsave(&iommu->register_lock, flags);
    fault_status = dmar_readl(iommu->reg, DMAR_FSTS_REG);
    spin_unlock_irqrestore(&iommu->register_lock, flags);

    /* FIXME: ignore advanced fault log */
    if ( !(fault_status & DMA_FSTS_PPF) )
        return;
    fault_index = dma_fsts_fault_record_index(fault_status);
    reg = cap_fault_reg_offset(iommu->cap);
    for ( ; ; )
    {
        u8 fault_reason;
        u16 source_id;
        u32 guest_addr, data;
        int type;

        /* highest 32 bits */
        spin_lock_irqsave(&iommu->register_lock, flags);
        data = dmar_readl(iommu->reg, reg +
                          fault_index * PRIMARY_FAULT_REG_LEN + 12);
        if ( !(data & DMA_FRCD_F) )
        {
            spin_unlock_irqrestore(&iommu->register_lock, flags);
            break;
        }

        fault_reason = dma_frcd_fault_reason(data);
        type = dma_frcd_type(data);

        data = dmar_readl(iommu->reg, reg +
                          fault_index * PRIMARY_FAULT_REG_LEN + 8);
        source_id = dma_frcd_source_id(data);

        guest_addr = dmar_readq(iommu->reg, reg +
                                fault_index * PRIMARY_FAULT_REG_LEN);
        guest_addr = dma_frcd_page_addr(guest_addr);
        /* clear the fault */
        dmar_writel(iommu->reg, reg +
                    fault_index * PRIMARY_FAULT_REG_LEN + 12, DMA_FRCD_F);
        spin_unlock_irqrestore(&iommu->register_lock, flags);

        iommu_page_fault_do_one(iommu, type, fault_reason,
                                source_id, guest_addr);

        fault_index++;
        if ( fault_index > cap_num_fault_regs(iommu->cap) )
            fault_index = 0;
    }

    /* clear primary fault overflow */
    if ( fault_status & DMA_FSTS_PFO )
    {
        spin_lock_irqsave(&iommu->register_lock, flags);
        dmar_writel(iommu->reg, DMAR_FSTS_REG, DMA_FSTS_PFO);
        spin_unlock_irqrestore(&iommu->register_lock, flags);
    }
}

static void dma_msi_unmask(unsigned int vector)
{
    struct iommu *iommu = vector_to_iommu[vector];
    unsigned long flags;

    /* unmask it */
    spin_lock_irqsave(&iommu->register_lock, flags);
    dmar_writel(iommu->reg, DMAR_FECTL_REG, 0);
    spin_unlock_irqrestore(&iommu->register_lock, flags);
}

static void dma_msi_mask(unsigned int vector)
{
    unsigned long flags;
    struct iommu *iommu = vector_to_iommu[vector];

    /* mask it */
    spin_lock_irqsave(&iommu->register_lock, flags);
    dmar_writel(iommu->reg, DMAR_FECTL_REG, DMA_FECTL_IM);
    spin_unlock_irqrestore(&iommu->register_lock, flags);
}

static unsigned int dma_msi_startup(unsigned int vector)
{
    dma_msi_unmask(vector);
    return 0;
}

static void dma_msi_end(unsigned int vector)
{
    dma_msi_unmask(vector);
    ack_APIC_irq();
}

static void dma_msi_data_init(struct iommu *iommu, int vector)
{
    u32 msi_data = 0;
    unsigned long flags;

    /* Fixed, edge, assert mode. Follow MSI setting */
    msi_data |= vector & 0xff;
    msi_data |= 1 << 14;

    spin_lock_irqsave(&iommu->register_lock, flags);
    dmar_writel(iommu->reg, DMAR_FEDATA_REG, msi_data);
    spin_unlock_irqrestore(&iommu->register_lock, flags);
}

static void dma_msi_addr_init(struct iommu *iommu, int phy_cpu)
{
    u64 msi_address;
    unsigned long flags;

    /* Physical, dedicated cpu. Follow MSI setting */
    msi_address = (MSI_ADDRESS_HEADER << (MSI_ADDRESS_HEADER_SHIFT + 8));
    msi_address |= MSI_PHYSICAL_MODE << 2;
    msi_address |= MSI_REDIRECTION_HINT_MODE << 3;
    msi_address |= phy_cpu << MSI_TARGET_CPU_SHIFT;

    spin_lock_irqsave(&iommu->register_lock, flags);
    dmar_writel(iommu->reg, DMAR_FEADDR_REG, (u32)msi_address);
    dmar_writel(iommu->reg, DMAR_FEUADDR_REG, (u32)(msi_address >> 32));
    spin_unlock_irqrestore(&iommu->register_lock, flags);
}

static void dma_msi_set_affinity(unsigned int vector, cpumask_t dest)
{
    struct iommu *iommu = vector_to_iommu[vector];
    dma_msi_addr_init(iommu, cpu_physical_id(first_cpu(dest)));
}

static struct hw_interrupt_type dma_msi_type = {
    .typename = "DMA_MSI",
    .startup = dma_msi_startup,
    .shutdown = dma_msi_mask,
    .enable = dma_msi_unmask,
    .disable = dma_msi_mask,
    .ack = dma_msi_mask,
    .end = dma_msi_end,
    .set_affinity = dma_msi_set_affinity,
};

int iommu_set_interrupt(struct iommu *iommu)
{
    int vector, ret;

    vector = assign_irq_vector(AUTO_ASSIGN);
    vector_to_iommu[vector] = iommu;

    /* VT-d fault is a MSI, make irq == vector */
    irq_vector[vector] = vector;
    vector_irq[vector] = vector;

    if ( !vector )
    {
        gdprintk(XENLOG_ERR VTDPREFIX, "IOMMU: no vectors\n");
        return -EINVAL;
    }

    irq_desc[vector].handler = &dma_msi_type;
    ret = request_irq(vector, iommu_page_fault, 0, "dmar", iommu);
    if ( ret )
        gdprintk(XENLOG_ERR VTDPREFIX, "IOMMU: can't request irq\n");
    return vector;
}

struct iommu *iommu_alloc(void *hw_data)
{
    struct acpi_drhd_unit *drhd = (struct acpi_drhd_unit *) hw_data;
    struct iommu *iommu;
    unsigned long sagaw;
    int agaw;

    if ( nr_iommus > MAX_IOMMUS )
    {
        gdprintk(XENLOG_ERR VTDPREFIX,
                 "IOMMU: nr_iommus %d > MAX_IOMMUS\n", nr_iommus);
        return NULL;
    }

    iommu = xmalloc(struct iommu);
    if ( !iommu )
        return NULL;
    memset(iommu, 0, sizeof(struct iommu));

    set_fixmap_nocache(FIX_IOMMU_REGS_BASE_0 + nr_iommus, drhd->address);
    iommu->reg = (void *) fix_to_virt(FIX_IOMMU_REGS_BASE_0 + nr_iommus);
    dprintk(XENLOG_INFO VTDPREFIX,
            "iommu_alloc: iommu->reg = %p drhd->address = %lx\n",
            iommu->reg, drhd->address);
    iommu->index = nr_iommus++;

    if ( !iommu->reg )
    {
        printk(KERN_ERR VTDPREFIX "IOMMU: can't mapping the region\n");
        goto error;
    }

    iommu->cap = dmar_readq(iommu->reg, DMAR_CAP_REG);
    iommu->ecap = dmar_readq(iommu->reg, DMAR_ECAP_REG);

    /* Calculate number of pagetable levels: between 2 and 4. */
    sagaw = cap_sagaw(iommu->cap);
    for ( agaw = level_to_agaw(4); agaw >= 0; agaw-- )
        if ( test_bit(agaw, &sagaw) )
            break;
    if ( agaw < 0 )
    {
        gdprintk(XENLOG_ERR VTDPREFIX,
                 "IOMMU: unsupported sagaw %lx\n", sagaw);
        xfree(iommu);
        return NULL;
    }
    iommu->nr_pt_levels = agaw_to_level(agaw);

    if ( !ecap_coherent(iommu->ecap) )
        iommus_incoherent = 1;

    spin_lock_init(&iommu->lock);
    spin_lock_init(&iommu->register_lock);

    drhd->iommu = iommu;
    return iommu;
 error:
    xfree(iommu);
    return NULL;
}

static void free_iommu(struct iommu *iommu)
{
    if ( !iommu )
        return;
    if ( iommu->root_entry )
        free_xenheap_page((void *)iommu->root_entry);
    if ( iommu->reg )
        iounmap(iommu->reg);
    free_irq(iommu->vector);
    xfree(iommu);
}

#define guestwidth_to_adjustwidth(gaw) ({       \
    int agaw, r = (gaw - 12) % 9;               \
    agaw = (r == 0) ? gaw : (gaw + 9 - r);      \
    if ( agaw > 64 )                            \
        agaw = 64;                              \
    agaw; })

int iommu_domain_init(struct domain *domain)
{
    struct hvm_iommu *hd = domain_hvm_iommu(domain);
    struct iommu *iommu = NULL;
    struct acpi_drhd_unit *drhd;

    spin_lock_init(&hd->mapping_lock);
    spin_lock_init(&hd->iommu_list_lock);
    INIT_LIST_HEAD(&hd->pdev_list);
    INIT_LIST_HEAD(&hd->g2m_ioport_list);

    if ( !vtd_enabled || list_empty(&acpi_drhd_units) )
        return 0;

    for_each_drhd_unit ( drhd )
        iommu = drhd->iommu ? : iommu_alloc(drhd);

    hd->agaw = width_to_agaw(DEFAULT_DOMAIN_ADDRESS_WIDTH);
    return 0;
}

static int domain_context_mapping_one(
    struct domain *domain,
    struct iommu *iommu,
    u8 bus, u8 devfn)
{
    struct hvm_iommu *hd = domain_hvm_iommu(domain);
    struct context_entry *context;
    unsigned long flags;
    int ret = 0;
    u64 pgd_maddr;
    int agaw = -1;

    context = device_to_context_entry(iommu, bus, devfn);
    if ( !context )
    {
        gdprintk(XENLOG_ERR VTDPREFIX,
                 "domain_context_mapping_one:context == NULL:"
                 "bdf = %x:%x:%x\n",
                 bus, PCI_SLOT(devfn), PCI_FUNC(devfn));
        return -ENOMEM;
    }

    if ( context_present(*context) )
    {
        gdprintk(XENLOG_WARNING VTDPREFIX,
                 "domain_context_mapping_one:context present:bdf=%x:%x:%x\n",
                 bus, PCI_SLOT(devfn), PCI_FUNC(devfn));
        return 0;
    }

    spin_lock_irqsave(&iommu->lock, flags);

    if ( ecap_pass_thru(iommu->ecap) && (domain->domain_id == 0) )
        context_set_translation_type(*context, CONTEXT_TT_PASS_THRU);
    else
    {
        /* Ensure we have pagetables allocated down to leaf PTE. */
        if ( !hd->pgd )
        {
            addr_to_dma_page(domain, 0);
            if ( !hd->pgd )
            {
            nomem:
                spin_unlock_irqrestore(&hd->mapping_lock, flags);
                return -ENOMEM;
            }
        }
 
        /* Skip top levels of page tables for 2- and 3-level DRHDs. */
        pgd_maddr = virt_to_maddr(hd->pgd);
        for ( agaw = level_to_agaw(4);
              agaw != level_to_agaw(iommu->nr_pt_levels);
              agaw-- )
        {
            if ( agaw == level_to_agaw(4) )
                pgd_maddr = dma_pte_addr(*hd->pgd);
            else
            {
                struct dma_pte *p = map_domain_page(pgd_maddr);
                pgd_maddr = dma_pte_addr(*p);
                unmap_domain_page(p);
                if ( pgd_maddr == 0 )
                    goto nomem;
            } 
        }
        context_set_address_root(*context, pgd_maddr);
        context_set_translation_type(*context, CONTEXT_TT_MULTI_LEVEL);
    }

    /*
     * domain_id 0 is not valid on Intel's IOMMU, force domain_id to
     * be 1 based as required by intel's iommu hw.
     */
    BUG_ON(agaw == -1);
    context_set_domain_id(context, domain);
    context_set_address_width(*context, agaw);
    context_set_fault_enable(*context);
    context_set_present(*context);
    iommu_flush_cache_entry(context);

    gdprintk(XENLOG_INFO VTDPREFIX,
             "domain_context_mapping_one-%x:%x:%x-*context=%"PRIx64":%"PRIx64
             " hd->pgd=%p\n",
             bus, PCI_SLOT(devfn), PCI_FUNC(devfn),
             context->hi, context->lo, hd->pgd);

    if ( iommu_flush_context_device(iommu, domain_iommu_domid(domain),
                                    (((u16)bus) << 8) | devfn,
                                    DMA_CCMD_MASK_NOBIT, 1) )
        iommu_flush_write_buffer(iommu);
    else
        iommu_flush_iotlb_dsi(iommu, domain_iommu_domid(domain), 0);

    set_bit(iommu->index, &hd->iommu_bitmap);
    spin_unlock_irqrestore(&iommu->lock, flags);
    return ret;
}

static int __pci_find_next_cap(u8 bus, unsigned int devfn, u8 pos, int cap)
{
    u8 id;
    int ttl = 48;

    while ( ttl-- )
    {
        pos = read_pci_config_byte(bus, PCI_SLOT(devfn), PCI_FUNC(devfn), pos);
        if ( pos < 0x40 )
            break;

        pos &= ~3;
        id = read_pci_config_byte(bus, PCI_SLOT(devfn), PCI_FUNC(devfn),
                                  pos + PCI_CAP_LIST_ID);

        if ( id == 0xff )
            break;
        if ( id == cap )
            return pos;

        pos += PCI_CAP_LIST_NEXT;
    }
    return 0;
}

#define PCI_BASE_CLASS_BRIDGE    0x06
#define PCI_CLASS_BRIDGE_PCI     0x0604

#define DEV_TYPE_PCIe_ENDPOINT   1
#define DEV_TYPE_PCI_BRIDGE      2
#define DEV_TYPE_PCI             3

int pdev_type(struct pci_dev *dev)
{
    u16 class_device;
    u16 status;

    class_device = read_pci_config_16(dev->bus, PCI_SLOT(dev->devfn),
                                      PCI_FUNC(dev->devfn), PCI_CLASS_DEVICE);
    if ( class_device == PCI_CLASS_BRIDGE_PCI )
        return DEV_TYPE_PCI_BRIDGE;

    status = read_pci_config_16(dev->bus, PCI_SLOT(dev->devfn),
                                PCI_FUNC(dev->devfn), PCI_STATUS);

    if ( !(status & PCI_STATUS_CAP_LIST) )
        return DEV_TYPE_PCI;

    if ( __pci_find_next_cap(dev->bus, dev->devfn,
                            PCI_CAPABILITY_LIST, PCI_CAP_ID_EXP) )
        return DEV_TYPE_PCIe_ENDPOINT;

    return DEV_TYPE_PCI;
}

#define MAX_BUSES 256
struct pci_dev bus2bridge[MAX_BUSES];

static int domain_context_mapping(
    struct domain *domain,
    struct iommu *iommu,
    struct pci_dev *pdev)
{
    int ret = 0;
    int dev, func, sec_bus, sub_bus;
    u32 type;

    type = pdev_type(pdev);
    switch ( type )
    {
    case DEV_TYPE_PCI_BRIDGE:
        sec_bus = read_pci_config_byte(
            pdev->bus, PCI_SLOT(pdev->devfn),
            PCI_FUNC(pdev->devfn), PCI_SECONDARY_BUS);

        if ( bus2bridge[sec_bus].bus == 0 )
        {
            bus2bridge[sec_bus].bus   =  pdev->bus;
            bus2bridge[sec_bus].devfn =  pdev->devfn;
        }

        sub_bus = read_pci_config_byte(
            pdev->bus, PCI_SLOT(pdev->devfn),
            PCI_FUNC(pdev->devfn), PCI_SUBORDINATE_BUS);

        if ( sec_bus != sub_bus )
            gdprintk(XENLOG_WARNING VTDPREFIX,
                     "context_context_mapping: nested PCI bridge not "
                     "supported: bdf = %x:%x:%x sec_bus = %x sub_bus = %x\n",
                     pdev->bus, PCI_SLOT(pdev->devfn), PCI_FUNC(pdev->devfn),
                     sec_bus, sub_bus);
        break;
    case DEV_TYPE_PCIe_ENDPOINT:
        gdprintk(XENLOG_INFO VTDPREFIX,
                 "domain_context_mapping:PCIe : bdf = %x:%x:%x\n",
                 pdev->bus, PCI_SLOT(pdev->devfn), PCI_FUNC(pdev->devfn));
        ret = domain_context_mapping_one(domain, iommu,
                                         (u8)(pdev->bus), (u8)(pdev->devfn));
        break;
    case DEV_TYPE_PCI:
        gdprintk(XENLOG_INFO VTDPREFIX,
                 "domain_context_mapping:PCI: bdf = %x:%x:%x\n",
                 pdev->bus, PCI_SLOT(pdev->devfn), PCI_FUNC(pdev->devfn));

        if ( pdev->bus == 0 )
            ret = domain_context_mapping_one(
                domain, iommu, (u8)(pdev->bus), (u8)(pdev->devfn));
        else
        {
            if ( bus2bridge[pdev->bus].bus != 0 )
                gdprintk(XENLOG_WARNING VTDPREFIX,
                         "domain_context_mapping:bus2bridge"
                         "[%d].bus != 0\n", pdev->bus);

            ret = domain_context_mapping_one(
                domain, iommu,
                (u8)(bus2bridge[pdev->bus].bus),
                (u8)(bus2bridge[pdev->bus].devfn));

            /* now map everything behind the PCI bridge */
            for ( dev = 0; dev < 32; dev++ )
            {
                for ( func = 0; func < 8; func++ )
                {
                    ret = domain_context_mapping_one(
                        domain, iommu,
                        pdev->bus, (u8)PCI_DEVFN(dev, func));
                    if ( ret )
                        return ret;
                }
            }
        }
        break;
    default:
        gdprintk(XENLOG_ERR VTDPREFIX,
                 "domain_context_mapping:unknown type : bdf = %x:%x:%x\n",
                 pdev->bus, PCI_SLOT(pdev->devfn), PCI_FUNC(pdev->devfn));
        ret = -EINVAL;
        break;
    }

    return ret;
}

static int domain_context_unmap_one(
    struct domain *domain,
    struct iommu *iommu,
    u8 bus, u8 devfn)
{
    struct context_entry *context;
    unsigned long flags;

    context = device_to_context_entry(iommu, bus, devfn);
    if ( !context )
    {
        gdprintk(XENLOG_ERR VTDPREFIX,
                 "domain_context_unmap_one-%x:%x:%x- context == NULL:return\n",
                 bus, PCI_SLOT(devfn), PCI_FUNC(devfn));
        return -ENOMEM;
    }

    if ( !context_present(*context) )
    {
        gdprintk(XENLOG_WARNING VTDPREFIX,
                 "domain_context_unmap_one-%x:%x:%x- "
                 "context NOT present:return\n",
                 bus, PCI_SLOT(devfn), PCI_FUNC(devfn));
        return 0;
    }

    gdprintk(XENLOG_INFO VTDPREFIX,
             "domain_context_unmap_one: bdf = %x:%x:%x\n",
             bus, PCI_SLOT(devfn), PCI_FUNC(devfn));

    spin_lock_irqsave(&iommu->lock, flags);
    context_clear_present(*context);
    context_clear_entry(*context);
    iommu_flush_cache_entry(context);
    iommu_flush_context_global(iommu, 0);
    iommu_flush_iotlb_global(iommu, 0);
    spin_unlock_irqrestore(&iommu->lock, flags);

    return 0;
}

static int domain_context_unmap(
    struct domain *domain,
    struct iommu *iommu,
    struct pci_dev *pdev)
{
    int ret = 0;
    int dev, func, sec_bus, sub_bus;
    u32 type;

    type = pdev_type(pdev);
    switch ( type )
    {
    case DEV_TYPE_PCI_BRIDGE:
        sec_bus = read_pci_config_byte(
            pdev->bus, PCI_SLOT(pdev->devfn),
            PCI_FUNC(pdev->devfn), PCI_SECONDARY_BUS);
        sub_bus = read_pci_config_byte(
            pdev->bus, PCI_SLOT(pdev->devfn),
            PCI_FUNC(pdev->devfn), PCI_SUBORDINATE_BUS);

        gdprintk(XENLOG_INFO VTDPREFIX,
                 "domain_context_unmap:BRIDGE:%x:%x:%x "
                 "sec_bus=%x sub_bus=%x\n",
                 pdev->bus, PCI_SLOT(pdev->devfn),
                 PCI_FUNC(pdev->devfn), sec_bus, sub_bus);
        break;
    case DEV_TYPE_PCIe_ENDPOINT:
        gdprintk(XENLOG_INFO VTDPREFIX,
                 "domain_context_unmap:PCIe : bdf = %x:%x:%x\n",
                 pdev->bus, PCI_SLOT(pdev->devfn), PCI_FUNC(pdev->devfn));
        ret = domain_context_unmap_one(domain, iommu,
                                       (u8)(pdev->bus), (u8)(pdev->devfn));
        break;
    case DEV_TYPE_PCI:
        gdprintk(XENLOG_INFO VTDPREFIX,
                 "domain_context_unmap:PCI: bdf = %x:%x:%x\n",
                 pdev->bus, PCI_SLOT(pdev->devfn), PCI_FUNC(pdev->devfn));
        if ( pdev->bus == 0 )
            ret = domain_context_unmap_one(
                domain, iommu,
                (u8)(pdev->bus), (u8)(pdev->devfn));
        else
        {
            if ( bus2bridge[pdev->bus].bus != 0 )
                gdprintk(XENLOG_WARNING VTDPREFIX,
                         "domain_context_unmap:"
                         "bus2bridge[%d].bus != 0\n", pdev->bus);

            ret = domain_context_unmap_one(domain, iommu,
                                           (u8)(bus2bridge[pdev->bus].bus),
                                           (u8)(bus2bridge[pdev->bus].devfn));

            /* Unmap everything behind the PCI bridge */
            for ( dev = 0; dev < 32; dev++ )
            {
                for ( func = 0; func < 8; func++ )
                {
                    ret = domain_context_unmap_one(
                        domain, iommu,
                        pdev->bus, (u8)PCI_DEVFN(dev, func));
                    if ( ret )
                        return ret;
                }
            }
        }
        break;
    default:
        gdprintk(XENLOG_ERR VTDPREFIX,
                 "domain_context_unmap:unknown type: bdf = %x:%x:%x\n",
                 pdev->bus, PCI_SLOT(pdev->devfn), PCI_FUNC(pdev->devfn));
        ret = -EINVAL;
        break;
    }

    return ret;
}

void reassign_device_ownership(
    struct domain *source,
    struct domain *target,
    u8 bus, u8 devfn)
{
    struct hvm_iommu *source_hd = domain_hvm_iommu(source);
    struct hvm_iommu *target_hd = domain_hvm_iommu(target);
    struct pci_dev *pdev, *pdev2;
    struct acpi_drhd_unit *drhd;
    struct iommu *iommu;
    int status;
    unsigned long flags;
    int found = 0;

    gdprintk(XENLOG_INFO VTDPREFIX,
             "reassign_device-%x:%x:%x- source = %d target = %d\n",
             bus, PCI_SLOT(devfn), PCI_FUNC(devfn),
             source->domain_id, target->domain_id);

    for_each_pdev( source, pdev )
    {
        if ( (pdev->bus != bus) || (pdev->devfn != devfn) )
            continue;

        drhd = acpi_find_matched_drhd_unit(pdev);
        iommu = drhd->iommu;
        domain_context_unmap(source, iommu, pdev);

        /* Move pci device from the source domain to target domain. */
        spin_lock_irqsave(&source_hd->iommu_list_lock, flags);
        spin_lock(&target_hd->iommu_list_lock);
        list_move(&pdev->list, &target_hd->pdev_list);
        spin_unlock(&target_hd->iommu_list_lock);
        spin_unlock_irqrestore(&source_hd->iommu_list_lock, flags);

        for_each_pdev ( source, pdev2 )
        {
            drhd = acpi_find_matched_drhd_unit(pdev2);
            if ( drhd->iommu == iommu )
            {
                found = 1;
                break;
            }
        }
        if ( !found )
            clear_bit(iommu->index, &source_hd->iommu_bitmap);

        status = domain_context_mapping(target, iommu, pdev);
        if ( status != 0 )
            gdprintk(XENLOG_ERR VTDPREFIX, "domain_context_mapping failed\n");

        break;
    }
}

void return_devices_to_dom0(struct domain *d)
{
    struct hvm_iommu *hd  = domain_hvm_iommu(d);
    struct pci_dev *pdev;

    while ( !list_empty(&hd->pdev_list) )
    {
        pdev = list_entry(hd->pdev_list.next, typeof(*pdev), list);
        dprintk(XENLOG_INFO VTDPREFIX,
                "return_devices_to_dom0: bdf = %x:%x:%x\n",
                pdev->bus, PCI_SLOT(pdev->devfn), PCI_FUNC(pdev->devfn));
        pdev_flr(pdev->bus, pdev->devfn);
        reassign_device_ownership(d, dom0, pdev->bus, pdev->devfn);
    }

#ifdef VTD_DEBUG
    for_each_pdev ( dom0, pdev )
        dprintk(XENLOG_INFO VTDPREFIX,
                "return_devices_to_dom0:%x: bdf = %x:%x:%x\n",
                dom0->domain_id, pdev->bus,
                PCI_SLOT(pdev->devfn), PCI_FUNC(pdev->devfn));
#endif
}

void iommu_domain_teardown(struct domain *d)
{
    if ( list_empty(&acpi_drhd_units) )
        return;

    iommu_domid_release(d);

#if CONFIG_PAGING_LEVELS == 3
    {
        struct hvm_iommu *hd  = domain_hvm_iommu(d);
        int level = agaw_to_level(hd->agaw);
        struct dma_pte *pgd = NULL;

        switch ( level )
        {
        case VTD_PAGE_TABLE_LEVEL_3:
            if ( hd->pgd )
                free_xenheap_page((void *)hd->pgd);
            break;
        case VTD_PAGE_TABLE_LEVEL_4:
            if ( hd->pgd )
            {
                pgd = hd->pgd;
                if ( pgd[0].val != 0 )
                    free_xenheap_page((void*)maddr_to_virt(
                        dma_pte_addr(pgd[0])));

                free_xenheap_page((void *)hd->pgd);
            }
            break;
        default:
            gdprintk(XENLOG_ERR VTDPREFIX,
                     "Unsupported p2m table sharing level!\n");
            break;
        }
    }
#endif
    return_devices_to_dom0(d);
}

static int domain_context_mapped(struct pci_dev *pdev)
{
    struct acpi_drhd_unit *drhd;
    struct iommu *iommu;
    int ret;

    for_each_drhd_unit ( drhd )
    {
        iommu = drhd->iommu;
        ret = device_context_mapped(iommu, pdev->bus, pdev->devfn);
        if ( ret )
            return ret;
    }

    return 0;
}

int iommu_map_page(struct domain *d, paddr_t gfn, paddr_t mfn)
{
    struct hvm_iommu *hd = domain_hvm_iommu(d);
    struct acpi_drhd_unit *drhd;
    struct iommu *iommu;
    struct dma_pte *pte = NULL;
    struct page_info *pg = NULL;

    drhd = list_entry(acpi_drhd_units.next, typeof(*drhd), list);
    iommu = drhd->iommu;

    /* do nothing if dom0 and iommu supports pass thru */
    if ( ecap_pass_thru(iommu->ecap) && (d->domain_id == 0) )
        return 0;

    pg = addr_to_dma_page(d, gfn << PAGE_SHIFT_4K);
    if ( !pg )
        return -ENOMEM;
    pte = (struct dma_pte *)map_domain_page(page_to_mfn(pg));
    pte += gfn & LEVEL_MASK;
    dma_set_pte_addr(*pte, mfn << PAGE_SHIFT_4K);
    dma_set_pte_prot(*pte, DMA_PTE_READ | DMA_PTE_WRITE);
    iommu_flush_cache_entry(pte);
    unmap_domain_page(pte);

    for_each_drhd_unit ( drhd )
    {
        iommu = drhd->iommu;

        if ( !test_bit(iommu->index, &hd->iommu_bitmap) )
            continue;

        if ( cap_caching_mode(iommu->cap) )
            iommu_flush_iotlb_psi(iommu, domain_iommu_domid(d),
                                  gfn << PAGE_SHIFT_4K, 1, 0);
        else if ( cap_rwbf(iommu->cap) )
            iommu_flush_write_buffer(iommu);
    }

    return 0;
}

int iommu_unmap_page(struct domain *d, dma_addr_t gfn)
{
    struct acpi_drhd_unit *drhd;
    struct iommu *iommu;

    drhd = list_entry(acpi_drhd_units.next, typeof(*drhd), list);
    iommu = drhd->iommu;

    /* do nothing if dom0 and iommu supports pass thru */
    if ( ecap_pass_thru(iommu->ecap) && (d->domain_id == 0) )
        return 0;

    dma_pte_clear_one(d, gfn << PAGE_SHIFT_4K);

    return 0;
}

int iommu_page_mapping(struct domain *domain, dma_addr_t iova,
                       void *hpa, size_t size, int prot)
{
    struct hvm_iommu *hd = domain_hvm_iommu(domain);
    struct acpi_drhd_unit *drhd;
    struct iommu *iommu;
    unsigned long start_pfn, end_pfn;
    struct dma_pte *pte = NULL;
    int index;
    struct page_info *pg = NULL;

    if ( (prot & (DMA_PTE_READ|DMA_PTE_WRITE)) == 0 )
        return -EINVAL;
    iova = (iova >> PAGE_SHIFT_4K) << PAGE_SHIFT_4K;
    start_pfn = (unsigned long)(((unsigned long) hpa) >> PAGE_SHIFT_4K);
    end_pfn = (unsigned long)
        ((PAGE_ALIGN_4K(((unsigned long)hpa) + size)) >> PAGE_SHIFT_4K);
    index = 0;
    while ( start_pfn < end_pfn )
    {
        pg = addr_to_dma_page(domain, iova + PAGE_SIZE_4K * index);
        if ( !pg )
            return -ENOMEM;
        pte = (struct dma_pte *)map_domain_page(page_to_mfn(pg));
        pte += start_pfn & LEVEL_MASK;
        dma_set_pte_addr(*pte, start_pfn << PAGE_SHIFT_4K);
        dma_set_pte_prot(*pte, prot);
        iommu_flush_cache_entry(pte);
        unmap_domain_page(pte);
        start_pfn++;
        index++;
    }

    for_each_drhd_unit ( drhd )
    {
        iommu = drhd->iommu;

        if ( !test_bit(iommu->index, &hd->iommu_bitmap) )
            continue;

        if ( cap_caching_mode(iommu->cap) )
            iommu_flush_iotlb_psi(iommu, domain_iommu_domid(domain),
                                  iova, index, 0);
        else if ( cap_rwbf(iommu->cap) )
            iommu_flush_write_buffer(iommu);
    }

    return 0;
}

int iommu_page_unmapping(struct domain *domain, dma_addr_t addr, size_t size)
{
    dma_pte_clear_range(domain, addr, addr + size);

    return 0;
}

void iommu_flush(struct domain *d, dma_addr_t gfn, u64 *p2m_entry)
{
    struct hvm_iommu *hd = domain_hvm_iommu(d);
    struct acpi_drhd_unit *drhd;
    struct iommu *iommu = NULL;
    struct dma_pte *pte = (struct dma_pte *) p2m_entry;

    for_each_drhd_unit ( drhd )
    {
        iommu = drhd->iommu;

        if ( !test_bit(iommu->index, &hd->iommu_bitmap) )
            continue;

        if ( cap_caching_mode(iommu->cap) )
            iommu_flush_iotlb_psi(iommu, domain_iommu_domid(d),
                                  gfn << PAGE_SHIFT_4K, 1, 0);
        else if ( cap_rwbf(iommu->cap) )
            iommu_flush_write_buffer(iommu);
    }

    iommu_flush_cache_entry(pte);
}

static int iommu_prepare_rmrr_dev(
    struct domain *d,
    struct acpi_rmrr_unit *rmrr,
    struct pci_dev *pdev)
{
    struct acpi_drhd_unit *drhd;
    unsigned long size;
    int ret;

    /* page table init */
    size = rmrr->end_address - rmrr->base_address + 1;
    ret = iommu_page_mapping(d, rmrr->base_address,
                             (void *)rmrr->base_address, size,
                             DMA_PTE_READ|DMA_PTE_WRITE);
    if ( ret )
        return ret;

    if ( domain_context_mapped(pdev) == 0 )
    {
        drhd = acpi_find_matched_drhd_unit(pdev);
        ret = domain_context_mapping(d, drhd->iommu, pdev);
        if ( !ret )
            return 0;
    }

    return ret;
}

void __init setup_dom0_devices(void)
{
    struct hvm_iommu *hd  = domain_hvm_iommu(dom0);
    struct acpi_drhd_unit *drhd;
    struct pci_dev *pdev;
    int bus, dev, func, ret;
    u32 l;

#ifdef DEBUG_VTD_CONTEXT_ENTRY
    for ( bus = 0; bus < 256; bus++ )
    {
        for ( dev = 0; dev < 32; dev++ )
        { 
            for ( func = 0; func < 8; func++ )
            {
                struct context_entry *context;
                struct pci_dev device;

                device.bus = bus; 
                device.devfn = PCI_DEVFN(dev, func); 
                drhd = acpi_find_matched_drhd_unit(&device);
                context = device_to_context_entry(drhd->iommu,
                                                  bus, PCI_DEVFN(dev, func));
                if ( (context->lo != 0) || (context->hi != 0) )
                    dprintk(XENLOG_INFO VTDPREFIX,
                            "setup_dom0_devices-%x:%x:%x- context not 0\n",
                            bus, dev, func);
            }
        }    
    }        
#endif

    for ( bus = 0; bus < 256; bus++ )
    {
        for ( dev = 0; dev < 32; dev++ )
        {
            for ( func = 0; func < 8; func++ )
            {
                l = read_pci_config(bus, dev, func, PCI_VENDOR_ID);
                /* some broken boards return 0 or ~0 if a slot is empty: */
                if ( (l == 0xffffffff) || (l == 0x00000000) ||
                     (l == 0x0000ffff) || (l == 0xffff0000) )
                    continue;
                pdev = xmalloc(struct pci_dev);
                pdev->bus = bus;
                pdev->devfn = PCI_DEVFN(dev, func);
                list_add_tail(&pdev->list, &hd->pdev_list);

                drhd = acpi_find_matched_drhd_unit(pdev);
                ret = domain_context_mapping(dom0, drhd->iommu, pdev);
                if ( ret != 0 )
                    gdprintk(XENLOG_ERR VTDPREFIX,
                             "domain_context_mapping failed\n");
            }
        }
    }

    for_each_pdev ( dom0, pdev )
        dprintk(XENLOG_INFO VTDPREFIX,
                "setup_dom0_devices: bdf = %x:%x:%x\n",
                pdev->bus, PCI_SLOT(pdev->devfn), PCI_FUNC(pdev->devfn));
}

void clear_fault_bit(struct iommu *iommu)
{
    u64 val;

    val = dmar_readq(
        iommu->reg,
        cap_fault_reg_offset(dmar_readq(iommu->reg,DMAR_CAP_REG))+0x8);
    dmar_writeq(
        iommu->reg,
        cap_fault_reg_offset(dmar_readq(iommu->reg,DMAR_CAP_REG))+8,
        val);
    dmar_writel(iommu->reg, DMAR_FSTS_REG, DMA_FSTS_PFO);
}

static int init_vtd_hw(void)
{
    struct acpi_drhd_unit *drhd;
    struct iommu *iommu;
    int ret;

    for_each_drhd_unit ( drhd )
    {
        iommu = drhd->iommu;
        ret = iommu_set_root_entry(iommu);
        if ( ret )
        {
            gdprintk(XENLOG_ERR VTDPREFIX, "IOMMU: set root entry failed\n");
            return -EIO;
        }
    }

    return 0;
}

static int enable_vtd_translation(void)
{
    struct acpi_drhd_unit *drhd;
    struct iommu *iommu;
    int vector = 0;

    for_each_drhd_unit ( drhd )
    {
        iommu = drhd->iommu;
        vector = iommu_set_interrupt(iommu);
        dma_msi_data_init(iommu, vector);
        dma_msi_addr_init(iommu, cpu_physical_id(first_cpu(cpu_online_map)));
        iommu->vector = vector;
        clear_fault_bit(iommu);
        if ( iommu_enable_translation(iommu) )
            return -EIO;
    }

    return 0;
}

static void setup_dom0_rmrr(void)
{
    struct acpi_rmrr_unit *rmrr;
    struct pci_dev *pdev;
    int ret;

    for_each_rmrr_device ( rmrr, pdev )
        ret = iommu_prepare_rmrr_dev(dom0, rmrr, pdev);
        if ( ret )
            gdprintk(XENLOG_ERR VTDPREFIX,
                     "IOMMU: mapping reserved region failed\n");
    end_for_each_rmrr_device ( rmrr, pdev )
}

int iommu_setup(void)
{
    struct hvm_iommu *hd  = domain_hvm_iommu(dom0);
    struct acpi_drhd_unit *drhd;
    struct iommu *iommu;
    u64 i;

    if ( !vtd_enabled )
        return 0;

    spin_lock_init(&domid_bitmap_lock);
    INIT_LIST_HEAD(&hd->pdev_list);

    /* start from scratch */
    iommu_flush_all();

    /* setup clflush size */
    x86_clflush_size = ((cpuid_ebx(1) >> 8) & 0xff) * 8;

    /* Allocate IO page directory page for the domain. */
    drhd = list_entry(acpi_drhd_units.next, typeof(*drhd), list);
    iommu = drhd->iommu;

    /* Allocate domain id bitmap, and set bit 0 as reserved */
    domid_bitmap_size = cap_ndoms(iommu->cap);
    domid_bitmap = xmalloc_bytes(domid_bitmap_size / 8);
    if ( domid_bitmap == NULL )
        goto error;
    memset(domid_bitmap, 0, domid_bitmap_size / 8);
    set_bit(0, domid_bitmap);

    /*
     * Set up 1:1 page table for dom0 except the critical segments
     * like Xen and tboot.
     */
    for ( i = 0; i < max_page; i++ )
    {
        extern int xen_in_range(paddr_t start, paddr_t end);
        extern int tboot_in_range(paddr_t start, paddr_t end);

        if ( xen_in_range(i << PAGE_SHIFT_4K, (i + 1) << PAGE_SHIFT_4K) ||
            tboot_in_range(i << PAGE_SHIFT_4K, (i + 1) << PAGE_SHIFT_4K) )
            continue;

        iommu_map_page(dom0, i, i);
    }

    if ( init_vtd_hw() )
        goto error;
    setup_dom0_devices();
    setup_dom0_rmrr();
    if ( enable_vtd_translation() )
        goto error;

    return 0;

 error:
    printk("iommu_setup() failed\n");
    for_each_drhd_unit ( drhd )
    {
        iommu = drhd->iommu;
        free_iommu(iommu);
    }
    return -EIO;
}

/*
 * If the device isn't owned by dom0, it means it already
 * has been assigned to other domain, or it's not exist.
 */
int device_assigned(u8 bus, u8 devfn)
{
    struct pci_dev *pdev;

    for_each_pdev( dom0, pdev )
        if ( (pdev->bus == bus ) && (pdev->devfn == devfn) )
            return 0;

    return 1;
}

int assign_device(struct domain *d, u8 bus, u8 devfn)
{
    struct acpi_rmrr_unit *rmrr;
    struct pci_dev *pdev;
    int ret = 0;

    if ( list_empty(&acpi_drhd_units) )
        return ret;

    gdprintk(XENLOG_INFO VTDPREFIX,
             "assign_device: bus = %x dev = %x func = %x\n",
             bus, PCI_SLOT(devfn), PCI_FUNC(devfn));

    pdev_flr(bus, devfn);
    reassign_device_ownership(dom0, d, bus, devfn);

    /* Setup rmrr identify mapping */
    for_each_rmrr_device( rmrr, pdev )
        if ( pdev->bus == bus && pdev->devfn == devfn )
        {
            /* FIXME: Because USB RMRR conflicts with guest bios region,
             * ignore USB RMRR temporarily.
             */
            if ( is_usb_device(pdev) )
                return 0;

            ret = iommu_prepare_rmrr_dev(d, rmrr, pdev);
            if ( ret )
            {
                gdprintk(XENLOG_ERR VTDPREFIX,
                         "IOMMU: mapping reserved region failed\n");
                return ret;
            }
        }
    end_for_each_rmrr_device(rmrr, pdev)

    return ret;
}

void iommu_set_pgd(struct domain *d)
{
    struct hvm_iommu *hd  = domain_hvm_iommu(d);
    unsigned long p2m_table;

    if ( hd->pgd )
    {
        gdprintk(XENLOG_INFO VTDPREFIX,
                 "iommu_set_pgd_1: hd->pgd = %p\n", hd->pgd);
        hd->pgd = NULL;
    }
    p2m_table = mfn_x(pagetable_get_mfn(d->arch.phys_table));

#if CONFIG_PAGING_LEVELS == 3
    if ( !hd->pgd )
    {
        int level = agaw_to_level(hd->agaw);
        struct dma_pte *pmd = NULL;
        struct dma_pte *pgd = NULL;
        struct dma_pte *pte = NULL;
        l3_pgentry_t *l3e;
        unsigned long flags;
        int i;

        spin_lock_irqsave(&hd->mapping_lock, flags);
        if ( !hd->pgd )
        {
            pgd = (struct dma_pte *)alloc_xenheap_page();
            if ( !pgd )
            {
                spin_unlock_irqrestore(&hd->mapping_lock, flags);
                gdprintk(XENLOG_ERR VTDPREFIX,
                         "Allocate pgd memory failed!\n");
                return;
            }
            memset(pgd, 0, PAGE_SIZE);
            hd->pgd = pgd;
       }

        l3e = map_domain_page(p2m_table);
        switch ( level )
        {
        case VTD_PAGE_TABLE_LEVEL_3:        /* Weybridge */
            /* We only support 8 entries for the PAE L3 p2m table */
            for ( i = 0; i < 8 ; i++ )
            {
                /* Don't create new L2 entry, use ones from p2m table */
                pgd[i].val = l3e[i].l3 | _PAGE_PRESENT | _PAGE_RW;
            }
            break;

        case VTD_PAGE_TABLE_LEVEL_4:        /* Stoakley */
            /* We allocate one more page for the top vtd page table. */
            pmd = (struct dma_pte *)alloc_xenheap_page();
            if ( !pmd )
            {
                unmap_domain_page(l3e);
                spin_unlock_irqrestore(&hd->mapping_lock, flags);
                gdprintk(XENLOG_ERR VTDPREFIX,
                         "Allocate pmd memory failed!\n");
                return;
            }
            memset((u8*)pmd, 0, PAGE_SIZE);
            pte = &pgd[0];
            dma_set_pte_addr(*pte, virt_to_maddr(pmd));
            dma_set_pte_readable(*pte);
            dma_set_pte_writable(*pte);

            for ( i = 0; i < 8; i++ )
            {
                /* Don't create new L2 entry, use ones from p2m table */
                pmd[i].val = l3e[i].l3 | _PAGE_PRESENT | _PAGE_RW;
            }
            break;
        default:
            gdprintk(XENLOG_ERR VTDPREFIX,
                     "iommu_set_pgd:Unsupported p2m table sharing level!\n");
            break;
        }
        unmap_domain_page(l3e);
        spin_unlock_irqrestore(&hd->mapping_lock, flags);
    }
#elif CONFIG_PAGING_LEVELS == 4
    if ( !hd->pgd )
    {
        int level = agaw_to_level(hd->agaw);
        l3_pgentry_t *l3e;
        mfn_t pgd_mfn;

        switch ( level )
        {
        case VTD_PAGE_TABLE_LEVEL_3:
            l3e = map_domain_page(p2m_table);
            if ( (l3e_get_flags(*l3e) & _PAGE_PRESENT) == 0 )
            {
                gdprintk(XENLOG_ERR VTDPREFIX,
                         "iommu_set_pgd: second level wasn't there\n");
                unmap_domain_page(l3e);
                return;
            }
            pgd_mfn = _mfn(l3e_get_pfn(*l3e));
            unmap_domain_page(l3e);
            hd->pgd = maddr_to_virt(pagetable_get_paddr(
                pagetable_from_mfn(pgd_mfn)));
            break;

        case VTD_PAGE_TABLE_LEVEL_4:
            pgd_mfn = _mfn(p2m_table);
            hd->pgd = maddr_to_virt(pagetable_get_paddr(
                pagetable_from_mfn(pgd_mfn)));
            break;
        default:
            gdprintk(XENLOG_ERR VTDPREFIX,
                     "iommu_set_pgd:Unsupported p2m table sharing level!\n");
            break;
        }
    }
#endif
    gdprintk(XENLOG_INFO VTDPREFIX,
             "iommu_set_pgd: hd->pgd = %p\n", hd->pgd);
}


u8 iommu_state[MAX_IOMMU_REGS * MAX_IOMMUS];
int iommu_suspend(void)
{
    struct acpi_drhd_unit *drhd;
    struct iommu *iommu;
    int i = 0;

    iommu_flush_all();

    for_each_drhd_unit ( drhd )
    {
        iommu = drhd->iommu;
        iommu_state[DMAR_RTADDR_REG * i] =
            (u64) dmar_readq(iommu->reg, DMAR_RTADDR_REG);
        iommu_state[DMAR_FECTL_REG * i] =
            (u32) dmar_readl(iommu->reg, DMAR_FECTL_REG);
        iommu_state[DMAR_FEDATA_REG * i] =
            (u32) dmar_readl(iommu->reg, DMAR_FEDATA_REG);
        iommu_state[DMAR_FEADDR_REG * i] =
            (u32) dmar_readl(iommu->reg, DMAR_FEADDR_REG);
        iommu_state[DMAR_FEUADDR_REG * i] =
            (u32) dmar_readl(iommu->reg, DMAR_FEUADDR_REG);
        iommu_state[DMAR_PLMBASE_REG * i] =
            (u32) dmar_readl(iommu->reg, DMAR_PLMBASE_REG);
        iommu_state[DMAR_PLMLIMIT_REG * i] =
            (u32) dmar_readl(iommu->reg, DMAR_PLMLIMIT_REG);
        iommu_state[DMAR_PHMBASE_REG * i] =
            (u64) dmar_readq(iommu->reg, DMAR_PHMBASE_REG);
        iommu_state[DMAR_PHMLIMIT_REG * i] =
            (u64) dmar_readq(iommu->reg, DMAR_PHMLIMIT_REG);
        i++;
    }

    return 0;
}

int iommu_resume(void)
{
    struct acpi_drhd_unit *drhd;
    struct iommu *iommu;
    int i = 0;

    iommu_flush_all();

    init_vtd_hw();
    for_each_drhd_unit ( drhd )
    {
        iommu = drhd->iommu;
        dmar_writeq( iommu->reg, DMAR_RTADDR_REG,
                     (u64) iommu_state[DMAR_RTADDR_REG * i]);
        dmar_writel(iommu->reg, DMAR_FECTL_REG,
                    (u32) iommu_state[DMAR_FECTL_REG * i]);
        dmar_writel(iommu->reg, DMAR_FEDATA_REG,
                    (u32) iommu_state[DMAR_FEDATA_REG * i]);
        dmar_writel(iommu->reg, DMAR_FEADDR_REG,
                    (u32) iommu_state[DMAR_FEADDR_REG * i]);
        dmar_writel(iommu->reg, DMAR_FEUADDR_REG,
                    (u32) iommu_state[DMAR_FEUADDR_REG * i]);
        dmar_writel(iommu->reg, DMAR_PLMBASE_REG,
                    (u32) iommu_state[DMAR_PLMBASE_REG * i]);
        dmar_writel(iommu->reg, DMAR_PLMLIMIT_REG,
                    (u32) iommu_state[DMAR_PLMLIMIT_REG * i]);
        dmar_writeq(iommu->reg, DMAR_PHMBASE_REG,
                    (u64) iommu_state[DMAR_PHMBASE_REG * i]);
        dmar_writeq(iommu->reg, DMAR_PHMLIMIT_REG,
                    (u64) iommu_state[DMAR_PHMLIMIT_REG * i]);

        if ( iommu_enable_translation(iommu) )
            return -EIO;
        i++;
    }
    return 0;
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
