#ifndef __ASM_DOMAIN_H__
#define __ASM_DOMAIN_H__

#include <xen/config.h>
#include <xen/mm.h>
#include <asm/hvm/vcpu.h>
#include <asm/hvm/domain.h>
#include <asm/e820.h>

#define has_32bit_shinfo(d)    ((d)->arch.has_32bit_shinfo)
#define is_pv_32bit_domain(d)  ((d)->arch.is_32bit_pv)
#define is_pv_32bit_vcpu(v)    (is_pv_32bit_domain((v)->domain))
#ifdef __x86_64__
#define is_pv_32on64_domain(d) (is_pv_32bit_domain(d))
#else
#define is_pv_32on64_domain(d) (0)
#endif
#define is_pv_32on64_vcpu(v)   (is_pv_32on64_domain((v)->domain))
#define IS_COMPAT(d)           (is_pv_32on64_domain(d))

struct trap_bounce {
    uint32_t      error_code;
    uint8_t       flags; /* TBF_ */
    uint16_t      cs;
    unsigned long eip;
};

#define MAPHASH_ENTRIES 8
#define MAPHASH_HASHFN(pfn) ((pfn) & (MAPHASH_ENTRIES-1))
#define MAPHASHENT_NOTINUSE ((u16)~0U)
struct mapcache_vcpu {
    /* Shadow of mapcache_domain.epoch. */
    unsigned int shadow_epoch;

    /* Lock-free per-VCPU hash of recently-used mappings. */
    struct vcpu_maphash_entry {
        unsigned long mfn;
        uint16_t      idx;
        uint16_t      refcnt;
    } hash[MAPHASH_ENTRIES];
};

#define MAPCACHE_ORDER   10
#define MAPCACHE_ENTRIES (1 << MAPCACHE_ORDER)
struct mapcache_domain {
    /* The PTEs that provide the mappings, and a cursor into the array. */
    l1_pgentry_t *l1tab;
    unsigned int cursor;

    /* Protects map_domain_page(). */
    spinlock_t lock;

    /* Garbage mappings are flushed from TLBs in batches called 'epochs'. */
    unsigned int epoch;
    u32 tlbflush_timestamp;

    /* Which mappings are in use, and which are garbage to reap next epoch? */
    unsigned long inuse[BITS_TO_LONGS(MAPCACHE_ENTRIES)];
    unsigned long garbage[BITS_TO_LONGS(MAPCACHE_ENTRIES)];
};

void mapcache_domain_init(struct domain *);
void mapcache_vcpu_init(struct vcpu *);

/* x86/64: toggle guest between kernel and user modes. */
void toggle_guest_mode(struct vcpu *);

/*
 * Initialise a hypercall-transfer page. The given pointer must be mapped
 * in Xen virtual address space (accesses are not validated or checked).
 */
void hypercall_page_initialise(struct domain *d, void *);

/************************************************/
/*          shadow paging extension             */
/************************************************/
struct shadow_domain {
    spinlock_t        lock;  /* shadow domain lock */
    int               locker; /* processor which holds the lock */
    const char       *locker_function; /* Func that took it */
    unsigned int      opt_flags;    /* runtime tunable optimizations on/off */
    struct list_head  pinned_shadows;

    /* Memory allocation */
    struct list_head  freelists[SHADOW_MAX_ORDER + 1];
    struct list_head  p2m_freelist;
    unsigned int      total_pages;  /* number of pages allocated */
    unsigned int      free_pages;   /* number of pages on freelists */
    unsigned int      p2m_pages;    /* number of pages allocates to p2m */

    /* 1-to-1 map for use when HVM vcpus have paging disabled */
    pagetable_t unpaged_pagetable;

    /* Shadow hashtable */
    struct shadow_page_info **hash_table;
    int hash_walking;  /* Some function is walking the hash table */

    /* Fast MMIO path heuristic */
    int has_fast_mmio_entries;
};

struct shadow_vcpu {
#if CONFIG_PAGING_LEVELS >= 3
    /* PAE guests: per-vcpu shadow top-level table */
    l3_pgentry_t l3table[4] __attribute__((__aligned__(32)));
    /* PAE guests: per-vcpu cache of the top-level *guest* entries */
    l3_pgentry_t gl3e[4] __attribute__((__aligned__(32)));
#endif
    /* Non-PAE guests: pointer to guest top-level pagetable */
    void *guest_vtable;
    /* Last MFN that we emulated a write to. */
    unsigned long last_emulated_mfn;
    /* MFN of the last shadow that we shot a writeable mapping in */
    unsigned long last_writeable_pte_smfn;
};

/************************************************/
/*            hardware assisted paging          */
/************************************************/
struct hap_domain {
    spinlock_t        lock;
    int               locker;
    const char       *locker_function;

    struct list_head  freelist;
    unsigned int      total_pages;  /* number of pages allocated */
    unsigned int      free_pages;   /* number of pages on freelists */
    unsigned int      p2m_pages;    /* number of pages allocates to p2m */
};

/************************************************/
/*       p2m handling                           */
/************************************************/
struct p2m_domain {
    /* Lock that protects updates to the p2m */
    spinlock_t         lock;
    int                locker;   /* processor which holds the lock */
    const char        *locker_function; /* Func that took it */

    /* Pages used to construct the p2m */
    struct list_head   pages;

    /* Functions to call to get or free pages for the p2m */
    struct page_info * (*alloc_page  )(struct domain *d);
    void               (*free_page   )(struct domain *d,
                                       struct page_info *pg);

    /* Highest guest frame that's ever been mapped in the p2m */
    unsigned long max_mapped_pfn;
};

/************************************************/
/*       common paging data structure           */
/************************************************/
struct log_dirty_domain {
    /* log-dirty lock */
    spinlock_t     lock;
    int            locker; /* processor that holds the lock */
    const char    *locker_function; /* func that took it */

    /* log-dirty radix tree to record dirty pages */
    mfn_t          top;
    unsigned int   allocs;
    unsigned int   failed_allocs;

    /* log-dirty mode stats */
    unsigned int   fault_count;
    unsigned int   dirty_count;

    /* functions which are paging mode specific */
    int            (*enable_log_dirty   )(struct domain *d);
    int            (*disable_log_dirty  )(struct domain *d);
    void           (*clean_dirty_bitmap )(struct domain *d);
};

struct paging_domain {
    /* flags to control paging operation */
    u32                     mode;
    /* extension for shadow paging support */
    struct shadow_domain    shadow;
    /* extension for hardware-assited paging */
    struct hap_domain       hap;
    /* log dirty support */
    struct log_dirty_domain log_dirty;
};

struct paging_vcpu {
    /* Pointers to mode-specific entry points. */
    struct paging_mode *mode;
    /* HVM guest: last emulate was to a pagetable */
    unsigned int last_write_was_pt:1;
    /* Translated guest: virtual TLB */
    struct shadow_vtlb *vtlb;
    spinlock_t          vtlb_lock;

    /* paging support extension */
    struct shadow_vcpu shadow;
};

struct arch_domain
{
    l1_pgentry_t *mm_perdomain_pt;
#ifdef CONFIG_X86_64
    l2_pgentry_t *mm_perdomain_l2;
    l3_pgentry_t *mm_perdomain_l3;
#endif

#ifdef CONFIG_X86_32
    /* map_domain_page() mapping cache. */
    struct mapcache_domain mapcache;
#endif

#ifdef CONFIG_COMPAT
    unsigned int hv_compat_vstart;
    l3_pgentry_t *mm_arg_xlat_l3;
#endif

    /* I/O-port admin-specified access capabilities. */
    struct rangeset *ioport_caps;

    struct hvm_domain hvm_domain;

    struct paging_domain paging;
    struct p2m_domain p2m ;

    /* Shadow translated domain: P2M mapping */
    pagetable_t phys_table;

    /* Pseudophysical e820 map (XENMEM_memory_map).  */
    struct e820entry e820[3];
    unsigned int nr_e820;

    /* Maximum physical-address bitwidth supported by this guest. */
    unsigned int physaddr_bitsize;

    /* Is a 32-bit PV (non-HVM) guest? */
    bool_t is_32bit_pv;
    /* Is shared-info page in 32-bit format? */
    bool_t has_32bit_shinfo;

    /* Continuable domain_relinquish_resources(). */
    enum {
        RELMEM_not_started,
        RELMEM_xen_l4,
        RELMEM_dom_l4,
        RELMEM_xen_l3,
        RELMEM_dom_l3,
        RELMEM_xen_l2,
        RELMEM_dom_l2,
        RELMEM_done,
    } relmem;
    struct list_head relmem_list;
} __cacheline_aligned;

#ifdef CONFIG_X86_PAE
struct pae_l3_cache {
    /*
     * Two low-memory (<4GB) PAE L3 tables, used as fallback when the guest
     * supplies a >=4GB PAE L3 table. We need two because we cannot set up
     * an L3 table while we are currently running on it (without using
     * expensive atomic 64-bit operations).
     */
    l3_pgentry_t  table[2][4] __attribute__((__aligned__(32)));
    unsigned long high_mfn;  /* The >=4GB MFN being shadowed. */
    unsigned int  inuse_idx; /* Which of the two cache slots is in use? */
    spinlock_t    lock;
};
#define pae_l3_cache_init(c) spin_lock_init(&(c)->lock)
#else /* !CONFIG_X86_PAE */
struct pae_l3_cache { };
#define pae_l3_cache_init(c) ((void)0)
#endif

struct arch_vcpu
{
    /* Needs 16-byte aligment for FXSAVE/FXRSTOR. */
    struct vcpu_guest_context guest_context
    __attribute__((__aligned__(16)));

    struct pae_l3_cache pae_l3_cache;

    unsigned long      flags; /* TF_ */

    void (*schedule_tail) (struct vcpu *);

    void (*ctxt_switch_from) (struct vcpu *);
    void (*ctxt_switch_to) (struct vcpu *);

    /* Record information required to continue execution after migration */
    void *continue_info;

    /* Bounce information for propagating an exception to guest OS. */
    struct trap_bounce trap_bounce;

    /* I/O-port access bitmap. */
    XEN_GUEST_HANDLE(uint8) iobmp; /* Guest kernel vaddr of the bitmap. */
    int iobmp_limit;  /* Number of ports represented in the bitmap.  */
    int iopl;         /* Current IOPL for this VCPU. */

#ifdef CONFIG_X86_32
    struct desc_struct int80_desc;
#endif
#ifdef CONFIG_X86_64
    struct trap_bounce int80_bounce;
    unsigned long      syscall32_callback_eip;
    unsigned long      sysenter_callback_eip;
    unsigned short     syscall32_callback_cs;
    unsigned short     sysenter_callback_cs;
    bool_t             syscall32_disables_events;
    bool_t             sysenter_disables_events;
#endif

    /* Virtual Machine Extensions */
    struct hvm_vcpu hvm_vcpu;

    /*
     * Every domain has a L1 pagetable of its own. Per-domain mappings
     * are put in this table (eg. the current GDT is mapped here).
     */
    l1_pgentry_t *perdomain_ptes;

#ifdef CONFIG_X86_64
    pagetable_t guest_table_user;       /* (MFN) x86/64 user-space pagetable */
#endif
    pagetable_t guest_table;            /* (MFN) guest notion of cr3 */
    /* guest_table holds a ref to the page, and also a type-count unless
     * shadow refcounts are in use */
    pagetable_t shadow_table[4];        /* (MFN) shadow(s) of guest */
    pagetable_t monitor_table;          /* (MFN) hypervisor PT (for HVM) */
    unsigned long cr3;                  /* (MA) value to install in HW CR3 */

    /* Current LDT details. */
    unsigned long shadow_ldt_mapcnt;

    struct paging_vcpu paging;

    /* Guest-specified relocation of vcpu_info. */
    unsigned long vcpu_info_mfn;

#ifdef CONFIG_X86_32
    /* map_domain_page() mapping cache. */
    struct mapcache_vcpu mapcache;
#endif

} __cacheline_aligned;

/* Shorthands to improve code legibility. */
#define hvm_vmx         hvm_vcpu.u.vmx
#define hvm_svm         hvm_vcpu.u.svm

/* Continue the current hypercall via func(data) on specified cpu. */
int continue_hypercall_on_cpu(int cpu, long (*func)(void *data), void *data);

/* Clean up CR4 bits that are not under guest control. */
unsigned long pv_guest_cr4_fixup(unsigned long guest_cr4);

/* Convert between guest-visible and real CR4 values. */
#define pv_guest_cr4_to_real_cr4(c) \
    (((c) | (mmu_cr4_features & (X86_CR4_PGE | X86_CR4_PSE))) & ~X86_CR4_DE)
#define real_cr4_to_pv_guest_cr4(c) \
    ((c) & ~(X86_CR4_PGE | X86_CR4_PSE))

#endif /* __ASM_DOMAIN_H__ */

/*
 * Local variables:
 * mode: C
 * c-set-style: "BSD"
 * c-basic-offset: 4
 * tab-width: 4
 * indent-tabs-mode: nil
 * End:
 */
