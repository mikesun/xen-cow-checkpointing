/*
 * hpet.c: HPET emulation for HVM guests.
 * Copyright (c) 2006, Intel Corporation.
 * Copyright (c) 2006, Keir Fraser <keir@xensource.com>
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

#include <asm/hvm/vpt.h>
#include <asm/hvm/io.h>
#include <asm/hvm/support.h>
#include <asm/current.h>
#include <xen/sched.h>
#include <xen/event.h>

#define HPET_BASE_ADDRESS   0xfed00000ULL
#define HPET_MMAP_SIZE      1024
#define S_TO_NS  1000000000ULL           /* 1s  = 10^9  ns */
#define S_TO_FS  1000000000000000ULL     /* 1s  = 10^15 fs */

/* Frequency_of_TSC / frequency_of_HPET = 32 */
#define TSC_PER_HPET_TICK 32
#define guest_time_hpet(v) (hvm_get_guest_time(v) / TSC_PER_HPET_TICK)

#define HPET_ID         0x000
#define HPET_PERIOD     0x004
#define HPET_CFG        0x010
#define HPET_STATUS     0x020
#define HPET_COUNTER    0x0f0
#define HPET_T0_CFG     0x100
#define HPET_T0_CMP     0x108
#define HPET_T0_ROUTE   0x110
#define HPET_T1_CFG     0x120
#define HPET_T1_CMP     0x128
#define HPET_T1_ROUTE   0x130
#define HPET_T2_CFG     0x140
#define HPET_T2_CMP     0x148
#define HPET_T2_ROUTE   0x150
#define HPET_T3_CFG     0x160

#define HPET_CFG_ENABLE          0x001
#define HPET_CFG_LEGACY          0x002

#define HPET_TN_INT_TYPE_LEVEL   0x002
#define HPET_TN_ENABLE           0x004
#define HPET_TN_PERIODIC         0x008
#define HPET_TN_PERIODIC_CAP     0x010
#define HPET_TN_SIZE_CAP         0x020
#define HPET_TN_SETVAL           0x040
#define HPET_TN_32BIT            0x100
#define HPET_TN_INT_ROUTE_MASK  0x3e00
#define HPET_TN_INT_ROUTE_SHIFT      9
#define HPET_TN_INT_ROUTE_CAP_SHIFT 32
#define HPET_TN_CFG_BITS_READONLY_OR_RESERVED 0xffff80b1U

/* can be routed to IOAPIC.redirect_table[23..20] */
#define HPET_TN_INT_ROUTE_CAP      (0x00f00000ULL \
                    << HPET_TN_INT_ROUTE_CAP_SHIFT) 

#define HPET_TN_INT_ROUTE_CAP_MASK (0xffffffffULL \
                    << HPET_TN_INT_ROUTE_CAP_SHIFT)

#define hpet_tick_to_ns(h, tick)                        \
    ((s_time_t)((((tick) > (h)->hpet_to_ns_limit) ?     \
        ~0ULL : (tick) * (h)->hpet_to_ns_scale) >> 10))

#define timer_config(h, n)       (h->hpet.timers[n].config)
#define timer_is_periodic(h, n)  (timer_config(h, n) & HPET_TN_PERIODIC)
#define timer_is_32bit(h, n)     (timer_config(h, n) & HPET_TN_32BIT)
#define hpet_enabled(h)          (h->hpet.config & HPET_CFG_ENABLE)
#define timer_level(h, n)        (timer_config(h, n) & HPET_TN_INT_TYPE_LEVEL)

#define timer_int_route(h, n)   \
    ((timer_config(h, n) & HPET_TN_INT_ROUTE_MASK) >> HPET_TN_INT_ROUTE_SHIFT)

#define timer_int_route_cap(h, n)   \
    ((timer_config(h, n) & HPET_TN_INT_ROUTE_CAP_MASK) \
        >> HPET_TN_INT_ROUTE_CAP_SHIFT)

#define hpet_time_after(a, b)   ((int32_t)(b) - (int32_t)(a) < 0)
#define hpet_time_after64(a, b) ((int64_t)(b) - (int64_t)(a) < 0)

static inline uint64_t hpet_read64(HPETState *h, unsigned long addr)
{
    addr &= ~7;

    switch ( addr )
    {
    case HPET_ID:
        return h->hpet.capability;
    case HPET_CFG:
        return h->hpet.config;
    case HPET_STATUS:
        return h->hpet.isr;
    case HPET_COUNTER:
        return h->hpet.mc64;
    case HPET_T0_CFG:
    case HPET_T1_CFG:
    case HPET_T2_CFG:
        return h->hpet.timers[(addr - HPET_T0_CFG) >> 5].config;
    case HPET_T0_CMP:
    case HPET_T1_CMP:
    case HPET_T2_CMP:
        return h->hpet.timers[(addr - HPET_T0_CMP) >> 5].cmp;
    case HPET_T0_ROUTE:
    case HPET_T1_ROUTE:
    case HPET_T2_ROUTE:
        return h->hpet.timers[(addr - HPET_T0_ROUTE) >> 5].fsb;
    }

    return 0;
}

static inline int hpet_check_access_length(
    unsigned long addr, unsigned long len)
{
    if ( (addr & (len - 1)) || (len > 8) )
    {
        /*
         * According to ICH9 specification, unaligned accesses may result
         * in unexpected behaviour or master abort, but should not crash/hang.
         * Hence we read all-ones, drop writes, and log a warning.
         */
        gdprintk(XENLOG_WARNING, "HPET: access across register boundary: "
                 "%lx %lx\n", addr, len);
        return -EINVAL;
    }

    return 0;
}

static inline uint64_t hpet_read_maincounter(HPETState *h)
{
    ASSERT(spin_is_locked(&h->lock));

    if ( hpet_enabled(h) )
        return guest_time_hpet(h->vcpu) + h->mc_offset;
    else 
        return h->hpet.mc64;
}

static unsigned long hpet_read(
    struct vcpu *v, unsigned long addr, unsigned long length)
{
    HPETState *h = &v->domain->arch.hvm_domain.pl_time.vhpet;
    unsigned long result;
    uint64_t val;

    addr &= HPET_MMAP_SIZE-1;

    if ( hpet_check_access_length(addr, length) != 0 )
        return ~0UL;

    spin_lock(&h->lock);

    val = hpet_read64(h, addr);
    if ( (addr & ~7) == HPET_COUNTER )
        val = hpet_read_maincounter(h);

    result = val;
    if ( length != 8 )
        result = (val >> ((addr & 7) * 8)) & ((1ULL << (length * 8)) - 1);

    spin_unlock(&h->lock);

    return result;
}

static void hpet_stop_timer(HPETState *h, unsigned int tn)
{
    ASSERT(tn < HPET_TIMER_NUM);
    ASSERT(spin_is_locked(&h->lock));
    stop_timer(&h->timers[tn]);
}

/* the number of HPET tick that stands for
 * 1/(2^10) second, namely, 0.9765625 milliseconds */
#define  HPET_TINY_TIME_SPAN  ((h->tsc_freq >> 10) / TSC_PER_HPET_TICK)

static void hpet_set_timer(HPETState *h, unsigned int tn)
{
    uint64_t tn_cmp, cur_tick, diff;

    ASSERT(tn < HPET_TIMER_NUM);
    ASSERT(spin_is_locked(&h->lock));

    if ( (tn == 0) && (h->hpet.config & HPET_CFG_LEGACY) )
    {
        /* HPET specification requires PIT shouldn't generate
         * interrupts if LegacyReplacementRoute is set for timer0 */
        PITState *pit = &h->vcpu->domain->arch.hvm_domain.pl_time.vpit;
        pit_stop_channel0_irq(pit);
    }

    tn_cmp   = h->hpet.timers[tn].cmp;
    cur_tick = hpet_read_maincounter(h);
    if ( timer_is_32bit(h, tn) )
    {
        tn_cmp   = (uint32_t)tn_cmp;
        cur_tick = (uint32_t)cur_tick;
    }

    diff = tn_cmp - cur_tick;

    /*
     * Detect time values set in the past. This is hard to do for 32-bit
     * comparators as the timer does not have to be set that far in the future
     * for the counter difference to wrap a 32-bit signed integer. We fudge
     * by looking for a 'small' time value in the past.
     */
    if ( (int64_t)diff < 0 )
        diff = (timer_is_32bit(h, tn) && (-diff > HPET_TINY_TIME_SPAN))
            ? (uint32_t)diff : 0;

    set_timer(&h->timers[tn], NOW() + hpet_tick_to_ns(h, diff));
}

static inline uint64_t hpet_fixup_reg(
    uint64_t new, uint64_t old, uint64_t mask)
{
    new &= mask;
    new |= old & ~mask;
    return new;
}

static void hpet_write(
    struct vcpu *v, unsigned long addr,
    unsigned long length, unsigned long val)
{
    HPETState *h = &v->domain->arch.hvm_domain.pl_time.vhpet;
    uint64_t old_val, new_val;
    int tn, i;

    addr &= HPET_MMAP_SIZE-1;

    if ( hpet_check_access_length(addr, length) != 0 )
        return;

    spin_lock(&h->lock);

    old_val = hpet_read64(h, addr);
    if ( (addr & ~7) == HPET_COUNTER )
        old_val = hpet_read_maincounter(h);

    new_val = val;
    if ( length != 8 )
        new_val = hpet_fixup_reg(
            new_val << (addr & 7) * 8, old_val,
            ((1ULL << (length*8)) - 1) << ((addr & 7) * 8));

    switch ( addr & ~7 )
    {
    case HPET_CFG:
        h->hpet.config = hpet_fixup_reg(new_val, old_val, 0x3);

        if ( !(old_val & HPET_CFG_ENABLE) && (new_val & HPET_CFG_ENABLE) )
        {
            /* Enable main counter and interrupt generation. */
            h->mc_offset = h->hpet.mc64 - guest_time_hpet(h->vcpu);
            for ( i = 0; i < HPET_TIMER_NUM; i++ )
                hpet_set_timer(h, i); 
        }
        else if ( (old_val & HPET_CFG_ENABLE) && !(new_val & HPET_CFG_ENABLE) )
        {
            /* Halt main counter and disable interrupt generation. */
            h->hpet.mc64 = h->mc_offset + guest_time_hpet(h->vcpu);
            for ( i = 0; i < HPET_TIMER_NUM; i++ )
                hpet_stop_timer(h, i);
        }
        break;

    case HPET_COUNTER:
        if ( hpet_enabled(h) )
            gdprintk(XENLOG_WARNING, 
                     "HPET: writing main counter but it's not halted!\n");
        h->hpet.mc64 = new_val;
        break;

    case HPET_T0_CFG:
    case HPET_T1_CFG:
    case HPET_T2_CFG:
        tn = (addr - HPET_T0_CFG) >> 5;

        h->hpet.timers[tn].config = hpet_fixup_reg(new_val, old_val, 0x3f4e);

        if ( timer_level(h, tn) )
        {
            gdprintk(XENLOG_ERR,
                     "HPET: level triggered interrupt not supported now\n");
            domain_crash(current->domain);
            break;
        }

        if ( new_val & HPET_TN_32BIT )
        {
            h->hpet.timers[tn].cmp = (uint32_t)h->hpet.timers[tn].cmp;
            h->hpet.period[tn] = (uint32_t)h->hpet.period[tn];
        }

        break;

    case HPET_T0_CMP:
    case HPET_T1_CMP:
    case HPET_T2_CMP:
        tn = (addr - HPET_T0_CMP) >> 5;
        if ( timer_is_32bit(h, tn) )
            new_val = (uint32_t)new_val;
        if ( !timer_is_periodic(h, tn) ||
             (h->hpet.timers[tn].config & HPET_TN_SETVAL) )
            h->hpet.timers[tn].cmp = new_val;
        else
        {
            /*
             * Clamp period to reasonable min/max values:
             *  - minimum is 900us, same as timers controlled by vpt.c
             *  - maximum is to prevent overflow in time_after() calculations
             */
            if ( hpet_tick_to_ns(h, new_val) < MICROSECS(900) )
                new_val = (MICROSECS(900) << 10) / h->hpet_to_ns_scale;
            new_val &= (timer_is_32bit(h, tn) ? ~0u : ~0ull) >> 1;
            h->hpet.period[tn] = new_val;
        }
        h->hpet.timers[tn].config &= ~HPET_TN_SETVAL;
        if ( hpet_enabled(h) )
            hpet_set_timer(h, tn);
        break;

    case HPET_T0_ROUTE:
    case HPET_T1_ROUTE:
    case HPET_T2_ROUTE:
        tn = (addr - HPET_T0_ROUTE) >> 5;
        h->hpet.timers[tn].fsb = new_val;
        break;

    default:
        /* Ignore writes to unsupported and reserved registers. */
        break;
    }

    spin_unlock(&h->lock);
}

static int hpet_range(struct vcpu *v, unsigned long addr)
{
    return ((addr >= HPET_BASE_ADDRESS) &&
            (addr < (HPET_BASE_ADDRESS + HPET_MMAP_SIZE)));
}

struct hvm_mmio_handler hpet_mmio_handler = {
    .check_handler = hpet_range,
    .read_handler  = hpet_read,
    .write_handler = hpet_write
};

static void hpet_route_interrupt(HPETState *h, unsigned int tn)
{
    unsigned int tn_int_route = timer_int_route(h, tn);
    struct domain *d = h->vcpu->domain;

    ASSERT(spin_is_locked(&h->lock));

    if ( (tn <= 1) && (h->hpet.config & HPET_CFG_LEGACY) )
    {
        /* if LegacyReplacementRoute bit is set, HPET specification requires
           timer0 be routed to IRQ0 in NON-APIC or IRQ2 in the I/O APIC,
           timer1 be routed to IRQ8 in NON-APIC or IRQ8 in the I/O APIC. */
        int isa_irq = (tn == 0) ? 0 : 8;
        hvm_isa_irq_deassert(d, isa_irq);
        hvm_isa_irq_assert(d, isa_irq);
        return;
    }

    if ( !(timer_int_route_cap(h, tn) & (1U << tn_int_route)) )
    {
        gdprintk(XENLOG_ERR,
                 "HPET: timer%u: invalid interrupt route config\n", tn);
        domain_crash(d);
        return;
    }

    /* We support only edge-triggered interrupt. */
    spin_lock(&d->arch.hvm_domain.irq_lock);
    vioapic_irq_positive_edge(d, tn_int_route);
    spin_unlock(&d->arch.hvm_domain.irq_lock);
}

static void hpet_timer_fn(void *opaque)
{
    struct HPET_timer_fn_info *htfi = opaque;
    HPETState *h = htfi->hs;
    unsigned int tn = htfi->tn;

    spin_lock(&h->lock);

    if ( !hpet_enabled(h) )
    {
        spin_unlock(&h->lock);
        return;
    }

    if ( timer_config(h, tn) & HPET_TN_ENABLE )
        hpet_route_interrupt(h, tn);

    if ( timer_is_periodic(h, tn) && (h->hpet.period[tn] != 0) )
    {
        uint64_t mc = hpet_read_maincounter(h), period = h->hpet.period[tn];
        if ( timer_is_32bit(h, tn) )
        {
            while ( hpet_time_after(mc, h->hpet.timers[tn].cmp) )
                h->hpet.timers[tn].cmp = (uint32_t)(
                    h->hpet.timers[tn].cmp + period);
        }
        else
        {
            while ( hpet_time_after64(mc, h->hpet.timers[tn].cmp) )
                h->hpet.timers[tn].cmp += period;
        }
        set_timer(&h->timers[tn], NOW() + hpet_tick_to_ns(h, period));
    }

    spin_unlock(&h->lock);
}

void hpet_migrate_timers(struct vcpu *v)
{
    struct HPETState *h = &v->domain->arch.hvm_domain.pl_time.vhpet;
    int i;

    if ( v != h->vcpu )
        return;

    for ( i = 0; i < HPET_TIMER_NUM; i++ )
        migrate_timer(&h->timers[i], v->processor);
}

static int hpet_save(struct domain *d, hvm_domain_context_t *h)
{
    HPETState *hp = &d->arch.hvm_domain.pl_time.vhpet;
    int rc;

    spin_lock(&hp->lock);

    /* Write the proper value into the main counter */
    hp->hpet.mc64 = hp->mc_offset + guest_time_hpet(hp->vcpu);

    /* Save the HPET registers */
    rc = _hvm_init_entry(h, HVM_SAVE_CODE(HPET), 0, HVM_SAVE_LENGTH(HPET));
    if ( rc == 0 )
    {
        struct hvm_hw_hpet *rec = (struct hvm_hw_hpet *)&h->data[h->cur];
        h->cur += HVM_SAVE_LENGTH(HPET);
        memset(rec, 0, HVM_SAVE_LENGTH(HPET));
#define C(x) rec->x = hp->hpet.x
        C(capability);
        C(config);
        C(isr);
        C(mc64);
        C(timers[0].config);
        C(timers[0].cmp);
        C(timers[0].fsb);
        C(timers[1].config);
        C(timers[1].cmp);
        C(timers[1].fsb);
        C(timers[2].config);
        C(timers[2].cmp);
        C(timers[2].fsb);
        C(period[0]);
        C(period[1]);
        C(period[2]);
#undef C
    }

    spin_unlock(&hp->lock);

    return rc;
}

static int hpet_load(struct domain *d, hvm_domain_context_t *h)
{
    HPETState *hp = &d->arch.hvm_domain.pl_time.vhpet;
    struct hvm_hw_hpet *rec;
    int i;

    spin_lock(&hp->lock);

    /* Reload the HPET registers */
    if ( _hvm_check_entry(h, HVM_SAVE_CODE(HPET), HVM_SAVE_LENGTH(HPET)) )
    {
        spin_unlock(&hp->lock);
        return -EINVAL;
    }

    rec = (struct hvm_hw_hpet *)&h->data[h->cur];
    h->cur += HVM_SAVE_LENGTH(HPET);

#define C(x) hp->hpet.x = rec->x
        C(capability);
        C(config);
        C(isr);
        C(mc64);
        C(timers[0].config);
        C(timers[0].cmp);
        C(timers[0].fsb);
        C(timers[1].config);
        C(timers[1].cmp);
        C(timers[1].fsb);
        C(timers[2].config);
        C(timers[2].cmp);
        C(timers[2].fsb);
        C(period[0]);
        C(period[1]);
        C(period[2]);
#undef C
    
    /* Recalculate the offset between the main counter and guest time */
    hp->mc_offset = hp->hpet.mc64 - guest_time_hpet(hp->vcpu);
                
    /* Restart the timers */
    for ( i = 0; i < HPET_TIMER_NUM; i++ )
        if ( hpet_enabled(hp) )
            hpet_set_timer(hp, i);

    spin_unlock(&hp->lock);

    return 0;
}

HVM_REGISTER_SAVE_RESTORE(HPET, hpet_save, hpet_load, 1, HVMSR_PER_DOM);

void hpet_init(struct vcpu *v)
{
    HPETState *h = &v->domain->arch.hvm_domain.pl_time.vhpet;
    int i;

    memset(h, 0, sizeof(HPETState));

    spin_lock_init(&h->lock);

    h->vcpu = v;
    h->tsc_freq = ticks_per_sec(v);

    h->hpet_to_ns_scale = ((S_TO_NS * TSC_PER_HPET_TICK) << 10) / h->tsc_freq;
    h->hpet_to_ns_limit = ~0ULL / h->hpet_to_ns_scale;

    /* 64-bit main counter; 3 timers supported; LegacyReplacementRoute. */
    h->hpet.capability = 0x8086A201ULL;

    /* This is the number of femptoseconds per HPET tick. */
    /* Here we define HPET's frequency to be 1/32 of the TSC's */
    h->hpet.capability |= ((S_TO_FS*TSC_PER_HPET_TICK/h->tsc_freq) << 32);

    for ( i = 0; i < HPET_TIMER_NUM; i++ )
    {
        h->hpet.timers[i].config = 
            HPET_TN_INT_ROUTE_CAP | HPET_TN_SIZE_CAP | HPET_TN_PERIODIC_CAP;
        h->hpet.timers[i].cmp = ~0ULL;
        h->timer_fn_info[i].hs = h;
        h->timer_fn_info[i].tn = i;
        init_timer(&h->timers[i], hpet_timer_fn, &h->timer_fn_info[i],
                   v->processor);
    }
}

void hpet_deinit(struct domain *d)
{
    int i;
    HPETState *h = &d->arch.hvm_domain.pl_time.vhpet;

    for ( i = 0; i < HPET_TIMER_NUM; i++ )
        kill_timer(&h->timers[i]);
}

