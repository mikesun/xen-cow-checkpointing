/*
 *	x86 SMP booting functions
 *
 *	(c) 1995 Alan Cox, Building #3 <alan@redhat.com>
 *	(c) 1998, 1999, 2000 Ingo Molnar <mingo@redhat.com>
 *
 *	Much of the core SMP work is based on previous work by Thomas Radke, to
 *	whom a great many thanks are extended.
 *
 *	Thanks to Intel for making available several different Pentium,
 *	Pentium Pro and Pentium-II/Xeon MP machines.
 *	Original development of Linux SMP code supported by Caldera.
 *
 *	This code is released under the GNU General Public License version 2 or
 *	later.
 *
 *	Fixes
 *		Felix Koop	:	NR_CPUS used properly
 *		Jose Renau	:	Handle single CPU case.
 *		Alan Cox	:	By repeated request 8) - Total BogoMIPS report.
 *		Greg Wright	:	Fix for kernel stacks panic.
 *		Erich Boleyn	:	MP v1.4 and additional changes.
 *	Matthias Sattler	:	Changes for 2.1 kernel map.
 *	Michel Lespinasse	:	Changes for 2.1 kernel map.
 *	Michael Chastain	:	Change trampoline.S to gnu as.
 *		Alan Cox	:	Dumb bug: 'B' step PPro's are fine
 *		Ingo Molnar	:	Added APIC timers, based on code
 *					from Jose Renau
 *		Ingo Molnar	:	various cleanups and rewrites
 *		Tigran Aivazian	:	fixed "0.00 in /proc/uptime on SMP" bug.
 *	Maciej W. Rozycki	:	Bits for genuine 82489DX APICs
 *		Martin J. Bligh	: 	Added support for multi-quad systems
 *		Dave Jones	:	Report invalid combinations of Athlon CPUs.
*		Rusty Russell	:	Hacked into shape for new "hotplug" boot process. */

#include <xen/config.h>
#include <xen/init.h>
#include <xen/kernel.h>
#include <xen/mm.h>
#include <xen/domain.h>
#include <xen/sched.h>
#include <xen/irq.h>
#include <xen/delay.h>
#include <xen/softirq.h>
#include <xen/serial.h>
#include <xen/numa.h>
#include <asm/current.h>
#include <asm/mc146818rtc.h>
#include <asm/desc.h>
#include <asm/div64.h>
#include <asm/flushtlb.h>
#include <asm/msr.h>
#include <asm/mtrr.h>
#include <mach_apic.h>
#include <mach_wakecpu.h>
#include <smpboot_hooks.h>

#define set_kernel_exec(x, y) (0)
#define setup_trampoline()    (bootsym_phys(trampoline_realmode_entry))

/* Set if we find a B stepping CPU */
static int __devinitdata smp_b_stepping;

/* Number of siblings per CPU package */
int smp_num_siblings = 1;
#ifdef CONFIG_X86_HT
EXPORT_SYMBOL(smp_num_siblings);
#endif

/* Package ID of each logical CPU */
int phys_proc_id[NR_CPUS] __read_mostly = {[0 ... NR_CPUS-1] = BAD_APICID};

/* Core ID of each logical CPU */
int cpu_core_id[NR_CPUS] __read_mostly = {[0 ... NR_CPUS-1] = BAD_APICID};

/* representing HT siblings of each logical CPU */
cpumask_t cpu_sibling_map[NR_CPUS] __read_mostly;
EXPORT_SYMBOL(cpu_sibling_map);

/* representing HT and core siblings of each logical CPU */
cpumask_t cpu_core_map[NR_CPUS] __read_mostly;
EXPORT_SYMBOL(cpu_core_map);

/* bitmap of online cpus */
cpumask_t cpu_online_map __read_mostly;
EXPORT_SYMBOL(cpu_online_map);

cpumask_t cpu_callin_map;
cpumask_t cpu_callout_map;
EXPORT_SYMBOL(cpu_callout_map);
cpumask_t cpu_possible_map;
EXPORT_SYMBOL(cpu_possible_map);
static cpumask_t smp_commenced_mask;

/* TSC's upper 32 bits can't be written in eariler CPU (before prescott), there
 * is no way to resync one AP against BP. TBD: for prescott and above, we
 * should use IA64's algorithm
 */
static int __devinitdata tsc_sync_disabled;

/* Per CPU bogomips and other parameters */
struct cpuinfo_x86 cpu_data[NR_CPUS] __cacheline_aligned;
EXPORT_SYMBOL(cpu_data);

u8 x86_cpu_to_apicid[NR_CPUS] __read_mostly =
			{ [0 ... NR_CPUS-1] = 0xff };
EXPORT_SYMBOL(x86_cpu_to_apicid);

static void map_cpu_to_logical_apicid(void);
/* State of each CPU. */
DEFINE_PER_CPU(int, cpu_state) = { 0 };

static void *stack_base[NR_CPUS] __cacheline_aligned;
spinlock_t cpu_add_remove_lock;

/*
 * The bootstrap kernel entry code has set these up. Save them for
 * a given CPU
 */

static void __devinit smp_store_cpu_info(int id)
{
	struct cpuinfo_x86 *c = cpu_data + id;

	*c = boot_cpu_data;
	if (id!=0)
		identify_cpu(c);
	/*
	 * Mask B, Pentium, but not Pentium MMX
	 */
	if (c->x86_vendor == X86_VENDOR_INTEL &&
	    c->x86 == 5 &&
	    c->x86_mask >= 1 && c->x86_mask <= 4 &&
	    c->x86_model <= 3)
		/*
		 * Remember we have B step Pentia with bugs
		 */
		smp_b_stepping = 1;

	/*
	 * Certain Athlons might work (for various values of 'work') in SMP
	 * but they are not certified as MP capable.
	 */
	if ((c->x86_vendor == X86_VENDOR_AMD) && (c->x86 == 6)) {

		/* Athlon 660/661 is valid. */	
		if ((c->x86_model==6) && ((c->x86_mask==0) || (c->x86_mask==1)))
			goto valid_k7;

		/* Duron 670 is valid */
		if ((c->x86_model==7) && (c->x86_mask==0))
			goto valid_k7;

		/*
		 * Athlon 662, Duron 671, and Athlon >model 7 have capability bit.
		 * It's worth noting that the A5 stepping (662) of some Athlon XP's
		 * have the MP bit set.
		 * See http://www.heise.de/newsticker/data/jow-18.10.01-000 for more.
		 */
		if (((c->x86_model==6) && (c->x86_mask>=2)) ||
		    ((c->x86_model==7) && (c->x86_mask>=1)) ||
		     (c->x86_model> 7))
			if (cpu_has_mp)
				goto valid_k7;

		/* If we get here, it's not a certified SMP capable AMD system. */
		add_taint(TAINT_UNSAFE_SMP);
	}

valid_k7:
	;
}

/*
 * TSC synchronization.
 *
 * We first check whether all CPUs have their TSC's synchronized,
 * then we print a warning if not, and always resync.
 */

static atomic_t tsc_start_flag = ATOMIC_INIT(0);
static atomic_t tsc_count_start = ATOMIC_INIT(0);
static atomic_t tsc_count_stop = ATOMIC_INIT(0);
static unsigned long long tsc_values[NR_CPUS];

#define NR_LOOPS 5

static void __init synchronize_tsc_bp (void)
{
	int i;
	unsigned long long t0;
	unsigned long long sum, avg;
	long long delta;
	unsigned int one_usec;
	int buggy = 0;

	printk(KERN_INFO "checking TSC synchronization across %u CPUs: ", num_booting_cpus());

	/* convert from kcyc/sec to cyc/usec */
	one_usec = cpu_khz / 1000;

	atomic_set(&tsc_start_flag, 1);
	wmb();

	/*
	 * We loop a few times to get a primed instruction cache,
	 * then the last pass is more or less synchronized and
	 * the BP and APs set their cycle counters to zero all at
	 * once. This reduces the chance of having random offsets
	 * between the processors, and guarantees that the maximum
	 * delay between the cycle counters is never bigger than
	 * the latency of information-passing (cachelines) between
	 * two CPUs.
	 */
	for (i = 0; i < NR_LOOPS; i++) {
		/*
		 * all APs synchronize but they loop on '== num_cpus'
		 */
		while (atomic_read(&tsc_count_start) != num_booting_cpus()-1)
			mb();
		atomic_set(&tsc_count_stop, 0);
		wmb();
		/*
		 * this lets the APs save their current TSC:
		 */
		atomic_inc(&tsc_count_start);

		rdtscll(tsc_values[smp_processor_id()]);
		/*
		 * We clear the TSC in the last loop:
		 */
		if (i == NR_LOOPS-1)
			write_tsc(0, 0);

		/*
		 * Wait for all APs to leave the synchronization point:
		 */
		while (atomic_read(&tsc_count_stop) != num_booting_cpus()-1)
			mb();
		atomic_set(&tsc_count_start, 0);
		wmb();
		atomic_inc(&tsc_count_stop);
	}

	sum = 0;
	for (i = 0; i < NR_CPUS; i++) {
		if (cpu_isset(i, cpu_callout_map)) {
			t0 = tsc_values[i];
			sum += t0;
		}
	}
	avg = sum;
	do_div(avg, num_booting_cpus());

	sum = 0;
	for (i = 0; i < NR_CPUS; i++) {
		if (!cpu_isset(i, cpu_callout_map))
			continue;
		delta = tsc_values[i] - avg;
		if (delta < 0)
			delta = -delta;
		/*
		 * We report bigger than 2 microseconds clock differences.
		 */
		if (delta > 2*one_usec) {
			long realdelta;
			if (!buggy) {
				buggy = 1;
				printk("\n");
			}
			realdelta = delta;
			do_div(realdelta, one_usec);
			if (tsc_values[i] < avg)
				realdelta = -realdelta;

			printk(KERN_INFO "CPU#%d had %ld usecs TSC skew, fixed it up.\n", i, realdelta);
		}

		sum += delta;
	}
	if (!buggy)
		printk("passed.\n");
}

static void __init synchronize_tsc_ap (void)
{
	int i;

	/*
	 * Not every cpu is online at the time
	 * this gets called, so we first wait for the BP to
	 * finish SMP initialization:
	 */
	while (!atomic_read(&tsc_start_flag)) mb();

	for (i = 0; i < NR_LOOPS; i++) {
		atomic_inc(&tsc_count_start);
		while (atomic_read(&tsc_count_start) != num_booting_cpus())
			mb();

		rdtscll(tsc_values[smp_processor_id()]);
		if (i == NR_LOOPS-1)
			write_tsc(0, 0);

		atomic_inc(&tsc_count_stop);
		while (atomic_read(&tsc_count_stop) != num_booting_cpus()) mb();
	}
}
#undef NR_LOOPS

extern void calibrate_delay(void);

static atomic_t init_deasserted;

void __devinit smp_callin(void)
{
	int cpuid, phys_id, i;

	/*
	 * If waken up by an INIT in an 82489DX configuration
	 * we may get here before an INIT-deassert IPI reaches
	 * our local APIC.  We have to wait for the IPI or we'll
	 * lock up on an APIC access.
	 */
	wait_for_init_deassert(&init_deasserted);

	/*
	 * (This works even if the APIC is not enabled.)
	 */
	phys_id = GET_APIC_ID(apic_read(APIC_ID));
	cpuid = smp_processor_id();
	if (cpu_isset(cpuid, cpu_callin_map)) {
		printk("huh, phys CPU#%d, CPU#%d already present??\n",
					phys_id, cpuid);
		BUG();
	}
	Dprintk("CPU#%d (phys ID: %d) waiting for CALLOUT\n", cpuid, phys_id);

	/*
	 * STARTUP IPIs are fragile beasts as they might sometimes
	 * trigger some glue motherboard logic. Complete APIC bus
	 * silence for 1 second, this overestimates the time the
	 * boot CPU is spending to send the up to 2 STARTUP IPIs
	 * by a factor of two. This should be enough.
	 */

	/*
	 * Waiting 2s total for startup
	 */
	for (i = 0; i < 200; i++) {
		/*
		 * Has the boot CPU finished it's STARTUP sequence?
		 */
		if (cpu_isset(cpuid, cpu_callout_map))
			break;
		rep_nop();
		mdelay(10);
	}

	if (!cpu_isset(cpuid, cpu_callout_map)) {
		printk("BUG: CPU%d started up but did not get a callout!\n",
			cpuid);
		BUG();
	}

	/*
	 * the boot CPU has finished the init stage and is spinning
	 * on callin_map until we finish. We are free to set up this
	 * CPU, first the APIC. (this is probably redundant on most
	 * boards)
	 */

	Dprintk("CALLIN, before setup_local_APIC().\n");
	smp_callin_clear_local_apic();
	setup_local_APIC();
	map_cpu_to_logical_apicid();

#if 0
	/*
	 * Get our bogomips.
	 */
	calibrate_delay();
	Dprintk("Stack at about %p\n",&cpuid);
#endif

	/*
	 * Save our processor parameters
	 */
 	smp_store_cpu_info(cpuid);

	disable_APIC_timer();

	/*
	 * Allow the master to continue.
	 */
	cpu_set(cpuid, cpu_callin_map);

	/*
	 *      Synchronize the TSC with the BP
	 */
	if (cpu_has_tsc && cpu_khz && !tsc_sync_disabled) {
		synchronize_tsc_ap();
		/* No sync for same reason as above */
		calibrate_tsc_ap();
	}
}

static int cpucount, booting_cpu;

/* representing cpus for which sibling maps can be computed */
static cpumask_t cpu_sibling_setup_map;

static inline void
set_cpu_sibling_map(int cpu)
{
	int i;
	struct cpuinfo_x86 *c = cpu_data;

	cpu_set(cpu, cpu_sibling_setup_map);

	if (smp_num_siblings > 1) {
		for_each_cpu_mask(i, cpu_sibling_setup_map) {
			if (phys_proc_id[cpu] == phys_proc_id[i] &&
			    cpu_core_id[cpu] == cpu_core_id[i]) {
				cpu_set(i, cpu_sibling_map[cpu]);
				cpu_set(cpu, cpu_sibling_map[i]);
				cpu_set(i, cpu_core_map[cpu]);
				cpu_set(cpu, cpu_core_map[i]);
			}
		}
	} else {
		cpu_set(cpu, cpu_sibling_map[cpu]);
	}

	if (current_cpu_data.x86_max_cores == 1) {
		cpu_core_map[cpu] = cpu_sibling_map[cpu];
		c[cpu].booted_cores = 1;
		return;
	}

	for_each_cpu_mask(i, cpu_sibling_setup_map) {
		if (phys_proc_id[cpu] == phys_proc_id[i]) {
			cpu_set(i, cpu_core_map[cpu]);
			cpu_set(cpu, cpu_core_map[i]);
			/*
			 *  Does this new cpu bringup a new core?
			 */
			if (cpus_weight(cpu_sibling_map[cpu]) == 1) {
				/*
				 * for each core in package, increment
				 * the booted_cores for this new cpu
				 */
				if (first_cpu(cpu_sibling_map[i]) == i)
					c[cpu].booted_cores++;
				/*
				 * increment the core count for all
				 * the other cpus in this package
				 */
				if (i != cpu)
					c[i].booted_cores++;
			} else if (i != cpu && !c[cpu].booted_cores)
				c[cpu].booted_cores = c[i].booted_cores;
		}
	}
}

static void construct_percpu_idt(unsigned int cpu)
{
	unsigned char idt_load[10];

	/* If IDT table exists since last hotplug, reuse it */
	if (!idt_tables[cpu]) {
		idt_tables[cpu] = xmalloc_array(idt_entry_t, IDT_ENTRIES);
		memcpy(idt_tables[cpu], idt_table,
				IDT_ENTRIES*sizeof(idt_entry_t));
	}

	*(unsigned short *)(&idt_load[0]) = (IDT_ENTRIES*sizeof(idt_entry_t))-1;
	*(unsigned long  *)(&idt_load[2]) = (unsigned long)idt_tables[cpu];
	__asm__ __volatile__ ( "lidt %0" : "=m" (idt_load) );
}

/*
 * Activate a secondary processor.
 */
void __devinit start_secondary(void *unused)
{
	/*
	 * Dont put anything before smp_callin(), SMP
	 * booting is too fragile that we want to limit the
	 * things done here to the most necessary things.
	 */
	unsigned int cpu = booting_cpu;

	set_processor_id(cpu);
	set_current(idle_vcpu[cpu]);
	this_cpu(curr_vcpu) = idle_vcpu[cpu];
        if ( cpu_has_efer )
            rdmsrl(MSR_EFER, this_cpu(efer));
	asm volatile ( "mov %%cr4,%0" : "=r" (this_cpu(cr4)) );

	percpu_traps_init();

	cpu_init();
	/*preempt_disable();*/
	smp_callin();
	while (!cpu_isset(smp_processor_id(), smp_commenced_mask))
		rep_nop();

	/*
	 * At this point, boot CPU has fully initialised the IDT. It is
	 * now safe to make ourselves a private copy.
	 */
	construct_percpu_idt(cpu);

	setup_secondary_APIC_clock();
	enable_APIC_timer();
	/*
	 * low-memory mappings have been cleared, flush them from
	 * the local TLBs too.
	 */
	flush_tlb_local();

	/* This must be done before setting cpu_online_map */
	set_cpu_sibling_map(raw_smp_processor_id());
	wmb();

	cpu_set(smp_processor_id(), cpu_online_map);
	per_cpu(cpu_state, smp_processor_id()) = CPU_ONLINE;

	init_percpu_time();

	/* We can take interrupts now: we're officially "up". */
	local_irq_enable();

	wmb();
	startup_cpu_idle_loop();
}

extern struct {
	void * esp;
	unsigned short ss;
} stack_start;

u8 cpu_2_logical_apicid[NR_CPUS] __read_mostly = { [0 ... NR_CPUS-1] = BAD_APICID };

static void map_cpu_to_logical_apicid(void)
{
	int cpu = smp_processor_id();
	int apicid = hard_smp_processor_id();

	cpu_2_logical_apicid[cpu] = apicid;
}

static void unmap_cpu_to_logical_apicid(int cpu)
{
	cpu_2_logical_apicid[cpu] = BAD_APICID;
}

#if APIC_DEBUG
static inline void __inquire_remote_apic(int apicid)
{
	int i, regs[] = { APIC_ID >> 4, APIC_LVR >> 4, APIC_SPIV >> 4 };
	char *names[] = { "ID", "VERSION", "SPIV" };
	int timeout, status;

	printk("Inquiring remote APIC #%d...\n", apicid);

	for (i = 0; i < ARRAY_SIZE(regs); i++) {
		printk("... APIC #%d %s: ", apicid, names[i]);

		/*
		 * Wait for idle.
		 */
		apic_wait_icr_idle();

		apic_write_around(APIC_ICR2, SET_APIC_DEST_FIELD(apicid));
		apic_write_around(APIC_ICR, APIC_DM_REMRD | regs[i]);

		timeout = 0;
		do {
			udelay(100);
			status = apic_read(APIC_ICR) & APIC_ICR_RR_MASK;
		} while (status == APIC_ICR_RR_INPROG && timeout++ < 1000);

		switch (status) {
		case APIC_ICR_RR_VALID:
			status = apic_read(APIC_RRR);
			printk("%08x\n", status);
			break;
		default:
			printk("failed\n");
		}
	}
}
#endif

#ifdef WAKE_SECONDARY_VIA_NMI
/* 
 * Poke the other CPU in the eye via NMI to wake it up. Remember that the normal
 * INIT, INIT, STARTUP sequence will reset the chip hard for us, and this
 * won't ... remember to clear down the APIC, etc later.
 */
static int __devinit
wakeup_secondary_cpu(int logical_apicid, unsigned long start_eip)
{
	unsigned long send_status = 0, accept_status = 0;
	int timeout, maxlvt;

	/* Target chip */
	apic_write_around(APIC_ICR2, SET_APIC_DEST_FIELD(logical_apicid));

	/* Boot on the stack */
	/* Kick the second */
	apic_write_around(APIC_ICR, APIC_DM_NMI | APIC_DEST_LOGICAL);

	Dprintk("Waiting for send to finish...\n");
	timeout = 0;
	do {
		Dprintk("+");
		udelay(100);
		send_status = apic_read(APIC_ICR) & APIC_ICR_BUSY;
	} while (send_status && (timeout++ < 1000));

	/*
	 * Give the other CPU some time to accept the IPI.
	 */
	udelay(200);
	/*
	 * Due to the Pentium erratum 3AP.
	 */
	maxlvt = get_maxlvt();
	if (maxlvt > 3) {
		apic_read_around(APIC_SPIV);
		apic_write(APIC_ESR, 0);
	}
	accept_status = (apic_read(APIC_ESR) & 0xEF);
	Dprintk("NMI sent.\n");

	if (send_status)
		printk("APIC never delivered???\n");
	if (accept_status)
		printk("APIC delivery error (%lx).\n", accept_status);

	return (send_status | accept_status);
}
#endif	/* WAKE_SECONDARY_VIA_NMI */

#ifdef WAKE_SECONDARY_VIA_INIT
static int __devinit
wakeup_secondary_cpu(int phys_apicid, unsigned long start_eip)
{
	unsigned long send_status = 0, accept_status = 0;
	int maxlvt, timeout, num_starts, j;

	/*
	 * Be paranoid about clearing APIC errors.
	 */
	if (APIC_INTEGRATED(apic_version[phys_apicid])) {
		apic_read_around(APIC_SPIV);
		apic_write(APIC_ESR, 0);
		apic_read(APIC_ESR);
	}

	Dprintk("Asserting INIT.\n");

	/*
	 * Turn INIT on target chip
	 */
	apic_write_around(APIC_ICR2, SET_APIC_DEST_FIELD(phys_apicid));

	/*
	 * Send IPI
	 */
	apic_write_around(APIC_ICR, APIC_INT_LEVELTRIG | APIC_INT_ASSERT
				| APIC_DM_INIT);

	Dprintk("Waiting for send to finish...\n");
	timeout = 0;
	do {
		Dprintk("+");
		udelay(100);
		send_status = apic_read(APIC_ICR) & APIC_ICR_BUSY;
	} while (send_status && (timeout++ < 1000));

	mdelay(10);

	Dprintk("Deasserting INIT.\n");

	/* Target chip */
	apic_write_around(APIC_ICR2, SET_APIC_DEST_FIELD(phys_apicid));

	/* Send IPI */
	apic_write_around(APIC_ICR, APIC_INT_LEVELTRIG | APIC_DM_INIT);

	Dprintk("Waiting for send to finish...\n");
	timeout = 0;
	do {
		Dprintk("+");
		udelay(100);
		send_status = apic_read(APIC_ICR) & APIC_ICR_BUSY;
	} while (send_status && (timeout++ < 1000));

	atomic_set(&init_deasserted, 1);

	/*
	 * Should we send STARTUP IPIs ?
	 *
	 * Determine this based on the APIC version.
	 * If we don't have an integrated APIC, don't send the STARTUP IPIs.
	 */
	if (APIC_INTEGRATED(apic_version[phys_apicid]))
		num_starts = 2;
	else
		num_starts = 0;

	/*
	 * Run STARTUP IPI loop.
	 */
	Dprintk("#startup loops: %d.\n", num_starts);

	maxlvt = get_maxlvt();

	for (j = 1; j <= num_starts; j++) {
		Dprintk("Sending STARTUP #%d.\n",j);
		apic_read_around(APIC_SPIV);
		apic_write(APIC_ESR, 0);
		apic_read(APIC_ESR);
		Dprintk("After apic_write.\n");

		/*
		 * STARTUP IPI
		 */

		/* Target chip */
		apic_write_around(APIC_ICR2, SET_APIC_DEST_FIELD(phys_apicid));

		/* Boot on the stack */
		/* Kick the second */
		apic_write_around(APIC_ICR, APIC_DM_STARTUP
					| (start_eip >> 12));

		/*
		 * Give the other CPU some time to accept the IPI.
		 */
		udelay(300);

		Dprintk("Startup point 1.\n");

		Dprintk("Waiting for send to finish...\n");
		timeout = 0;
		do {
			Dprintk("+");
			udelay(100);
			send_status = apic_read(APIC_ICR) & APIC_ICR_BUSY;
		} while (send_status && (timeout++ < 1000));

		/*
		 * Give the other CPU some time to accept the IPI.
		 */
		udelay(200);
		/*
		 * Due to the Pentium erratum 3AP.
		 */
		if (maxlvt > 3) {
			apic_read_around(APIC_SPIV);
			apic_write(APIC_ESR, 0);
		}
		accept_status = (apic_read(APIC_ESR) & 0xEF);
		if (send_status || accept_status)
			break;
	}
	Dprintk("After Startup.\n");

	if (send_status)
		printk("APIC never delivered???\n");
	if (accept_status)
		printk("APIC delivery error (%lx).\n", accept_status);

	return (send_status | accept_status);
}
#endif	/* WAKE_SECONDARY_VIA_INIT */

extern cpumask_t cpu_initialized;
static inline int alloc_cpu_id(void)
{
	cpumask_t	tmp_map;
	int cpu;
	cpus_complement(tmp_map, cpu_present_map);
	cpu = first_cpu(tmp_map);
	if (cpu >= NR_CPUS)
		return -ENODEV;
	return cpu;
}

static struct vcpu *prepare_idle_vcpu(unsigned int cpu)
{
	if (idle_vcpu[cpu])
		return idle_vcpu[cpu];

	return alloc_idle_vcpu(cpu);
}

static void *prepare_idle_stack(unsigned int cpu)
{
	if (!stack_base[cpu])
		stack_base[cpu] = alloc_xenheap_pages(STACK_ORDER);

	return stack_base[cpu];
}

static int __devinit do_boot_cpu(int apicid, int cpu)
/*
 * NOTE - on most systems this is a PHYSICAL apic ID, but on multiquad
 * (ie clustered apic addressing mode), this is a LOGICAL apic ID.
 * Returns zero if CPU booted OK, else error code from wakeup_secondary_cpu.
 */
{
	unsigned long boot_error;
	int timeout;
	unsigned long start_eip;
	unsigned short nmi_high = 0, nmi_low = 0;
	struct vcpu *v;

	/*
	 * Save current MTRR state in case it was changed since early boot
	 * (e.g. by the ACPI SMI) to initialize new CPUs with MTRRs in sync:
	 */
	mtrr_save_state();

	++cpucount;

	booting_cpu = cpu;

	v = prepare_idle_vcpu(cpu);
	BUG_ON(v == NULL);

	/* start_eip had better be page-aligned! */
	start_eip = setup_trampoline();

	/* So we see what's up   */
	printk("Booting processor %d/%d eip %lx\n", cpu, apicid, start_eip);

	stack_start.esp = prepare_idle_stack(cpu);

	/* Debug build: detect stack overflow by setting up a guard page. */
	memguard_guard_stack(stack_start.esp);

	/*
	 * This grunge runs the startup process for
	 * the targeted processor.
	 */

	atomic_set(&init_deasserted, 0);

	Dprintk("Setting warm reset code and vector.\n");

	store_NMI_vector(&nmi_high, &nmi_low);

	smpboot_setup_warm_reset_vector(start_eip);

	/*
	 * Starting actual IPI sequence...
	 */
	boot_error = wakeup_secondary_cpu(apicid, start_eip);

	if (!boot_error) {
		/*
		 * allow APs to start initializing.
		 */
		Dprintk("Before Callout %d.\n", cpu);
		cpu_set(cpu, cpu_callout_map);
		Dprintk("After Callout %d.\n", cpu);

		/*
		 * Wait 5s total for a response
		 */
		for (timeout = 0; timeout < 50000; timeout++) {
			if (cpu_isset(cpu, cpu_callin_map))
				break;	/* It has booted */
			udelay(100);
		}

		if (cpu_isset(cpu, cpu_callin_map)) {
			/* number CPUs logically, starting from 1 (BSP is 0) */
			Dprintk("OK.\n");
			printk("CPU%d: ", cpu);
			print_cpu_info(&cpu_data[cpu]);
			Dprintk("CPU has booted.\n");
		} else {
			boot_error = 1;
			mb();
			if (bootsym(trampoline_cpu_started) == 0xA5)
				/* trampoline started but...? */
				printk("Stuck ??\n");
			else
				/* trampoline code not run */
				printk("Not responding.\n");
			inquire_remote_apic(apicid);
		}
	}

	if (boot_error) {
		/* Try to put things back the way they were before ... */
		unmap_cpu_to_logical_apicid(cpu);
		cpu_clear(cpu, cpu_callout_map); /* was set here (do_boot_cpu()) */
		cpu_clear(cpu, cpu_initialized); /* was set by cpu_init() */
		cpucount--;
	} else {
		x86_cpu_to_apicid[cpu] = apicid;
		cpu_set(cpu, cpu_present_map);
	}

	/* mark "stuck" area as not stuck */
	bootsym(trampoline_cpu_started) = 0;
	mb();

	return boot_error;
}

#ifdef CONFIG_HOTPLUG_CPU
static void idle_task_exit(void)
{
	/* Give up lazy state borrowed by this idle vcpu */
	__sync_lazy_execstate();
}

void cpu_exit_clear(void)
{
	int cpu = raw_smp_processor_id();

	idle_task_exit();

	cpucount --;
	cpu_uninit();

	cpu_clear(cpu, cpu_callout_map);
	cpu_clear(cpu, cpu_callin_map);

	cpu_clear(cpu, smp_commenced_mask);
	unmap_cpu_to_logical_apicid(cpu);
}

static int __cpuinit __smp_prepare_cpu(int cpu)
{
	int	apicid, ret;

	apicid = x86_cpu_to_apicid[cpu];
	if (apicid == BAD_APICID) {
		ret = -ENODEV;
		goto exit;
	}

	tsc_sync_disabled = 1;

	do_boot_cpu(apicid, cpu);

	tsc_sync_disabled = 0;

	ret = 0;
exit:
	return ret;
}
#endif

/*
 * Cycle through the processors sending APIC IPIs to boot each.
 */

/* Where the IO area was mapped on multiquad, always 0 otherwise */
void *xquad_portio;
#ifdef CONFIG_X86_NUMAQ
EXPORT_SYMBOL(xquad_portio);
#endif

static void __init smp_boot_cpus(unsigned int max_cpus)
{
	int apicid, cpu, bit, kicked;
#ifdef BOGOMIPS
	unsigned long bogosum = 0;
#endif

	/*
	 * Setup boot CPU information
	 */
	smp_store_cpu_info(0); /* Final full version of the data */
	printk("CPU%d: ", 0);
	print_cpu_info(&cpu_data[0]);

	boot_cpu_physical_apicid = GET_APIC_ID(apic_read(APIC_ID));
	x86_cpu_to_apicid[0] = boot_cpu_physical_apicid;

	stack_base[0] = stack_start.esp;

	/*current_thread_info()->cpu = 0;*/
	/*smp_tune_scheduling();*/

	set_cpu_sibling_map(0);

	/*
	 * If we couldn't find an SMP configuration at boot time,
	 * get out of here now!
	 */
	if (!smp_found_config && !acpi_lapic) {
		printk(KERN_NOTICE "SMP motherboard not detected.\n");
	init_uniprocessor:
		phys_cpu_present_map = physid_mask_of_physid(0);
		if (APIC_init_uniprocessor())
			printk(KERN_NOTICE "Local APIC not detected."
					   " Using dummy APIC emulation.\n");
		map_cpu_to_logical_apicid();
		cpu_set(0, cpu_sibling_map[0]);
		cpu_set(0, cpu_core_map[0]);
		return;
	}

	/*
	 * Should not be necessary because the MP table should list the boot
	 * CPU too, but we do it for the sake of robustness anyway.
	 * Makes no sense to do this check in clustered apic mode, so skip it
	 */
	if (!check_phys_apicid_present(boot_cpu_physical_apicid)) {
		printk("weird, boot CPU (#%d) not listed by the BIOS.\n",
				boot_cpu_physical_apicid);
		physid_set(hard_smp_processor_id(), phys_cpu_present_map);
	}

	/*
	 * If we couldn't find a local APIC, then get out of here now!
	 */
	if (APIC_INTEGRATED(apic_version[boot_cpu_physical_apicid]) && !cpu_has_apic) {
		printk(KERN_ERR "BIOS bug, local APIC #%d not detected!...\n",
			boot_cpu_physical_apicid);
		goto init_uniprocessor;
	}

	verify_local_APIC();

	/*
	 * If SMP should be disabled, then really disable it!
	 */
	if (!max_cpus)
		goto init_uniprocessor;

	connect_bsp_APIC();
	setup_local_APIC();
	map_cpu_to_logical_apicid();


	setup_portio_remap();

	/*
	 * Scan the CPU present map and fire up the other CPUs via do_boot_cpu
	 *
	 * In clustered apic mode, phys_cpu_present_map is a constructed thus:
	 * bits 0-3 are quad0, 4-7 are quad1, etc. A perverse twist on the 
	 * clustered apic ID.
	 */
	Dprintk("CPU present map: %lx\n", physids_coerce(phys_cpu_present_map));

	kicked = 1;
	for (bit = 0; kicked < NR_CPUS && bit < MAX_APICS; bit++) {
		apicid = cpu_present_to_apicid(bit);
		/*
		 * Don't even attempt to start the boot CPU!
		 */
		if ((apicid == boot_cpu_apicid) || (apicid == BAD_APICID))
			continue;

		if (!check_apicid_present(apicid))
			continue;
		if (max_cpus <= cpucount+1)
			continue;

		if (((cpu = alloc_cpu_id()) <= 0) || do_boot_cpu(apicid, cpu))
			printk("CPU #%d not responding - cannot use it.\n",
								apicid);
		else
			++kicked;
	}

	/*
	 * Cleanup possible dangling ends...
	 */
	smpboot_restore_warm_reset_vector();

#ifdef BOGOMIPS
	/*
	 * Allow the user to impress friends.
	 */
	Dprintk("Before bogomips.\n");
	for (cpu = 0; cpu < NR_CPUS; cpu++)
		if (cpu_isset(cpu, cpu_callout_map))
			bogosum += cpu_data[cpu].loops_per_jiffy;
	printk(KERN_INFO
		"Total of %d processors activated (%lu.%02lu BogoMIPS).\n",
		cpucount+1,
		bogosum/(500000/HZ),
		(bogosum/(5000/HZ))%100);
#else
	printk("Total of %d processors activated.\n", cpucount+1);
#endif
	
	Dprintk("Before bogocount - setting activated=1.\n");

	if (smp_b_stepping)
		printk(KERN_WARNING "WARNING: SMP operation may be unreliable with B stepping processors.\n");

	/*
	 * Don't taint if we are running SMP kernel on a single non-MP
	 * approved Athlon
	 */
	if (tainted & TAINT_UNSAFE_SMP) {
		if (cpucount)
			printk (KERN_INFO "WARNING: This combination of AMD processors is not suitable for SMP.\n");
		else
			tainted &= ~TAINT_UNSAFE_SMP;
	}

	Dprintk("Boot done.\n");

	/*
	 * construct cpu_sibling_map[], so that we can tell sibling CPUs
	 * efficiently.
	 */
	for (cpu = 0; cpu < NR_CPUS; cpu++) {
		cpus_clear(cpu_sibling_map[cpu]);
		cpus_clear(cpu_core_map[cpu]);
	}

	cpu_set(0, cpu_sibling_map[0]);
	cpu_set(0, cpu_core_map[0]);

	if (nmi_watchdog == NMI_LOCAL_APIC)
		check_nmi_watchdog();

	smpboot_setup_io_apic();

	setup_boot_APIC_clock();

	/*
	 * Synchronize the TSC with the AP
	 */
	if (cpu_has_tsc && cpucount && cpu_khz)
		synchronize_tsc_bp();
	calibrate_tsc_bp();
}

/* These are wrappers to interface to the new boot process.  Someone
   who understands all this stuff should rewrite it properly. --RR 15/Jul/02 */
void __init smp_prepare_cpus(unsigned int max_cpus)
{
	smp_commenced_mask = cpumask_of_cpu(0);
	cpu_callin_map = cpumask_of_cpu(0);
	mb();
	smp_boot_cpus(max_cpus);
}

void __devinit smp_prepare_boot_cpu(void)
{
	cpu_set(smp_processor_id(), cpu_online_map);
	cpu_set(smp_processor_id(), cpu_callout_map);
	cpu_set(smp_processor_id(), cpu_present_map);
	cpu_set(smp_processor_id(), cpu_possible_map);
	per_cpu(cpu_state, smp_processor_id()) = CPU_ONLINE;
	spin_lock_init(&cpu_add_remove_lock);
}

#ifdef CONFIG_HOTPLUG_CPU
static void
remove_siblinginfo(int cpu)
{
	int sibling;
	struct cpuinfo_x86 *c = cpu_data;

	for_each_cpu_mask(sibling, cpu_core_map[cpu]) {
		cpu_clear(cpu, cpu_core_map[sibling]);
		/*
		 * last thread sibling in this cpu core going down
		 */
		if (cpus_weight(cpu_sibling_map[cpu]) == 1)
			c[sibling].booted_cores--;
	}
			
	for_each_cpu_mask(sibling, cpu_sibling_map[cpu])
		cpu_clear(cpu, cpu_sibling_map[sibling]);
	cpus_clear(cpu_sibling_map[cpu]);
	cpus_clear(cpu_core_map[cpu]);
	phys_proc_id[cpu] = BAD_APICID;
	cpu_core_id[cpu] = BAD_APICID;
	cpu_clear(cpu, cpu_sibling_setup_map);
}

extern void fixup_irqs(cpumask_t map);
int __cpu_disable(void)
{
	cpumask_t map = cpu_online_map;
	int cpu = smp_processor_id();

	/*
	 * Perhaps use cpufreq to drop frequency, but that could go
	 * into generic code.
 	 *
	 * We won't take down the boot processor on i386 due to some
	 * interrupts only being able to be serviced by the BSP.
	 * Especially so if we're not using an IOAPIC	-zwane
	 */
	if (cpu == 0)
		return -EBUSY;

	local_irq_disable();
	clear_local_APIC();
	/* Allow any queued timer interrupts to get serviced */
	local_irq_enable();
	mdelay(1);
	local_irq_disable();

	time_suspend();

	remove_siblinginfo(cpu);

	cpu_clear(cpu, map);
	fixup_irqs(map);
	/* It's now safe to remove this processor from the online map */
	cpu_clear(cpu, cpu_online_map);
	return 0;
}

void __cpu_die(unsigned int cpu)
{
	/* We don't do anything here: idle task is faking death itself. */
	unsigned int i;

	for (i = 0; i < 10; i++) {
		/* They ack this in play_dead by setting CPU_DEAD */
		if (per_cpu(cpu_state, cpu) == CPU_DEAD) {
			printk ("CPU %d is now offline\n", cpu);
			return;
		}
		mdelay(100);
		mb();
		process_pending_timers();
	}
 	printk(KERN_ERR "CPU %u didn't die...\n", cpu);
}

/* 
 * XXX: One important thing missed here is to migrate vcpus
 * from dead cpu to other online ones and then put whole
 * system into a stop state. It assures a safe environment
 * for a cpu hotplug/remove at normal running state.
 *
 * However for xen PM case, at this point:
 * 	-> All other domains should be notified with PM event,
 *	   and then in following states:
 *		* Suspend state, or
 *		* Paused state, which is a force step to all
 *		  domains if they do nothing to suspend
 *	-> All vcpus of dom0 (except vcpu0) have already beem
 *	   hot removed
 * with the net effect that all other cpus only have idle vcpu
 * running. In this special case, we can avoid vcpu migration
 * then and system can be considered in a stop state.
 *
 * So current cpu hotplug is a special version for PM specific
 * usage, and need more effort later for full cpu hotplug.
 * (ktian1)
 */
int cpu_down(unsigned int cpu)
{
	int err = 0;
	cpumask_t mask;

	spin_lock(&cpu_add_remove_lock);
	if (num_online_cpus() == 1) {
		err = -EBUSY;
		goto out;
	}

	if (!cpu_online(cpu)) {
		err = -EINVAL;
		goto out;
	}

	printk("Prepare to bring CPU%d down...\n", cpu);
	/* Send notification to remote idle vcpu */
	cpus_clear(mask);
	cpu_set(cpu, mask);
	per_cpu(cpu_state, cpu) = CPU_DYING;
	smp_send_event_check_mask(mask);

	__cpu_die(cpu);

	if (cpu_online(cpu)) {
		printk("Bad state (DEAD, but in online map) on CPU%d\n", cpu);
		err = -EBUSY;
	}
out:
	spin_unlock(&cpu_add_remove_lock);
	return err;
}

int cpu_up(unsigned int cpu)
{
	int err = 0;

	spin_lock(&cpu_add_remove_lock);
	if (cpu_online(cpu)) {
		printk("Bring up a online cpu. Bogus!\n");
		err = -EBUSY;
		goto out;
	}

	err = __cpu_up(cpu);
	if (err < 0)
		goto out;

out:
	spin_unlock(&cpu_add_remove_lock);
	return err;
}

/* From kernel/power/main.c */
/* This is protected by pm_sem semaphore */
static cpumask_t frozen_cpus;

void disable_nonboot_cpus(void)
{
	int cpu, error;

	error = 0;
	cpus_clear(frozen_cpus);
	printk("Freezing cpus ...\n");
	for_each_online_cpu(cpu) {
		if (cpu == 0)
			continue;
		error = cpu_down(cpu);
		if (!error) {
			cpu_set(cpu, frozen_cpus);
			printk("CPU%d is down\n", cpu);
			continue;
		}
		printk("Error taking cpu %d down: %d\n", cpu, error);
	}
	BUG_ON(raw_smp_processor_id() != 0);
	if (error)
		panic("cpus not sleeping");
}

void enable_nonboot_cpus(void)
{
	int cpu, error;

	printk("Thawing cpus ...\n");
	for_each_cpu_mask(cpu, frozen_cpus) {
		error = cpu_up(cpu);
		if (!error) {
			printk("CPU%d is up\n", cpu);
			continue;
		}
		printk("Error taking cpu %d up: %d\n", cpu, error);
		panic("Not enough cpus");
	}
	cpus_clear(frozen_cpus);

	/*
	 * Cleanup possible dangling ends after sleep...
	 */
	smpboot_restore_warm_reset_vector();
}
#else /* ... !CONFIG_HOTPLUG_CPU */
int __cpu_disable(void)
{
	return -ENOSYS;
}

void __cpu_die(unsigned int cpu)
{
	/* We said "no" in __cpu_disable */
	BUG();
}
#endif /* CONFIG_HOTPLUG_CPU */

int __devinit __cpu_up(unsigned int cpu)
{
#ifdef CONFIG_HOTPLUG_CPU
	int ret=0;

	/*
	 * We do warm boot only on cpus that had booted earlier
	 * Otherwise cold boot is all handled from smp_boot_cpus().
	 * cpu_callin_map is set during AP kickstart process. Its reset
	 * when a cpu is taken offline from cpu_exit_clear().
	 */
	if (!cpu_isset(cpu, cpu_callin_map))
		ret = __smp_prepare_cpu(cpu);

	if (ret)
		return -EIO;
#endif

	/* In case one didn't come up */
	if (!cpu_isset(cpu, cpu_callin_map)) {
		printk(KERN_DEBUG "skipping cpu%d, didn't come online\n", cpu);
		local_irq_enable();
		return -EIO;
	}

	local_irq_enable();
	/*per_cpu(cpu_state, cpu) = CPU_UP_PREPARE;*/
	/* Unleash the CPU! */
	cpu_set(cpu, smp_commenced_mask);
	while (!cpu_isset(cpu, cpu_online_map)) {
		mb();
		process_pending_timers();
	}
	return 0;
}


void __init smp_cpus_done(unsigned int max_cpus)
{
#ifdef CONFIG_X86_IO_APIC
	setup_ioapic_dest();
#endif
#ifndef CONFIG_HOTPLUG_CPU
	/*
	 * Disable executability of the SMP trampoline:
	 */
	set_kernel_exec((unsigned long)trampoline_base, trampoline_exec);
#endif
}

void __init smp_intr_init(void)
{
	int irq, seridx;

	/*
	 * IRQ0 must be given a fixed assignment and initialized,
	 * because it's used before the IO-APIC is set up.
	 */
	irq_vector[0] = FIRST_HIPRIORITY_VECTOR;
	vector_irq[FIRST_HIPRIORITY_VECTOR] = 0;

	/*
	 * Also ensure serial interrupts are high priority. We do not
	 * want them to be blocked by unacknowledged guest-bound interrupts.
	 */
	for (seridx = 0; seridx < 2; seridx++) {
		if ((irq = serial_irq(seridx)) < 0)
			continue;
		irq_vector[irq] = FIRST_HIPRIORITY_VECTOR + seridx + 1;
		vector_irq[FIRST_HIPRIORITY_VECTOR + seridx + 1] = irq;
	}

	/* IPI for event checking. */
	set_intr_gate(EVENT_CHECK_VECTOR, event_check_interrupt);

	/* IPI for invalidation */
	set_intr_gate(INVALIDATE_TLB_VECTOR, invalidate_interrupt);

	/* IPI for generic function call */
	set_intr_gate(CALL_FUNCTION_VECTOR, call_function_interrupt);
}
