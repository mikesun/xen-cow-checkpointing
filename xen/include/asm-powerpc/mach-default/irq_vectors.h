/* from xen/include/asm-x86/mach-default/irq_vectors.h */

/*
 * This file should contain #defines for all of the interrupt vector
 * numbers used by this architecture.
 *
 * In addition, there are some standard defines:
 *
 *	FIRST_EXTERNAL_VECTOR:
 *		The first free place for external interrupts
 *
 *	SYSCALL_VECTOR:
 *		The IRQ vector a syscall makes the user to kernel transition
 *		under.
 *
 *	TIMER_IRQ:
 *		The IRQ number the timer interrupt comes in at.
 *
 *	NR_IRQS:
 *		The total number of interrupt vectors (including all the
 *		architecture specific interrupts) needed.
 *
 */			
#ifndef _ASM_IRQ_VECTORS_H
#define _ASM_IRQ_VECTORS_H

/*
 * IDT vectors usable for external interrupt sources start
 * at 0x0:
 */
#define FIRST_EXTERNAL_VECTOR	0x0
#define FIRST_DEVICE_VECTOR	0
#define NR_IRQS 256
#define NR_VECTORS NR_IRQS
#define NR_IRQ_VECTORS NR_IRQS
#define HYPERCALL_VECTOR	-1
#define FAST_TRAP -1 /* 0x80 */
#define FIRST_SYSTEM_VECTOR	-1

#define CALL_FUNCTION_VECTOR	0x0
#define EVENT_CHECK_VECTOR	0x1

#if 0

#define THERMAL_APIC_VECTOR	0xf0
/*
 * Local APIC timer IRQ vector is on a different priority level,
 * to work around the 'lost local interrupt if more than 2 IRQ
 * sources per level' errata.
 */
#define LOCAL_TIMER_VECTOR	0xef

/*
 * First APIC vector available to drivers: (vectors 0x30-0xee)
 * we start at 0x31 to spread out vectors evenly between priority
 * levels. (0x80 is the syscall vector)
 */
#define FIRST_DEVICE_VECTOR	0x31
#define FIRST_SYSTEM_VECTOR	0xef

#define TIMER_IRQ 0

/*
 * 16 8259A IRQ's, 208 potential APIC interrupt sources.
 * Right now the APIC is mostly only used for SMP.
 * 256 vectors is an architectural limit. (we can have
 * more than 256 devices theoretically, but they will
 * have to use shared interrupts)
 * Since vectors 0x00-0x1f are used/reserved for the CPU,
 * the usable vector space is 0x20-0xff (224 vectors)
 */

/*
 * The maximum number of vectors supported by i386 processors
 * is limited to 256. For processors other than i386, NR_VECTORS
 * should be changed accordingly.
 */
#define NR_VECTORS 256

#include "irq_vectors_limits.h"

#define FPU_IRQ			13

#define	FIRST_VM86_IRQ		3
#define LAST_VM86_IRQ		15
#define invalid_vm86_irq(irq)	((irq) < 3 || (irq) > 15)

#endif // 0
#endif /* _ASM_IRQ_VECTORS_H */
