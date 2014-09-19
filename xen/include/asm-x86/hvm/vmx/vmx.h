/*
 * vmx.h: VMX Architecture related definitions
 * Copyright (c) 2004, Intel Corporation.
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
#ifndef __ASM_X86_HVM_VMX_VMX_H__
#define __ASM_X86_HVM_VMX_VMX_H__

#include <xen/sched.h>
#include <asm/types.h>
#include <asm/regs.h>
#include <asm/processor.h>
#include <asm/hvm/vmx/vmcs.h>
#include <asm/i387.h>
#include <asm/hvm/trace.h>

void vmx_asm_vmexit_handler(struct cpu_user_regs);
void vmx_asm_do_vmentry(void);
void vmx_intr_assist(void);
void vmx_do_resume(struct vcpu *);
void set_guest_time(struct vcpu *v, u64 gtime);
void vmx_vlapic_msr_changed(struct vcpu *v);
void vmx_do_no_device_fault(void);
void vmx_cpuid_intercept(
    unsigned int *eax, unsigned int *ebx,
    unsigned int *ecx, unsigned int *edx);
int vmx_msr_read_intercept(struct cpu_user_regs *regs);
int vmx_msr_write_intercept(struct cpu_user_regs *regs);
void vmx_wbinvd_intercept(void);
void vmx_realmode(struct cpu_user_regs *regs);
int vmx_realmode_io_complete(void);

/*
 * Exit Reasons
 */
#define VMX_EXIT_REASONS_FAILED_VMENTRY 0x80000000

#define EXIT_REASON_EXCEPTION_NMI       0
#define EXIT_REASON_EXTERNAL_INTERRUPT  1
#define EXIT_REASON_TRIPLE_FAULT        2
#define EXIT_REASON_INIT                3
#define EXIT_REASON_SIPI                4
#define EXIT_REASON_IO_SMI              5
#define EXIT_REASON_OTHER_SMI           6
#define EXIT_REASON_PENDING_VIRT_INTR   7
#define EXIT_REASON_PENDING_VIRT_NMI    8
#define EXIT_REASON_TASK_SWITCH         9
#define EXIT_REASON_CPUID               10
#define EXIT_REASON_HLT                 12
#define EXIT_REASON_INVD                13
#define EXIT_REASON_INVLPG              14
#define EXIT_REASON_RDPMC               15
#define EXIT_REASON_RDTSC               16
#define EXIT_REASON_RSM                 17
#define EXIT_REASON_VMCALL              18
#define EXIT_REASON_VMCLEAR             19
#define EXIT_REASON_VMLAUNCH            20
#define EXIT_REASON_VMPTRLD             21
#define EXIT_REASON_VMPTRST             22
#define EXIT_REASON_VMREAD              23
#define EXIT_REASON_VMRESUME            24
#define EXIT_REASON_VMWRITE             25
#define EXIT_REASON_VMXOFF              26
#define EXIT_REASON_VMXON               27
#define EXIT_REASON_CR_ACCESS           28
#define EXIT_REASON_DR_ACCESS           29
#define EXIT_REASON_IO_INSTRUCTION      30
#define EXIT_REASON_MSR_READ            31
#define EXIT_REASON_MSR_WRITE           32
#define EXIT_REASON_INVALID_GUEST_STATE 33
#define EXIT_REASON_MSR_LOADING         34
#define EXIT_REASON_MWAIT_INSTRUCTION   36
#define EXIT_REASON_MONITOR_INSTRUCTION 39
#define EXIT_REASON_PAUSE_INSTRUCTION   40
#define EXIT_REASON_MACHINE_CHECK       41
#define EXIT_REASON_TPR_BELOW_THRESHOLD 43
#define EXIT_REASON_APIC_ACCESS         44
#define EXIT_REASON_WBINVD              54

/*
 * Interruption-information format
 */
#define INTR_INFO_VECTOR_MASK           0xff            /* 7:0 */
#define INTR_INFO_INTR_TYPE_MASK        0x700           /* 10:8 */
#define INTR_INFO_DELIVER_CODE_MASK     0x800           /* 11 */
#define INTR_INFO_NMI_UNBLOCKED_BY_IRET 0x1000          /* 12 */
#define INTR_INFO_VALID_MASK            0x80000000      /* 31 */
#define INTR_INFO_RESVD_BITS_MASK       0x7ffff000

/*
 * Exit Qualifications for MOV for Control Register Access
 */
#define CONTROL_REG_ACCESS_NUM          0xf     /* 3:0, number of control register */
#define CONTROL_REG_ACCESS_TYPE         0x30    /* 5:4, access type */
#define CONTROL_REG_ACCESS_REG          0xf00   /* 10:8, general purpose register */
#define LMSW_SOURCE_DATA                (0xFFFF << 16)  /* 16:31 lmsw source */
#define REG_EAX                         (0 << 8)
#define REG_ECX                         (1 << 8)
#define REG_EDX                         (2 << 8)
#define REG_EBX                         (3 << 8)
#define REG_ESP                         (4 << 8)
#define REG_EBP                         (5 << 8)
#define REG_ESI                         (6 << 8)
#define REG_EDI                         (7 << 8)
#define REG_R8                          (8 << 8)
#define REG_R9                          (9 << 8)
#define REG_R10                         (10 << 8)
#define REG_R11                         (11 << 8)
#define REG_R12                         (12 << 8)
#define REG_R13                         (13 << 8)
#define REG_R14                         (14 << 8)
#define REG_R15                         (15 << 8)

/*
 * Exit Qualifications for MOV for Debug Register Access
 */
#define DEBUG_REG_ACCESS_NUM            0x7     /* 2:0, number of debug register */
#define DEBUG_REG_ACCESS_TYPE           0x10    /* 4, direction of access */
#define TYPE_MOV_TO_DR                  (0 << 4)
#define TYPE_MOV_FROM_DR                (1 << 4)
#define DEBUG_REG_ACCESS_REG            0xf00   /* 11:8, general purpose register */

/*
 * Access Rights
 */
#define X86_SEG_AR_SEG_TYPE     0xf        /* 3:0, segment type */
#define X86_SEG_AR_DESC_TYPE    (1u << 4)  /* 4, descriptor type */
#define X86_SEG_AR_DPL          0x60       /* 6:5, descriptor privilege level */
#define X86_SEG_AR_SEG_PRESENT  (1u << 7)  /* 7, segment present */
#define X86_SEG_AR_AVL          (1u << 12) /* 12, available for system software */
#define X86_SEG_AR_CS_LM_ACTIVE (1u << 13) /* 13, long mode active (CS only) */
#define X86_SEG_AR_DEF_OP_SIZE  (1u << 14) /* 14, default operation size */
#define X86_SEG_AR_GRANULARITY  (1u << 15) /* 15, granularity */
#define X86_SEG_AR_SEG_UNUSABLE (1u << 16) /* 16, segment unusable */

#define VMCALL_OPCODE   ".byte 0x0f,0x01,0xc1\n"
#define VMCLEAR_OPCODE  ".byte 0x66,0x0f,0xc7\n"        /* reg/opcode: /6 */
#define VMLAUNCH_OPCODE ".byte 0x0f,0x01,0xc2\n"
#define VMPTRLD_OPCODE  ".byte 0x0f,0xc7\n"             /* reg/opcode: /6 */
#define VMPTRST_OPCODE  ".byte 0x0f,0xc7\n"             /* reg/opcode: /7 */
#define VMREAD_OPCODE   ".byte 0x0f,0x78\n"
#define VMRESUME_OPCODE ".byte 0x0f,0x01,0xc3\n"
#define VMWRITE_OPCODE  ".byte 0x0f,0x79\n"
#define VMXOFF_OPCODE   ".byte 0x0f,0x01,0xc4\n"
#define VMXON_OPCODE    ".byte 0xf3,0x0f,0xc7\n"

#define MODRM_EAX_06    ".byte 0x30\n" /* [EAX], with reg/opcode: /6 */
#define MODRM_EAX_07    ".byte 0x38\n" /* [EAX], with reg/opcode: /7 */
#define MODRM_EAX_ECX   ".byte 0xc1\n" /* [EAX], [ECX] */

static inline void __vmptrld(u64 addr)
{
    __asm__ __volatile__ ( VMPTRLD_OPCODE
                           MODRM_EAX_06
                           /* CF==1 or ZF==1 --> crash (ud2) */
                           "ja 1f ; ud2 ; 1:\n"
                           :
                           : "a" (&addr)
                           : "memory");
}

static inline void __vmptrst(u64 addr)
{
    __asm__ __volatile__ ( VMPTRST_OPCODE
                           MODRM_EAX_07
                           :
                           : "a" (&addr)
                           : "memory");
}

static inline void __vmpclear(u64 addr)
{
    __asm__ __volatile__ ( VMCLEAR_OPCODE
                           MODRM_EAX_06
                           /* CF==1 or ZF==1 --> crash (ud2) */
                           "ja 1f ; ud2 ; 1:\n"
                           :
                           : "a" (&addr)
                           : "memory");
}

static inline unsigned long __vmread(unsigned long field)
{
    unsigned long ecx;

    __asm__ __volatile__ ( VMREAD_OPCODE
                           MODRM_EAX_ECX
                           /* CF==1 or ZF==1 --> crash (ud2) */
                           "ja 1f ; ud2 ; 1:\n"
                           : "=c" (ecx)
                           : "a" (field)
                           : "memory");

    return ecx;
}

static inline void __vmwrite(unsigned long field, unsigned long value)
{
    __asm__ __volatile__ ( VMWRITE_OPCODE
                           MODRM_EAX_ECX
                           /* CF==1 or ZF==1 --> crash (ud2) */
                           "ja 1f ; ud2 ; 1:\n"
                           : 
                           : "a" (field) , "c" (value)
                           : "memory");
}

static inline unsigned long __vmread_safe(unsigned long field, int *error)
{
    unsigned long ecx;

    __asm__ __volatile__ ( VMREAD_OPCODE
                           MODRM_EAX_ECX
                           /* CF==1 or ZF==1 --> rc = -1 */
                           "setna %b0 ; neg %0"
                           : "=q" (*error), "=c" (ecx)
                           : "0" (0), "a" (field)
                           : "memory");

    return ecx;
}

static inline void __vm_set_bit(unsigned long field, unsigned int bit)
{
    __vmwrite(field, __vmread(field) | (1UL << bit));
}

static inline void __vm_clear_bit(unsigned long field, unsigned int bit)
{
    __vmwrite(field, __vmread(field) & ~(1UL << bit));
}

static inline void __vmxoff(void)
{
    asm volatile (
        VMXOFF_OPCODE
        : : : "memory" );
}

static inline int __vmxon(u64 addr)
{
    int rc;

    asm volatile ( 
        "1: " VMXON_OPCODE MODRM_EAX_06 "\n"
        "   setna %b0 ; neg %0\n" /* CF==1 or ZF==1 --> rc = -1 */
        "2:\n"
        ".section .fixup,\"ax\"\n"
        "3: sub $2,%0 ; jmp 2b\n"    /* #UD or #GP --> rc = -2 */
        ".previous\n"
        ".section __ex_table,\"a\"\n"
        "   "__FIXUP_ALIGN"\n"
        "   "__FIXUP_WORD" 1b,3b\n"
        ".previous\n"
        : "=q" (rc)
        : "0" (0), "a" (&addr)
        : "memory");

    return rc;
}

static inline void __vmx_inject_exception(
    struct vcpu *v, int trap, int type, int error_code)
{
    unsigned long intr_fields;

    /*
     * NB. Callers do not need to worry about clearing STI/MOV-SS blocking:
     *  "If the VM entry is injecting, there is no blocking by STI or by
     *   MOV SS following the VM entry, regardless of the contents of the
     *   interruptibility-state field [in the guest-state area before the
     *   VM entry]", PRM Vol. 3, 22.6.1 (Interruptibility State).
     */

    intr_fields = (INTR_INFO_VALID_MASK | (type<<8) | trap);
    if ( error_code != HVM_DELIVER_NO_ERROR_CODE ) {
        __vmwrite(VM_ENTRY_EXCEPTION_ERROR_CODE, error_code);
        intr_fields |= INTR_INFO_DELIVER_CODE_MASK;
    }

    __vmwrite(VM_ENTRY_INTR_INFO, intr_fields);

    if ( trap == TRAP_page_fault )
        HVMTRACE_2D(PF_INJECT, v, v->arch.hvm_vcpu.guest_cr[2], error_code);
    else
        HVMTRACE_2D(INJ_EXC, v, trap, error_code);
}

static inline void vmx_inject_hw_exception(
    struct vcpu *v, int trap, int error_code)
{
    __vmx_inject_exception(v, trap, X86_EVENTTYPE_HW_EXCEPTION, error_code);
}

static inline void vmx_inject_extint(struct vcpu *v, int trap)
{
    __vmx_inject_exception(v, trap, X86_EVENTTYPE_EXT_INTR,
                           HVM_DELIVER_NO_ERROR_CODE);
}

static inline void vmx_inject_nmi(struct vcpu *v)
{
    __vmx_inject_exception(v, 2, X86_EVENTTYPE_NMI,
                           HVM_DELIVER_NO_ERROR_CODE);
}

#endif /* __ASM_X86_HVM_VMX_VMX_H__ */
