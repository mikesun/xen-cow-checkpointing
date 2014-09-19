/*
 * io.c: Handling I/O and interrupts.
 *
 * Copyright (c) 2004, Intel Corporation.
 * Copyright (c) 2005, International Business Machines Corporation.
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

#include <xen/config.h>
#include <xen/init.h>
#include <xen/mm.h>
#include <xen/lib.h>
#include <xen/errno.h>
#include <xen/trace.h>
#include <xen/event.h>

#include <xen/hypercall.h>
#include <asm/current.h>
#include <asm/cpufeature.h>
#include <asm/processor.h>
#include <asm/msr.h>
#include <asm/apic.h>
#include <asm/paging.h>
#include <asm/shadow.h>
#include <asm/p2m.h>
#include <asm/hvm/hvm.h>
#include <asm/hvm/support.h>
#include <asm/hvm/vpt.h>
#include <asm/hvm/vpic.h>
#include <asm/hvm/vlapic.h>
#include <asm/hvm/trace.h>

#include <public/sched.h>
#include <xen/iocap.h>
#include <public/hvm/ioreq.h>

#if defined (__i386__)
static void set_reg_value (int size, int index, int seg, struct cpu_user_regs *regs, long value)
{
    switch (size) {
    case BYTE:
        switch (index) {
        case 0:
            regs->eax &= 0xFFFFFF00;
            regs->eax |= (value & 0xFF);
            break;
        case 1:
            regs->ecx &= 0xFFFFFF00;
            regs->ecx |= (value & 0xFF);
            break;
        case 2:
            regs->edx &= 0xFFFFFF00;
            regs->edx |= (value & 0xFF);
            break;
        case 3:
            regs->ebx &= 0xFFFFFF00;
            regs->ebx |= (value & 0xFF);
            break;
        case 4:
            regs->eax &= 0xFFFF00FF;
            regs->eax |= ((value & 0xFF) << 8);
            break;
        case 5:
            regs->ecx &= 0xFFFF00FF;
            regs->ecx |= ((value & 0xFF) << 8);
            break;
        case 6:
            regs->edx &= 0xFFFF00FF;
            regs->edx |= ((value & 0xFF) << 8);
            break;
        case 7:
            regs->ebx &= 0xFFFF00FF;
            regs->ebx |= ((value & 0xFF) << 8);
            break;
        default:
            goto crash;
        }
        break;
    case WORD:
        switch (index) {
        case 0:
            regs->eax &= 0xFFFF0000;
            regs->eax |= (value & 0xFFFF);
            break;
        case 1:
            regs->ecx &= 0xFFFF0000;
            regs->ecx |= (value & 0xFFFF);
            break;
        case 2:
            regs->edx &= 0xFFFF0000;
            regs->edx |= (value & 0xFFFF);
            break;
        case 3:
            regs->ebx &= 0xFFFF0000;
            regs->ebx |= (value & 0xFFFF);
            break;
        case 4:
            regs->esp &= 0xFFFF0000;
            regs->esp |= (value & 0xFFFF);
            break;
        case 5:
            regs->ebp &= 0xFFFF0000;
            regs->ebp |= (value & 0xFFFF);
            break;
        case 6:
            regs->esi &= 0xFFFF0000;
            regs->esi |= (value & 0xFFFF);
            break;
        case 7:
            regs->edi &= 0xFFFF0000;
            regs->edi |= (value & 0xFFFF);
            break;
        default:
            goto crash;
        }
        break;
    case LONG:
        switch (index) {
        case 0:
            regs->eax = value;
            break;
        case 1:
            regs->ecx = value;
            break;
        case 2:
            regs->edx = value;
            break;
        case 3:
            regs->ebx = value;
            break;
        case 4:
            regs->esp = value;
            break;
        case 5:
            regs->ebp = value;
            break;
        case 6:
            regs->esi = value;
            break;
        case 7:
            regs->edi = value;
            break;
        default:
            goto crash;
        }
        break;
    default:
    crash:
        gdprintk(XENLOG_ERR, "size:%x, index:%x are invalid!\n", size, index);
        domain_crash_synchronous();
    }
}
#else
static inline void __set_reg_value(unsigned long *reg, int size, long value)
{
    switch (size) {
    case BYTE_64:
        *reg &= ~0xFF;
        *reg |= (value & 0xFF);
        break;
    case WORD:
        *reg &= ~0xFFFF;
        *reg |= (value & 0xFFFF);
        break;
    case LONG:
        *reg &= ~0xFFFFFFFF;
        *reg |= (value & 0xFFFFFFFF);
        break;
    case QUAD:
        *reg = value;
        break;
    default:
        gdprintk(XENLOG_ERR, "size:%x is invalid\n", size);
        domain_crash_synchronous();
    }
}

static void set_reg_value (int size, int index, int seg, struct cpu_user_regs *regs, long value)
{
    if (size == BYTE) {
        switch (index) {
        case 0:
            regs->rax &= ~0xFF;
            regs->rax |= (value & 0xFF);
            break;
        case 1:
            regs->rcx &= ~0xFF;
            regs->rcx |= (value & 0xFF);
            break;
        case 2:
            regs->rdx &= ~0xFF;
            regs->rdx |= (value & 0xFF);
            break;
        case 3:
            regs->rbx &= ~0xFF;
            regs->rbx |= (value & 0xFF);
            break;
        case 4:
            regs->rax &= 0xFFFFFFFFFFFF00FF;
            regs->rax |= ((value & 0xFF) << 8);
            break;
        case 5:
            regs->rcx &= 0xFFFFFFFFFFFF00FF;
            regs->rcx |= ((value & 0xFF) << 8);
            break;
        case 6:
            regs->rdx &= 0xFFFFFFFFFFFF00FF;
            regs->rdx |= ((value & 0xFF) << 8);
            break;
        case 7:
            regs->rbx &= 0xFFFFFFFFFFFF00FF;
            regs->rbx |= ((value & 0xFF) << 8);
            break;
        default:
            gdprintk(XENLOG_ERR, "size:%x, index:%x are invalid!\n",
                     size, index);
            domain_crash_synchronous();
            break;
        }
        return;
    }

    switch (index) {
    case 0:
        __set_reg_value(&regs->rax, size, value);
        break;
    case 1:
        __set_reg_value(&regs->rcx, size, value);
        break;
    case 2:
        __set_reg_value(&regs->rdx, size, value);
        break;
    case 3:
        __set_reg_value(&regs->rbx, size, value);
        break;
    case 4:
        __set_reg_value(&regs->rsp, size, value);
        break;
    case 5:
        __set_reg_value(&regs->rbp, size, value);
        break;
    case 6:
        __set_reg_value(&regs->rsi, size, value);
        break;
    case 7:
        __set_reg_value(&regs->rdi, size, value);
        break;
    case 8:
        __set_reg_value(&regs->r8, size, value);
        break;
    case 9:
        __set_reg_value(&regs->r9, size, value);
        break;
    case 10:
        __set_reg_value(&regs->r10, size, value);
        break;
    case 11:
        __set_reg_value(&regs->r11, size, value);
        break;
    case 12:
        __set_reg_value(&regs->r12, size, value);
        break;
    case 13:
        __set_reg_value(&regs->r13, size, value);
        break;
    case 14:
        __set_reg_value(&regs->r14, size, value);
        break;
    case 15:
        __set_reg_value(&regs->r15, size, value);
        break;
    default:
        gdprintk(XENLOG_ERR, "Invalid index\n");
        domain_crash_synchronous();
    }
    return;
}
#endif

long get_reg_value(int size, int index, int seg, struct cpu_user_regs *regs);

static inline void set_eflags_CF(int size,
                                 unsigned int instr,
                                 unsigned long result,
                                 unsigned long src,
                                 unsigned long dst,
                                 struct cpu_user_regs *regs)
{
    unsigned long mask;

    if ( size == BYTE_64 )
        size = BYTE;
    ASSERT((size <= sizeof(mask)) && (size > 0));

    mask = ~0UL >> (8 * (sizeof(mask) - size));

    if ( instr == INSTR_ADD )
    {
        /* CF=1 <==> result is less than the augend and addend) */
        if ( (result & mask) < (dst & mask) )
        {
            ASSERT((result & mask) < (src & mask));
            regs->eflags |= X86_EFLAGS_CF;
        }
    }
    else
    {
        ASSERT( instr == INSTR_CMP || instr == INSTR_SUB );
        if ( (src & mask) > (dst & mask) )
            regs->eflags |= X86_EFLAGS_CF;
    }
}

static inline void set_eflags_OF(int size,
                                 unsigned int instr,
                                 unsigned long result,
                                 unsigned long src,
                                 unsigned long dst,
                                 struct cpu_user_regs *regs)
{
    unsigned long mask;

    if ( size == BYTE_64 )
        size = BYTE;
    ASSERT((size <= sizeof(mask)) && (size > 0));

    mask =  1UL << ((8*size) - 1);

    if ( instr == INSTR_ADD )
    {
        if ((src ^ result) & (dst ^ result) & mask);
            regs->eflags |= X86_EFLAGS_OF;
    }
    else
    {
        ASSERT(instr == INSTR_CMP || instr == INSTR_SUB);
        if ((dst ^ src) & (dst ^ result) & mask)
            regs->eflags |= X86_EFLAGS_OF;
    }
}

static inline void set_eflags_AF(int size,
                                 unsigned long result,
                                 unsigned long src,
                                 unsigned long dst,
                                 struct cpu_user_regs *regs)
{
    if ((result ^ src ^ dst) & 0x10)
        regs->eflags |= X86_EFLAGS_AF;
}

static inline void set_eflags_ZF(int size, unsigned long result,
                                 struct cpu_user_regs *regs)
{
    unsigned long mask;

    if ( size == BYTE_64 )
        size = BYTE;
    ASSERT((size <= sizeof(mask)) && (size > 0));

    mask = ~0UL >> (8 * (sizeof(mask) - size));

    if ((result & mask) == 0)
        regs->eflags |= X86_EFLAGS_ZF;
}

static inline void set_eflags_SF(int size, unsigned long result,
                                 struct cpu_user_regs *regs)
{
    unsigned long mask;

    if ( size == BYTE_64 )
        size = BYTE;
    ASSERT((size <= sizeof(mask)) && (size > 0));

    mask = 1UL << ((8*size) - 1);

    if (result & mask)
        regs->eflags |= X86_EFLAGS_SF;
}

static char parity_table[256] = {
    1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1,
    0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0,
    0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0,
    1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1,
    0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0,
    1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1,
    1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1,
    0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0,
    0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0,
    1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1,
    1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1,
    0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0,
    1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1,
    0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0,
    0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0,
    1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1
};

static inline void set_eflags_PF(int size, unsigned long result,
                                 struct cpu_user_regs *regs)
{
    if (parity_table[result & 0xFF])
        regs->eflags |= X86_EFLAGS_PF;
}

static void hvm_pio_assist(struct cpu_user_regs *regs, ioreq_t *p,
                           struct hvm_io_op *pio_opp)
{
    if ( p->data_is_ptr || (pio_opp->flags & OVERLAP) )
    {
        int sign = p->df ? -1 : 1;

        if ( pio_opp->flags & REPZ )
            regs->ecx -= p->count;

        if ( p->dir == IOREQ_READ )
        {
            if ( pio_opp->flags & OVERLAP )
            {
                unsigned long addr = pio_opp->addr;
                if ( hvm_paging_enabled(current) )
                {
                    int rv = hvm_copy_to_guest_virt(addr, &p->data, p->size);
                    if ( rv == HVMCOPY_bad_gva_to_gfn )
                        return; /* exception already injected */
                }
                else
                    (void)hvm_copy_to_guest_phys(addr, &p->data, p->size);
            }
            regs->edi += sign * p->count * p->size;
        }
        else /* p->dir == IOREQ_WRITE */
        {
            ASSERT(p->dir == IOREQ_WRITE);
            regs->esi += sign * p->count * p->size;
        }
    }
    else if ( p->dir == IOREQ_READ )
    {
        unsigned long old_eax = regs->eax;

        switch ( p->size )
        {
        case 1:
            regs->eax = (old_eax & ~0xff) | (p->data & 0xff);
            break;
        case 2:
            regs->eax = (old_eax & ~0xffff) | (p->data & 0xffff);
            break;
        case 4:
            regs->eax = (p->data & 0xffffffff);
            break;
        default:
            printk("Error: %s unknown port size\n", __FUNCTION__);
            domain_crash_synchronous();
        }
        HVMTRACE_1D(IO_ASSIST, current, p->data);
    }
}

static void hvm_mmio_assist(struct cpu_user_regs *regs, ioreq_t *p,
                            struct hvm_io_op *mmio_opp)
{
    int sign = p->df ? -1 : 1;
    int size = -1, index = -1;
    unsigned long value = 0, result = 0;
    unsigned long src, dst;

    src = mmio_opp->operand[0];
    dst = mmio_opp->operand[1];
    size = operand_size(src);

    HVMTRACE_1D(MMIO_ASSIST, current, p->data);
        
    switch (mmio_opp->instr) {
    case INSTR_MOV:
        if (dst & REGISTER) {
            index = operand_index(dst);
            set_reg_value(size, index, 0, regs, p->data);
        }
        break;

    case INSTR_MOVZX:
        if (dst & REGISTER) {
            switch (size) {
            case BYTE:
                p->data &= 0xFFULL;
                break;

            case WORD:
                p->data &= 0xFFFFULL;
                break;

            case LONG:
                p->data &= 0xFFFFFFFFULL;
                break;

            default:
                printk("Impossible source operand size of movzx instr: %d\n", size);
                domain_crash_synchronous();
            }
            index = operand_index(dst);
            set_reg_value(operand_size(dst), index, 0, regs, p->data);
        }
        break;

    case INSTR_MOVSX:
        if (dst & REGISTER) {
            switch (size) {
            case BYTE:
                p->data &= 0xFFULL;
                if ( p->data & 0x80ULL )
                    p->data |= 0xFFFFFFFFFFFFFF00ULL;
                break;

            case WORD:
                p->data &= 0xFFFFULL;
                if ( p->data & 0x8000ULL )
                    p->data |= 0xFFFFFFFFFFFF0000ULL;
                break;

            case LONG:
                p->data &= 0xFFFFFFFFULL;
                if ( p->data & 0x80000000ULL )
                    p->data |= 0xFFFFFFFF00000000ULL;
                break;

            default:
                printk("Impossible source operand size of movsx instr: %d\n", size);
                domain_crash_synchronous();
            }
            index = operand_index(dst);
            set_reg_value(operand_size(dst), index, 0, regs, p->data);
        }
        break;

    case INSTR_MOVS:
        sign = p->df ? -1 : 1;

        if (mmio_opp->flags & REPZ)
            regs->ecx -= p->count;

        if ((mmio_opp->flags & OVERLAP) && p->dir == IOREQ_READ) {
            unsigned long addr = mmio_opp->addr;

            if (hvm_paging_enabled(current))
            {
                int rv = hvm_copy_to_guest_virt(addr, &p->data, p->size);
                if ( rv == HVMCOPY_bad_gva_to_gfn )
                    return; /* exception already injected */
            }
            else
                (void)hvm_copy_to_guest_phys(addr, &p->data, p->size);
        }

        regs->esi += sign * p->count * p->size;
        regs->edi += sign * p->count * p->size;

        break;

    case INSTR_STOS:
        sign = p->df ? -1 : 1;
        regs->edi += sign * p->count * p->size;
        if (mmio_opp->flags & REPZ)
            regs->ecx -= p->count;
        break;

    case INSTR_LODS:
        set_reg_value(size, 0, 0, regs, p->data);
        sign = p->df ? -1 : 1;
        regs->esi += sign * p->count * p->size;
        if (mmio_opp->flags & REPZ)
            regs->ecx -= p->count;
        break;

    case INSTR_AND:
        if (src & REGISTER) {
            index = operand_index(src);
            value = get_reg_value(size, index, 0, regs);
            result = (unsigned long) p->data & value;
        } else if (src & IMMEDIATE) {
            value = mmio_opp->immediate;
            result = (unsigned long) p->data & value;
        } else if (src & MEMORY) {
            index = operand_index(dst);
            value = get_reg_value(size, index, 0, regs);
            result = (unsigned long) p->data & value;
            set_reg_value(size, index, 0, regs, result);
        }

        /*
         * The OF and CF flags are cleared; the SF, ZF, and PF
         * flags are set according to the result. The state of
         * the AF flag is undefined.
         */
        regs->eflags &= ~(X86_EFLAGS_CF|X86_EFLAGS_PF|
                          X86_EFLAGS_ZF|X86_EFLAGS_SF|X86_EFLAGS_OF);
        set_eflags_ZF(size, result, regs);
        set_eflags_SF(size, result, regs);
        set_eflags_PF(size, result, regs);
        break;

    case INSTR_ADD:
        if (src & REGISTER) {
            index = operand_index(src);
            value = get_reg_value(size, index, 0, regs);
            result = (unsigned long) p->data + value;
        } else if (src & IMMEDIATE) {
            value = mmio_opp->immediate;
            result = (unsigned long) p->data + value;
        } else if (src & MEMORY) {
            index = operand_index(dst);
            value = get_reg_value(size, index, 0, regs);
            result = (unsigned long) p->data + value;
            set_reg_value(size, index, 0, regs, result);
        }

        /*
         * The CF, OF, SF, ZF, AF, and PF flags are set according
         * to the result
         */
        regs->eflags &= ~(X86_EFLAGS_CF|X86_EFLAGS_PF|X86_EFLAGS_AF|
                          X86_EFLAGS_ZF|X86_EFLAGS_SF|X86_EFLAGS_OF);
        set_eflags_CF(size, mmio_opp->instr, result, value,
                      (unsigned long) p->data, regs);
        set_eflags_OF(size, mmio_opp->instr, result, value,
                      (unsigned long) p->data, regs);
        set_eflags_AF(size, result, value, (unsigned long) p->data, regs);
        set_eflags_ZF(size, result, regs);
        set_eflags_SF(size, result, regs);
        set_eflags_PF(size, result, regs);
        break;

    case INSTR_OR:
        if (src & REGISTER) {
            index = operand_index(src);
            value = get_reg_value(size, index, 0, regs);
            result = (unsigned long) p->data | value;
        } else if (src & IMMEDIATE) {
            value = mmio_opp->immediate;
            result = (unsigned long) p->data | value;
        } else if (src & MEMORY) {
            index = operand_index(dst);
            value = get_reg_value(size, index, 0, regs);
            result = (unsigned long) p->data | value;
            set_reg_value(size, index, 0, regs, result);
        }

        /*
         * The OF and CF flags are cleared; the SF, ZF, and PF
         * flags are set according to the result. The state of
         * the AF flag is undefined.
         */
        regs->eflags &= ~(X86_EFLAGS_CF|X86_EFLAGS_PF|
                          X86_EFLAGS_ZF|X86_EFLAGS_SF|X86_EFLAGS_OF);
        set_eflags_ZF(size, result, regs);
        set_eflags_SF(size, result, regs);
        set_eflags_PF(size, result, regs);
        break;

    case INSTR_XOR:
        if (src & REGISTER) {
            index = operand_index(src);
            value = get_reg_value(size, index, 0, regs);
            result = (unsigned long) p->data ^ value;
        } else if (src & IMMEDIATE) {
            value = mmio_opp->immediate;
            result = (unsigned long) p->data ^ value;
        } else if (src & MEMORY) {
            index = operand_index(dst);
            value = get_reg_value(size, index, 0, regs);
            result = (unsigned long) p->data ^ value;
            set_reg_value(size, index, 0, regs, result);
        }

        /*
         * The OF and CF flags are cleared; the SF, ZF, and PF
         * flags are set according to the result. The state of
         * the AF flag is undefined.
         */
        regs->eflags &= ~(X86_EFLAGS_CF|X86_EFLAGS_PF|
                          X86_EFLAGS_ZF|X86_EFLAGS_SF|X86_EFLAGS_OF);
        set_eflags_ZF(size, result, regs);
        set_eflags_SF(size, result, regs);
        set_eflags_PF(size, result, regs);
        break;

    case INSTR_CMP:
    case INSTR_SUB:
        if (src & REGISTER) {
            index = operand_index(src);
            value = get_reg_value(size, index, 0, regs);
            result = (unsigned long) p->data - value;
        } else if (src & IMMEDIATE) {
            value = mmio_opp->immediate;
            result = (unsigned long) p->data - value;
        } else if (src & MEMORY) {
            index = operand_index(dst);
            value = get_reg_value(size, index, 0, regs);
            result = value - (unsigned long) p->data;
            if ( mmio_opp->instr == INSTR_SUB )
                set_reg_value(size, index, 0, regs, result);
        }

        /*
         * The CF, OF, SF, ZF, AF, and PF flags are set according
         * to the result
         */
        regs->eflags &= ~(X86_EFLAGS_CF|X86_EFLAGS_PF|X86_EFLAGS_AF|
                          X86_EFLAGS_ZF|X86_EFLAGS_SF|X86_EFLAGS_OF);
        if ( src & (REGISTER | IMMEDIATE) )
        {
            set_eflags_CF(size, mmio_opp->instr, result, value,
                          (unsigned long) p->data, regs);
            set_eflags_OF(size, mmio_opp->instr, result, value,
                          (unsigned long) p->data, regs);
        }
        else
        {
            set_eflags_CF(size, mmio_opp->instr, result,
                          (unsigned long) p->data, value, regs);
            set_eflags_OF(size, mmio_opp->instr, result,
                          (unsigned long) p->data, value, regs);
        }
        set_eflags_AF(size, result, value, (unsigned long) p->data, regs);
        set_eflags_ZF(size, result, regs);
        set_eflags_SF(size, result, regs);
        set_eflags_PF(size, result, regs);
        break;

    case INSTR_TEST:
        if (src & REGISTER) {
            index = operand_index(src);
            value = get_reg_value(size, index, 0, regs);
        } else if (src & IMMEDIATE) {
            value = mmio_opp->immediate;
        } else if (src & MEMORY) {
            index = operand_index(dst);
            value = get_reg_value(size, index, 0, regs);
        }
        result = (unsigned long) p->data & value;

        /*
         * Sets the SF, ZF, and PF status flags. CF and OF are set to 0
         */
        regs->eflags &= ~(X86_EFLAGS_CF|X86_EFLAGS_PF|
                          X86_EFLAGS_ZF|X86_EFLAGS_SF|X86_EFLAGS_OF);
        set_eflags_ZF(size, result, regs);
        set_eflags_SF(size, result, regs);
        set_eflags_PF(size, result, regs);
        break;

    case INSTR_BT:
        if ( src & REGISTER )
        {
            index = operand_index(src);
            value = get_reg_value(size, index, 0, regs);
        }
        else if ( src & IMMEDIATE )
            value = mmio_opp->immediate;
        if (p->data & (1 << (value & ((1 << 5) - 1))))
            regs->eflags |= X86_EFLAGS_CF;
        else
            regs->eflags &= ~X86_EFLAGS_CF;

        break;

    case INSTR_XCHG:
        if (src & REGISTER) {
            index = operand_index(src);
            set_reg_value(size, index, 0, regs, p->data);
        } else {
            index = operand_index(dst);
            set_reg_value(size, index, 0, regs, p->data);
        }
        break;

    case INSTR_PUSH:
        mmio_opp->addr += hvm_get_segment_base(current, x86_seg_ss);
        {
            unsigned long addr = mmio_opp->addr;
            int rv = hvm_copy_to_guest_virt(addr, &p->data, size);
            if ( rv == HVMCOPY_bad_gva_to_gfn )
                return; /* exception already injected */
        }
        break;
    }
}

void hvm_io_assist(void)
{
    vcpu_iodata_t *vio;
    ioreq_t *p;
    struct cpu_user_regs *regs;
    struct hvm_io_op *io_opp;
    struct vcpu *v = current;

    io_opp = &v->arch.hvm_vcpu.io_op;
    regs   = &io_opp->io_context;
    vio    = get_ioreq(v);

    p = &vio->vp_ioreq;
    if ( p->state != STATE_IORESP_READY )
    {
        gdprintk(XENLOG_ERR, "Unexpected HVM iorequest state %d.\n", p->state);
        domain_crash(v->domain);
        goto out;
    }

    rmb(); /* see IORESP_READY /then/ read contents of ioreq */

    p->state = STATE_IOREQ_NONE;

    if ( v->arch.hvm_vcpu.io_complete && v->arch.hvm_vcpu.io_complete() )
        goto out;

    switch ( p->type )
    {
    case IOREQ_TYPE_INVALIDATE:
        goto out;
    case IOREQ_TYPE_PIO:
        hvm_pio_assist(regs, p, io_opp);
        break;
    default:
        hvm_mmio_assist(regs, p, io_opp);
        break;
    }

    /* Copy register changes back into current guest state. */
    regs->eflags &= ~X86_EFLAGS_RF;
    memcpy(guest_cpu_user_regs(), regs, HVM_CONTEXT_STACK_BYTES);
    if ( regs->eflags & X86_EFLAGS_TF )
        hvm_inject_exception(TRAP_debug, HVM_DELIVER_NO_ERROR_CODE, 0);

 out:
    vcpu_end_shutdown_deferral(v);
}

void dpci_ioport_read(uint32_t mport, ioreq_t *p)
{
    uint64_t i;
    uint64_t z_data;
    uint64_t length = (p->count * p->size);

    for ( i = 0; i < length; i += p->size )
    {
        z_data = ~0ULL;
        
        switch ( p->size )
        {
        case BYTE:
            z_data = (uint64_t)inb(mport);
            break;
        case WORD:
            z_data = (uint64_t)inw(mport);
            break;
        case LONG:
            z_data = (uint64_t)inl(mport);
            break;
        default:
            gdprintk(XENLOG_ERR, "Error: unable to handle size: %"
                     PRId64 "\n", p->size);
            return;
        }

        p->data = z_data;
        if ( p->data_is_ptr &&
             hvm_copy_to_guest_phys(p->data + i, (void *)&z_data,
                                    (int)p->size) )
        {
            gdprintk(XENLOG_ERR, "Error: couldn't copy to hvm phys\n");
            return;
        }
    }
}

void dpci_ioport_write(uint32_t mport, ioreq_t *p)
{
    uint64_t i;
    uint64_t z_data = 0;
    uint64_t length = (p->count * p->size);

    for ( i = 0; i < length; i += p->size )
    {
        z_data = p->data;
        if ( p->data_is_ptr &&
             hvm_copy_from_guest_phys((void *)&z_data,
                                      p->data + i, (int)p->size) )
        {
            gdprintk(XENLOG_ERR, "Error: couldn't copy from hvm phys\n");
            return;
        }

        switch ( p->size )
        {
        case BYTE:
            outb((uint8_t) z_data, mport);
            break;
        case WORD:
            outw((uint16_t) z_data, mport);
            break;
        case LONG:
            outl((uint32_t) z_data, mport);
            break;
        default:
            gdprintk(XENLOG_ERR, "Error: unable to handle size: %"
                     PRId64 "\n", p->size);
            break;
        }
    }
}

int dpci_ioport_intercept(ioreq_t *p)
{
    struct domain *d = current->domain;
    struct hvm_iommu *hd = domain_hvm_iommu(d);
    struct g2m_ioport *g2m_ioport;
    unsigned int mport, gport = p->addr;
    unsigned int s = 0, e = 0;

    list_for_each_entry( g2m_ioport, &hd->g2m_ioport_list, list )
    {
        s = g2m_ioport->gport;
        e = s + g2m_ioport->np;
        if ( (gport >= s) && (gport < e) )
            goto found;
    }

    return 0;

 found:
    mport = (gport - s) + g2m_ioport->mport;

    if ( !ioports_access_permitted(d, mport, mport + p->size - 1) ) 
    {
        gdprintk(XENLOG_ERR, "Error: access to gport=0x%x denied!\n",
                 (uint32_t)p->addr);
        return 0;
    }

    switch ( p->dir )
    {
    case IOREQ_READ:
        dpci_ioport_read(mport, p);
        break;
    case IOREQ_WRITE:
        dpci_ioport_write(mport, p);
        break;
    default:
        gdprintk(XENLOG_ERR, "Error: couldn't handle p->dir = %d", p->dir);
    }

    return 1;
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
