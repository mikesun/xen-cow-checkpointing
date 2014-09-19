/*
 * vm86.c: A vm86 emulator. The main purpose of this emulator is to do as
 * little work as possible.
 *
 * Leendert van Doorn, leendert@watson.ibm.com
 * Copyright (c) 2005-2006, International Business Machines Corporation.
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
#include "vm86.h"
#include "util.h"
#include "machine.h"

#define	HIGHMEM		(1 << 20)		/* 1MB */
#define	MASK16(v)	((v) & 0xFFFF)

#define	DATA32		0x0001
#define	ADDR32		0x0002
#define	SEG_CS		0x0004
#define	SEG_DS		0x0008
#define	SEG_ES		0x0010
#define	SEG_SS		0x0020
#define	SEG_FS		0x0040
#define	SEG_GS		0x0080
#define REP		0x0100

static unsigned prev_eip = 0;
enum vm86_mode mode = 0;

static struct regs saved_rm_regs;

#ifdef DEBUG
int traceset = 0;

char *states[] = {
	"<VM86_REAL>",
	"<VM86_REAL_TO_PROTECTED>",
	"<VM86_PROTECTED_TO_REAL>",
	"<VM86_PROTECTED>"
};

static char *rnames[] = { "ax", "cx", "dx", "bx", "sp", "bp", "si", "di" };
#endif /* DEBUG */

#define PDE_PS				(1 << 7)
#define PT_ENTRY_PRESENT	0x1

/* We only support access to <=4G physical memory due to 1:1 mapping */
static uint64_t
guest_linear_to_phys(uint32_t base)
{
	uint32_t gcr3 = oldctx.cr3;
	uint64_t l2_mfn;
	uint64_t l1_mfn;
	uint64_t l0_mfn;

	if (!(oldctx.cr0 & CR0_PG))
		return base;

	if (!(oldctx.cr4 & CR4_PAE)) {
		l1_mfn = ((uint32_t *)(long)gcr3)[(base >> 22) & 0x3ff];
		if (!(l1_mfn & PT_ENTRY_PRESENT))
			panic("l2 entry not present\n");

		if ((oldctx.cr4 & CR4_PSE) && (l1_mfn & PDE_PS)) {
			l0_mfn = l1_mfn & 0xffc00000;
			return l0_mfn + (base & 0x3fffff);
		}

		l1_mfn &= 0xfffff000;

		l0_mfn = ((uint32_t *)(long)l1_mfn)[(base >> 12) & 0x3ff];
		if (!(l0_mfn & PT_ENTRY_PRESENT))
			panic("l1 entry not present\n");
		l0_mfn &= 0xfffff000;

		return l0_mfn + (base & 0xfff);
	} else {
		l2_mfn = ((uint64_t *)(long)gcr3)[(base >> 30) & 0x3];
		if (!(l2_mfn & PT_ENTRY_PRESENT))
			panic("l3 entry not present\n");
		l2_mfn &= 0xffffff000ULL;

		if (l2_mfn & 0xf00000000ULL) {
			printf("l2 page above 4G\n");
			cpuid_addr_value(l2_mfn + 8 * ((base >> 21) & 0x1ff), &l1_mfn);
		} else
			l1_mfn = ((uint64_t *)(long)l2_mfn)[(base >> 21) & 0x1ff];
		if (!(l1_mfn & PT_ENTRY_PRESENT))
			panic("l2 entry not present\n");

		if (l1_mfn & PDE_PS) { /* CR4.PSE is ignored in PAE mode */
			l0_mfn = l1_mfn & 0xfffe00000ULL;
			return l0_mfn + (base & 0x1fffff);
		}

		l1_mfn &= 0xffffff000ULL;

		if (l1_mfn & 0xf00000000ULL) {
			printf("l1 page above 4G\n");
			cpuid_addr_value(l1_mfn + 8 * ((base >> 12) & 0x1ff), &l0_mfn);
		} else
			l0_mfn = ((uint64_t *)(long)l1_mfn)[(base >> 12) & 0x1ff];
		if (!(l0_mfn & PT_ENTRY_PRESENT))
			panic("l1 entry not present\n");

		l0_mfn &= 0xffffff000ULL;

		return l0_mfn + (base & 0xfff);
	}
}

static unsigned
address(struct regs *regs, unsigned seg, unsigned off)
{
	uint64_t gdt_phys_base;
	unsigned long long entry;
	unsigned seg_base, seg_limit;
	unsigned entry_low, entry_high;

	if (seg == 0) {
		if (mode == VM86_REAL || mode == VM86_REAL_TO_PROTECTED)
			return off;
		else
			panic("segment is zero, but not in real mode!\n");
	}

	if (mode == VM86_REAL || seg > oldctx.gdtr_limit ||
		(mode == VM86_REAL_TO_PROTECTED && regs->cs == seg))
		return ((seg & 0xFFFF) << 4) + off;

	gdt_phys_base = guest_linear_to_phys(oldctx.gdtr_base);
	if (gdt_phys_base != (uint32_t)gdt_phys_base) {
		printf("gdt base address above 4G\n");
		cpuid_addr_value(gdt_phys_base + 8 * (seg >> 3), &entry);
	} else
		entry = ((unsigned long long *)(long)gdt_phys_base)[seg >> 3];

	entry_high = entry >> 32;
	entry_low = entry & 0xFFFFFFFF;

	seg_base  = (entry_high & 0xFF000000) | ((entry >> 16) & 0xFFFFFF);
	seg_limit = (entry_high & 0xF0000) | (entry_low & 0xFFFF);

	if (entry_high & 0x8000 &&
		((entry_high & 0x800000 && off >> 12 <= seg_limit) ||
		(!(entry_high & 0x800000) && off <= seg_limit)))
		return seg_base + off;

	panic("should never reach here in function address():\n\t"
		  "entry=0x%08x%08x, mode=%d, seg=0x%08x, offset=0x%08x\n",
		  entry_high, entry_low, mode, seg, off);

	return 0;
}

#ifdef DEBUG
void
trace(struct regs *regs, int adjust, char *fmt, ...)
{
	unsigned off = regs->eip - adjust;
	va_list ap;

	if ((traceset & (1 << mode)) &&
		(mode == VM86_REAL_TO_PROTECTED || mode == VM86_REAL)) {
		/* 16-bit, seg:off addressing */
		unsigned addr = address(regs, regs->cs, off);
		printf("0x%08x: 0x%x:0x%04x ", addr, regs->cs, off);
		printf("(%d) ", mode);
		va_start(ap, fmt);
		vprintf(fmt, ap);
		va_end(ap);
		printf("\n");
	}
	if ((traceset & (1 << mode)) &&
		(mode == VM86_PROTECTED_TO_REAL || mode == VM86_PROTECTED)) {
		/* 16-bit, gdt addressing */
		unsigned addr = address(regs, regs->cs, off);
		printf("0x%08x: 0x%x:0x%08x ", addr, regs->cs, off);
		printf("(%d) ", mode);
		va_start(ap, fmt);
		vprintf(fmt, ap);
		va_end(ap);
		printf("\n");
	}
}
#endif /* DEBUG */

static inline unsigned
read32(unsigned addr)
{
	return *(unsigned long *) addr;
}

static inline unsigned
read16(unsigned addr)
{
	return *(unsigned short *) addr;
}

static inline unsigned
read8(unsigned addr)
{
	return *(unsigned char *) addr;
}

static inline void
write32(unsigned addr, unsigned value)
{
	*(unsigned long *) addr = value;
}

static inline void
write16(unsigned addr, unsigned value)
{
	*(unsigned short *) addr = value;
}

static inline void
write8(unsigned addr, unsigned value)
{
	*(unsigned char *) addr = value;
}

static inline void
push32(struct regs *regs, unsigned value)
{
	regs->uesp -= 4;
	write32(address(regs, regs->uss, MASK16(regs->uesp)), value);
}

static inline void
push16(struct regs *regs, unsigned value)
{
	regs->uesp -= 2;
	write16(address(regs, regs->uss, MASK16(regs->uesp)), value);
}

static inline unsigned
pop32(struct regs *regs)
{
	unsigned value = read32(address(regs, regs->uss, MASK16(regs->uesp)));
	regs->uesp += 4;
	return value;
}

static inline unsigned
pop16(struct regs *regs)
{
	unsigned value = read16(address(regs, regs->uss, MASK16(regs->uesp)));
	regs->uesp += 2;
	return value;
}

static inline unsigned
fetch32(struct regs *regs)
{
	unsigned addr = address(regs, regs->cs, MASK16(regs->eip));

	regs->eip += 4;
	return read32(addr);
}

static inline unsigned
fetch16(struct regs *regs)
{
	unsigned addr = address(regs, regs->cs, MASK16(regs->eip));

	regs->eip += 2;
	return read16(addr);
}

static inline unsigned
fetch8(struct regs *regs)
{
	unsigned addr = address(regs, regs->cs, MASK16(regs->eip));

	regs->eip++;
	return read8(addr);
}

static unsigned
getreg32(struct regs *regs, int r)
{
	switch (r & 7) {
	case 0: return regs->eax;
	case 1: return regs->ecx;
	case 2: return regs->edx;
	case 3: return regs->ebx;
	case 4: return regs->uesp;
	case 5: return regs->ebp;
	case 6: return regs->esi;
	case 7: return regs->edi;
	}
	return ~0;
}

static unsigned
getreg16(struct regs *regs, int r)
{
	return MASK16(getreg32(regs, r));
}

static unsigned
getreg8(struct regs *regs, int r)
{
	switch (r & 7) {
	case 0: return regs->eax & 0xFF; /* al */
	case 1: return regs->ecx & 0xFF; /* cl */
	case 2: return regs->edx & 0xFF; /* dl */
	case 3: return regs->ebx & 0xFF; /* bl */
	case 4: return (regs->eax >> 8) & 0xFF; /* ah */
	case 5: return (regs->ecx >> 8) & 0xFF; /* ch */
	case 6: return (regs->edx >> 8) & 0xFF; /* dh */
	case 7: return (regs->ebx >> 8) & 0xFF; /* bh */
	}
	return ~0;
}

static void
setreg32(struct regs *regs, int r, unsigned v)
{
	switch (r & 7) {
	case 0: regs->eax = v; break;
	case 1: regs->ecx = v; break;
	case 2: regs->edx = v; break;
	case 3: regs->ebx = v; break;
	case 4: regs->uesp = v; break;
	case 5: regs->ebp = v; break;
	case 6: regs->esi = v; break;
	case 7: regs->edi = v; break;
	}
}

static void
setreg16(struct regs *regs, int r, unsigned v)
{
	setreg32(regs, r, (getreg32(regs, r) & ~0xFFFF) | MASK16(v));
}

static void
setreg8(struct regs *regs, int r, unsigned v)
{
	v &= 0xFF;
	switch (r & 7) {
	case 0: regs->eax = (regs->eax & ~0xFF) | v; break;
	case 1: regs->ecx = (regs->ecx & ~0xFF) | v; break;
	case 2: regs->edx = (regs->edx & ~0xFF) | v; break;
	case 3: regs->ebx = (regs->ebx & ~0xFF) | v; break;
	case 4: regs->eax = (regs->eax & ~0xFF00) | (v << 8); break;
	case 5: regs->ecx = (regs->ecx & ~0xFF00) | (v << 8); break;
	case 6: regs->edx = (regs->edx & ~0xFF00) | (v << 8); break;
	case 7: regs->ebx = (regs->ebx & ~0xFF00) | (v << 8); break;
	}
}

static unsigned
segment(unsigned prefix, struct regs *regs, unsigned seg)
{
	if (prefix & SEG_ES)
		seg = regs->ves;
	if (prefix & SEG_DS)
		seg = regs->vds;
	if (prefix & SEG_CS)
		seg = regs->cs;
	if (prefix & SEG_SS)
		seg = regs->uss;
	if (prefix & SEG_FS)
		seg = regs->vfs;
	if (prefix & SEG_GS)
		seg = regs->vgs;
	return seg;
}

static unsigned
sib(struct regs *regs, int mod, unsigned byte)
{
	unsigned scale = (byte >> 6) & 3;
	int index = (byte >> 3) & 7;
	int base = byte & 7;
	unsigned addr = 0;

	switch (mod) {
	case 0:
		if (base == 5)
			addr = fetch32(regs);
		else
			addr = getreg32(regs, base);
		break;
	case 1:
		addr = getreg32(regs, base) + (char) fetch8(regs);
		break;
	case 2:
		addr = getreg32(regs, base) + fetch32(regs);
		break;
	}

	if (index != 4)
		addr += getreg32(regs, index) << scale;

	return addr;
}

/*
 * Operand (modrm) decode
 */
static unsigned
operand(unsigned prefix, struct regs *regs, unsigned modrm)
{
	int mod, disp = 0, seg;

	seg = segment(prefix, regs, regs->vds);

	if (prefix & ADDR32) { /* 32-bit addressing */
		switch ((mod = (modrm >> 6) & 3)) {
		case 0:
			switch (modrm & 7) {
			case 0: return address(regs, seg, regs->eax);
			case 1: return address(regs, seg, regs->ecx);
			case 2: return address(regs, seg, regs->edx);
			case 3: return address(regs, seg, regs->ebx);
			case 4: return address(regs, seg,
						   sib(regs, mod, fetch8(regs)));
			case 5: return address(regs, seg, fetch32(regs));
			case 6: return address(regs, seg, regs->esi);
			case 7: return address(regs, seg, regs->edi);
			}
			break;
		case 1:
		case 2:
			if ((modrm & 7) != 4) {
				if (mod == 1)
					disp = (char) fetch8(regs);
				else
					disp = (int) fetch32(regs);
			}
			switch (modrm & 7) {
			case 0: return address(regs, seg, regs->eax + disp);
			case 1: return address(regs, seg, regs->ecx + disp);
			case 2: return address(regs, seg, regs->edx + disp);
			case 3: return address(regs, seg, regs->ebx + disp);
			case 4: return address(regs, seg,
						   sib(regs, mod, fetch8(regs)));
			case 5: return address(regs, seg, regs->ebp + disp);
			case 6: return address(regs, seg, regs->esi + disp);
			case 7: return address(regs, seg, regs->edi + disp);
			}
			break;
		case 3:
			return getreg32(regs, modrm);
		}
	} else { /* 16-bit addressing */
		switch ((mod = (modrm >> 6) & 3)) {
		case 0:
			switch (modrm & 7) {
			case 0: return address(regs, seg, MASK16(regs->ebx) +
					MASK16(regs->esi));
			case 1: return address(regs, seg, MASK16(regs->ebx) +
					MASK16(regs->edi));
			case 2: return address(regs, seg, MASK16(regs->ebp) +
					MASK16(regs->esi));
			case 3: return address(regs, seg, MASK16(regs->ebp) +
					MASK16(regs->edi));
			case 4: return address(regs, seg, MASK16(regs->esi));
			case 5: return address(regs, seg, MASK16(regs->edi));
			case 6: return address(regs, seg, fetch16(regs));
			case 7: return address(regs, seg, MASK16(regs->ebx));
			}
			break;
		case 1:
		case 2:
			if (mod == 1)
				disp = (char) fetch8(regs);
			else
				disp = (int) fetch16(regs);
			switch (modrm & 7) {
			case 0: return address(regs, seg, MASK16(regs->ebx) +
					MASK16(regs->esi) + disp);
			case 1: return address(regs, seg, MASK16(regs->ebx) +
					MASK16(regs->edi) + disp);
			case 2: return address(regs, seg, MASK16(regs->ebp) +
					MASK16(regs->esi) + disp);
			case 3: return address(regs, seg, MASK16(regs->ebp) +
					MASK16(regs->edi) + disp);
			case 4: return address(regs, seg,
					MASK16(regs->esi) + disp);
			case 5: return address(regs, seg,
					MASK16(regs->edi) + disp);
			case 6: return address(regs, seg,
					MASK16(regs->ebp) + disp);
			case 7: return address(regs, seg,
					MASK16(regs->ebx) + disp);
			}
			break;
		case 3:
			return getreg16(regs, modrm);
		}
	}

	return 0;
}

/*
 * Load new IDT
 */
static int
lidt(struct regs *regs, unsigned prefix, unsigned modrm)
{
	unsigned eip = regs->eip - 3;
	unsigned addr = operand(prefix, regs, modrm);

	oldctx.idtr_limit = ((struct dtr *) addr)->size;
	if ((prefix & DATA32) == 0)
		oldctx.idtr_base = ((struct dtr *) addr)->base & 0xFFFFFF;
	else
		oldctx.idtr_base = ((struct dtr *) addr)->base;
	TRACE((regs, regs->eip - eip, "lidt 0x%x <%d, 0x%x>",
		addr, oldctx.idtr_limit, oldctx.idtr_base));

	return 1;
}

/*
 * Load new GDT
 */
static int
lgdt(struct regs *regs, unsigned prefix, unsigned modrm)
{
	unsigned eip = regs->eip - 3;
	unsigned addr = operand(prefix, regs, modrm);

	oldctx.gdtr_limit = ((struct dtr *) addr)->size;
	if ((prefix & DATA32) == 0)
		oldctx.gdtr_base = ((struct dtr *) addr)->base & 0xFFFFFF;
	else
		oldctx.gdtr_base = ((struct dtr *) addr)->base;
	TRACE((regs, regs->eip - eip, "lgdt 0x%x <%d, 0x%x>",
		addr, oldctx.gdtr_limit, oldctx.gdtr_base));

	return 1;
}

/*
 * Modify CR0 either through an lmsw instruction.
 */
static int
lmsw(struct regs *regs, unsigned prefix, unsigned modrm)
{
	unsigned eip = regs->eip - 3;
	unsigned ax = operand(prefix, regs, modrm) & 0xF;
	unsigned cr0 = (oldctx.cr0 & 0xFFFFFFF0) | ax;

	TRACE((regs, regs->eip - eip, "lmsw 0x%x", ax));
	oldctx.cr0 = cr0 | CR0_PE | CR0_NE;
	if (cr0 & CR0_PE)
		set_mode(regs, VM86_REAL_TO_PROTECTED);

	return 1;
}

/*
 * We need to handle moves that address memory beyond the 64KB segment
 * limit that VM8086 mode enforces.
 */
static int
movr(struct regs *regs, unsigned prefix, unsigned opc)
{
	unsigned eip = regs->eip - 1;
	unsigned modrm = fetch8(regs);
	unsigned addr = operand(prefix, regs, modrm);
	unsigned val, r = (modrm >> 3) & 7;

	if ((modrm & 0xC0) == 0xC0) {
		/*
		 * Emulate all guest instructions in protected to real mode.
		 */
		if (mode != VM86_PROTECTED_TO_REAL)
			return 0;
	}

	switch (opc) {
	case 0x88: /* addr32 mov r8, r/m8 */
		val = getreg8(regs, r);
		TRACE((regs, regs->eip - eip,
			"movb %%e%s, *0x%x", rnames[r], addr));
		write8(addr, val);
		return 1;

	case 0x8A: /* addr32 mov r/m8, r8 */
		TRACE((regs, regs->eip - eip,
			"movb *0x%x, %%%s", addr, rnames[r]));
		setreg8(regs, r, read8(addr));
		return 1;

	case 0x89: /* addr32 mov r16, r/m16 */
		val = getreg32(regs, r);
		if ((modrm & 0xC0) == 0xC0) {
			if (prefix & DATA32)
				setreg32(regs, modrm & 7, val);
			else
				setreg16(regs, modrm & 7, MASK16(val));
			return 1;
		}

		if (prefix & DATA32) {
			TRACE((regs, regs->eip - eip,
				"movl %%e%s, *0x%x", rnames[r], addr));
			write32(addr, val);
		} else {
			TRACE((regs, regs->eip - eip,
				"movw %%%s, *0x%x", rnames[r], addr));
			write16(addr, MASK16(val));
		}
		return 1;

	case 0x8B: /* mov r/m16, r16 */
		if ((modrm & 0xC0) == 0xC0) {
			if (prefix & DATA32)
				setreg32(regs, r, addr);
			else
				setreg16(regs, r, MASK16(addr));
			return 1;
		}

		if (prefix & DATA32) {
			TRACE((regs, regs->eip - eip,
				"movl *0x%x, %%e%s", addr, rnames[r]));
			setreg32(regs, r, read32(addr));
		} else {
			TRACE((regs, regs->eip - eip,
				"movw *0x%x, %%%s", addr, rnames[r]));
			setreg16(regs, r, read16(addr));
		}
		return 1;

	case 0xC6: /* addr32 movb $imm, r/m8 */
		if ((modrm >> 3) & 7)
			return 0;
		val = fetch8(regs);
		write8(addr, val);
		TRACE((regs, regs->eip - eip, "movb $0x%x, *0x%x",
							val, addr));
		return 1;
	}
	return 0;
}

/*
 * We need to handle string moves that address memory beyond the 64KB segment
 * limit that VM8086 mode enforces.
 */
static inline int
movs(struct regs *regs, unsigned prefix, unsigned opc)
{
	unsigned eip = regs->eip - 1;
	unsigned sseg = segment(prefix, regs, regs->vds);
	unsigned dseg = regs->ves;
	unsigned saddr, daddr;
	unsigned count = 1;
	int incr = ((regs->eflags & EFLAGS_DF) == 0) ? 1 : -1;

	saddr = address(regs, sseg, regs->esi);
	daddr = address(regs, dseg, regs->edi);

	if ((prefix & REP) != 0) {
		count = regs->ecx;
		regs->ecx = 0;
	}

	switch (opc) {
	case 0xA4: /* movsb */
		regs->esi += (incr * count);
		regs->edi += (incr * count);

		while (count-- != 0) {
			write8(daddr, read8(saddr));
			daddr += incr;
			saddr += incr;
		}
		TRACE((regs, regs->eip - eip, "movsb (%%esi),%%es:(%%edi)"));
		break;

	case 0xA5: /* movsw */
		if ((prefix & DATA32) == 0) {
			incr = 2 * incr;
			regs->esi += (incr * count);
			regs->edi += (incr * count);

			while (count-- != 0) {
				write16(daddr, read16(saddr));
				daddr += incr;
				saddr += incr;
			}
		} else {
			incr = 4 * incr;
			regs->esi += (incr * count);
			regs->edi += (incr * count);

			while (count-- != 0) {
				write32(daddr, read32(saddr));
				daddr += incr;
				saddr += incr;
			}
		}			
		TRACE((regs, regs->eip - eip, "movsw %s(%%esi),%%es:(%%edi)"));
		break;
	}

	return 1;
}

static inline int
lods(struct regs *regs, unsigned prefix, unsigned opc)
{
	unsigned eip = regs->eip - 1;
	unsigned seg = segment(prefix, regs, regs->vds);
	unsigned addr = address(regs, seg, regs->esi);
	unsigned count = 1;
	int incr = ((regs->eflags & EFLAGS_DF) == 0) ? 1 : -1;

	if ((prefix & REP) != 0) {
		count = regs->ecx;
		regs->ecx = 0;
	}

	switch (opc) {
	case 0xAD: /* lodsw */
		if ((prefix & DATA32) == 0) {
			incr = 2 * incr;
			regs->esi += (incr * count);
			while (count-- != 0) {
				setreg16(regs, 0, read16(addr));
				addr += incr;
			}

			TRACE((regs, regs->eip - eip, "lodsw (%%esi),%%ax"));
		} else {
			incr = 4 * incr;
			regs->esi += (incr * count);
			while (count-- != 0) {
				setreg32(regs, 0, read32(addr));
				addr += incr;
			}
			TRACE((regs, regs->eip - eip, "lodsw (%%esi),%%eax"));
		}
		break;
	}
	return 1;
}
/*
 * Move to and from a control register.
 */
static int
movcr(struct regs *regs, unsigned prefix, unsigned opc)
{
	unsigned eip = regs->eip - 2;
	unsigned modrm = fetch8(regs);
	unsigned cr = (modrm >> 3) & 7;

	if ((modrm & 0xC0) != 0xC0) /* only registers */
		return 0;

	switch (opc) {
	case 0x20: /* mov Rd, Cd */
		TRACE((regs, regs->eip - eip, "movl %%cr%d, %%eax", cr));
		switch (cr) {
		case 0:
			setreg32(regs, modrm,
				oldctx.cr0 & ~(CR0_PE | CR0_NE));
			break;
		case 2:
			setreg32(regs, modrm, get_cr2());
			break;
		case 3:
			setreg32(regs, modrm, oldctx.cr3);
			break;
		case 4:
			setreg32(regs, modrm, oldctx.cr4);
			break;
		}
		break;
	case 0x22: /* mov Cd, Rd */
		TRACE((regs, regs->eip - eip, "movl %%eax, %%cr%d", cr));
		switch (cr) {
		case 0:
			oldctx.cr0 = getreg32(regs, modrm) | (CR0_PE | CR0_NE);
			if (getreg32(regs, modrm) & CR0_PE)
				set_mode(regs, VM86_REAL_TO_PROTECTED);
			else
				set_mode(regs, VM86_REAL);
			break;
		case 3:
			oldctx.cr3 = getreg32(regs, modrm);
			break;
		case 4:
			oldctx.cr4 = getreg32(regs, modrm);
			break;
		}
		break;
	}

	return 1;
}

static inline void set_eflags_ZF(unsigned mask, unsigned v1, struct regs *regs)
{
	if ((v1 & mask) == 0)
		regs->eflags |= EFLAGS_ZF;
	else
		regs->eflags &= ~EFLAGS_ZF;
}

static void set_eflags_add(unsigned hi_bit_mask, unsigned v1, unsigned v2,
				unsigned result, struct regs *regs)
{
	int bit_count;
	unsigned tmp;
	unsigned full_mask;
	unsigned nonsign_mask;

	/* Carry out of high order bit? */
	if ( v1 & v2 & hi_bit_mask )
		regs->eflags |= EFLAGS_CF;
	else
		regs->eflags &= ~EFLAGS_CF;

	/* Even parity in least significant byte? */
	tmp = result & 0xff;
	for (bit_count = 0; tmp != 0; bit_count++)
		tmp &= (tmp - 1);

	if (bit_count & 1)
		regs->eflags &= ~EFLAGS_PF;
	else
		regs->eflags |= EFLAGS_PF;

	/* Carry out of least significant BCD digit? */
	if ( v1 & v2 & (1<<3) )
		regs->eflags |= EFLAGS_AF;
	else
		regs->eflags &= ~EFLAGS_AF;

	/* Result is zero? */
	full_mask = (hi_bit_mask - 1) | hi_bit_mask;
	set_eflags_ZF(full_mask, result, regs);

	/* Sign of result? */
	if ( result & hi_bit_mask )
		regs->eflags |= EFLAGS_SF;
	else
		regs->eflags &= ~EFLAGS_SF;

	/* Carry out of highest non-sign bit? */
	nonsign_mask = (hi_bit_mask >> 1) & ~hi_bit_mask;
	if ( v1 & v2 & hi_bit_mask )
		regs->eflags |= EFLAGS_OF;
	else
		regs->eflags &= ~EFLAGS_OF;

}

/*
 * We need to handle cmp opcodes that address memory beyond the 64KB
 * segment limit that VM8086 mode enforces.
 */
static int
cmp(struct regs *regs, unsigned prefix, unsigned opc)
{
	unsigned eip = regs->eip - 1;
	unsigned modrm = fetch8(regs);
	unsigned addr = operand(prefix, regs, modrm);
	unsigned diff, val, r = (modrm >> 3) & 7;

	if ((modrm & 0xC0) == 0xC0) /* no registers */
		return 0;

	switch (opc) {
	case 0x39: /* addr32 cmp r16, r/m16 */
		val = getreg32(regs, r);
		if (prefix & DATA32) {
			diff = read32(addr) - val;
			set_eflags_ZF(~0, diff, regs);

			TRACE((regs, regs->eip - eip,
				"cmp %%e%s, *0x%x (0x%x)",
				rnames[r], addr, diff));
		} else {
			diff = read16(addr) - val;
			set_eflags_ZF(0xFFFF, diff, regs);

			TRACE((regs, regs->eip - eip,
				"cmp %%%s, *0x%x (0x%x)",
				rnames[r], addr, diff));
		}
		break;

	/* other cmp opcodes ... */
	}
	return 1;
}

/*
 * We need to handle test opcodes that address memory beyond the 64KB
 * segment limit that VM8086 mode enforces.
 */
static int
test(struct regs *regs, unsigned prefix, unsigned opc)
{
	unsigned eip = regs->eip - 1;
	unsigned modrm = fetch8(regs);
	unsigned addr = operand(prefix, regs, modrm);
	unsigned val, diff;

	if ((modrm & 0xC0) == 0xC0) /* no registers */
		return 0;

	switch (opc) {
	case 0xF6: /* testb $imm, r/m8 */
		if ((modrm >> 3) & 7)
			return 0;
		val = fetch8(regs);
		diff = read8(addr) & val;
		set_eflags_ZF(0xFF, diff, regs);

		TRACE((regs, regs->eip - eip, "testb $0x%x, *0x%x (0x%x)",
							val, addr, diff));
		break;

	/* other test opcodes ... */
	}

	return 1;
}

/*
 * We need to handle add opcodes that address memory beyond the 64KB
 * segment limit that VM8086 mode enforces.
 */
static int
add(struct regs *regs, unsigned prefix, unsigned opc)
{
	unsigned eip = regs->eip - 1;
	unsigned modrm = fetch8(regs);
	unsigned addr = operand(prefix, regs, modrm);
	unsigned r = (modrm >> 3) & 7;

	unsigned val1 = 0;
	unsigned val2 = 0;
	unsigned result = 0;
	unsigned hi_bit;

	if ((modrm & 0xC0) == 0xC0) /* no registers */
		return 0;

	switch (opc) {
	case 0x00: /* addr32 add r8, r/m8 */
		val1 = getreg8(regs, r);
		val2 = read8(addr);
		result = val1 + val2;
		write8(addr, result);
		TRACE((regs, regs->eip - eip,
			"addb %%e%s, *0x%x", rnames[r], addr));
		break;
		
	case 0x01: /* addr32 add r16, r/m16 */
		if (prefix & DATA32) {
			val1 = getreg32(regs, r);
			val2 = read32(addr);
			result = val1 + val2;
			write32(addr, result);
			TRACE((regs, regs->eip - eip,
				"addl %%e%s, *0x%x", rnames[r], addr));
		} else {
			val1 = getreg16(regs, r);
			val2 = read16(addr);
			result = val1 + val2;
			write16(addr, result);
			TRACE((regs, regs->eip - eip,
				"addw %%e%s, *0x%x", rnames[r], addr));
		}
		break;
		
	case 0x03: /* addr32 add r/m16, r16 */
		if (prefix & DATA32) {
			val1 = getreg32(regs, r);
			val2 = read32(addr);
			result = val1 + val2;
			setreg32(regs, r, result);
			TRACE((regs, regs->eip - eip,
				"addl *0x%x, %%e%s", addr, rnames[r]));
		} else {
			val1 = getreg16(regs, r);
			val2 = read16(addr);
			result = val1 + val2;
			setreg16(regs, r, result);
			TRACE((regs, regs->eip - eip,
				"addw *0x%x, %%%s", addr, rnames[r]));
		}
		break;
	}

	if (opc == 0x00)
		hi_bit = (1<<7);
	else
		hi_bit = (prefix & DATA32) ? (1<<31) : (1<<15);
	set_eflags_add(hi_bit, val1, val2, result, regs);

	return 1;
}

/*
 * We need to handle pop opcodes that address memory beyond the 64KB
 * segment limit that VM8086 mode enforces.
 */
static int
pop(struct regs *regs, unsigned prefix, unsigned opc)
{
	unsigned eip = regs->eip - 1;
	unsigned modrm = fetch8(regs);
	unsigned addr = operand(prefix, regs, modrm);

	if ((modrm & 0xC0) == 0xC0) /* no registers */
		return 0;

	switch (opc) {
	case 0x8F: /* pop r/m16 */
		if ((modrm >> 3) & 7)
			return 0;
		if (prefix & DATA32)
			write32(addr, pop32(regs));
		else
			write16(addr, pop16(regs));
		TRACE((regs, regs->eip - eip, "pop *0x%x", addr));
		break;

	/* other pop opcodes ... */
	}

	return 1;
}

static int
mov_to_seg(struct regs *regs, unsigned prefix, unsigned opc)
{
	unsigned modrm = fetch8(regs);

	/*
	 * Emulate segment loads in:
	 * 1) real->protected mode.
	 * 2) protected->real mode.
	 */
	if (mode != VM86_REAL_TO_PROTECTED &&
	    mode != VM86_PROTECTED_TO_REAL)
		return 0;

	/* Register source only. */
	if ((modrm & 0xC0) != 0xC0)
		goto fail;

	switch ((modrm & 0x38) >> 3) {
	case 0: /* es */
		regs->ves = getreg16(regs, modrm);
		if (mode == VM86_PROTECTED_TO_REAL)
			return 1;
		saved_rm_regs.ves = 0;
		oldctx.es_sel = regs->ves;
		return 1;

	/* case 1: cs */

	case 2: /* ss */
		regs->uss = getreg16(regs, modrm);
		if (mode == VM86_PROTECTED_TO_REAL)
			return 1;
		saved_rm_regs.uss = 0;
		oldctx.ss_sel = regs->uss;
		return 1;
	case 3: /* ds */
		regs->vds = getreg16(regs, modrm);
		if (mode == VM86_PROTECTED_TO_REAL)
			return 1;
		saved_rm_regs.vds = 0;
		oldctx.ds_sel = regs->vds;
		return 1;
	case 4: /* fs */
		regs->vfs = getreg16(regs, modrm);
		if (mode == VM86_PROTECTED_TO_REAL)
			return 1;
		saved_rm_regs.vfs = 0;
		oldctx.fs_sel = regs->vfs;
		return 1;
	case 5: /* gs */
		regs->vgs = getreg16(regs, modrm);
		if (mode == VM86_PROTECTED_TO_REAL)
			return 1;
		saved_rm_regs.vgs = 0;
		oldctx.gs_sel = regs->vgs;
		return 1;
	}

 fail:
	printf("%s:%d: missed opcode %02x %02x\n",
		   __FUNCTION__, __LINE__, opc, modrm);
	return 0;
}

/*
 * Emulate a segment load in protected mode
 */
static int
load_seg(unsigned long sel, uint32_t *base, uint32_t *limit, union vmcs_arbytes *arbytes)
{
	uint64_t gdt_phys_base;
	unsigned long long entry;

	/* protected mode: use seg as index into gdt */
	if (sel > oldctx.gdtr_limit)
		return 0;

	if (sel == 0) {
		arbytes->fields.null_bit = 1;
		return 1;
	}

	gdt_phys_base = guest_linear_to_phys(oldctx.gdtr_base);
	if (gdt_phys_base != (uint32_t)gdt_phys_base) {
		printf("gdt base address above 4G\n");
		cpuid_addr_value(gdt_phys_base + 8 * (sel >> 3), &entry);
	} else
		entry = ((unsigned long long *)(long)gdt_phys_base)[sel >> 3];

	/* Check the P bit first */
	if (!((entry >> (15+32)) & 0x1) && sel != 0)
		return 0;

	*base =  (((entry >> (56-24)) & 0xFF000000) |
		  ((entry >> (32-16)) & 0x00FF0000) |
		  ((entry >> (   16)) & 0x0000FFFF));
	*limit = (((entry >> (48-16)) & 0x000F0000) |
		  (entry & 0x0000FFFF));

	arbytes->bytes = 0;
	arbytes->fields.seg_type = (entry >> (8+32)) & 0xF; /* TYPE */
	arbytes->fields.s = (entry >> (12+32)) & 0x1; /* S */
	if (arbytes->fields.s)
		arbytes->fields.seg_type |= 1; /* accessed */
	arbytes->fields.dpl = (entry >> (13+32)) & 0x3; /* DPL */
	arbytes->fields.p = (entry >> (15+32)) & 0x1; /* P */
	arbytes->fields.avl = (entry >> (20+32)) & 0x1; /* AVL */
	arbytes->fields.default_ops_size = (entry >> (22+32)) & 0x1; /* D */

	if (entry & (1ULL << (23+32))) { /* G */
		arbytes->fields.g = 1;
		*limit = (*limit << 12) | 0xFFF;
	}

	return 1;
}

/*
 * Emulate a protected mode segment load, falling back to clearing it if
 * the descriptor was invalid.
 */
static void
load_or_clear_seg(unsigned long sel, uint32_t *base, uint32_t *limit, union vmcs_arbytes *arbytes)
{
	if (!load_seg(sel, base, limit, arbytes))
		load_seg(0, base, limit, arbytes);
}

static unsigned char rm_irqbase[2];

/*
 * Transition to protected mode
 */
static void
protected_mode(struct regs *regs)
{
	extern char stack_top[];

	oldctx.rm_irqbase[0] = rm_irqbase[0];
	oldctx.rm_irqbase[1] = rm_irqbase[1];

	regs->eflags &= ~(EFLAGS_TF|EFLAGS_VM);

	oldctx.eip = regs->eip;
	oldctx.esp = regs->uesp;
	oldctx.eflags = regs->eflags;

	/* reload all segment registers */
	if (!load_seg(regs->cs, &oldctx.cs_base,
				&oldctx.cs_limit, &oldctx.cs_arbytes))
		panic("Invalid %%cs=0x%x for protected mode\n", regs->cs);
	oldctx.cs_sel = regs->cs;

	load_or_clear_seg(oldctx.es_sel, &oldctx.es_base,
			  &oldctx.es_limit, &oldctx.es_arbytes);
	load_or_clear_seg(oldctx.ss_sel, &oldctx.ss_base,
			  &oldctx.ss_limit, &oldctx.ss_arbytes);
	load_or_clear_seg(oldctx.ds_sel, &oldctx.ds_base,
			  &oldctx.ds_limit, &oldctx.ds_arbytes);
	load_or_clear_seg(oldctx.fs_sel, &oldctx.fs_base,
			  &oldctx.fs_limit, &oldctx.fs_arbytes);
	load_or_clear_seg(oldctx.gs_sel, &oldctx.gs_base,
			  &oldctx.gs_limit, &oldctx.gs_arbytes);

	/* initialize jump environment to warp back to protected mode */
	regs->uss = DATA_SELECTOR;
	regs->uesp = (unsigned long)stack_top;
	regs->cs = CODE_SELECTOR;
	regs->eip = (unsigned long)switch_to_protected_mode;

	/* this should get us into 32-bit mode */
}

/*
 * Start real-mode emulation
 */
static void
real_mode(struct regs *regs)
{
	regs->eflags |= EFLAGS_VM | 0x02;

	/*
	 * When we transition from protected to real-mode and we
	 * have not reloaded the segment descriptors yet, they are
	 * interpreted as if they were in protect mode.
	 * We emulate this behavior by assuming that these memory
	 * reference are below 1MB and set %ss, %ds, %es accordingly.
	 */
	if (regs->uss != 0) {
		if (regs->uss >= HIGHMEM)
			panic("%%ss 0x%lx higher than 1MB", regs->uss);
		regs->uss = address(regs, regs->uss, 0) >> 4;
	} else {
		regs->uss = saved_rm_regs.uss;
	}
	if (regs->vds != 0) {
		if (regs->vds >= HIGHMEM)
			panic("%%ds 0x%lx higher than 1MB", regs->vds);
		regs->vds = address(regs, regs->vds, 0) >> 4;
	} else {
		regs->vds = saved_rm_regs.vds;
	}
	if (regs->ves != 0) {
		if (regs->ves >= HIGHMEM)
			panic("%%es 0x%lx higher than 1MB", regs->ves);
		regs->ves = address(regs, regs->ves, 0) >> 4;
	} else {
		regs->ves = saved_rm_regs.ves;
	}

	/* this should get us into 16-bit mode */
}

/*
 * This is the smarts of the emulator and handles the mode transitions. The
 * emulator handles 4 different modes. 1) VM86_REAL: emulated real-mode,
 * Just handle those instructions that are not supported under VM8086.
 * 2) VM86_REAL_TO_PROTECTED: going from real-mode to protected mode. In
 * this we single step through the instructions until we reload the
 * new %cs (some OSes do a lot of computations before reloading %cs). 2)
 * VM86_PROTECTED_TO_REAL when we are going from protected to real mode. In
 * this case we emulate the instructions by hand. Finally, 4) VM86_PROTECTED
 * when we transitioned to protected mode and we should abandon the
 * emulator. No instructions are emulated when in VM86_PROTECTED mode.
 */
void
set_mode(struct regs *regs, enum vm86_mode newmode)
{
	switch (newmode) {
	case VM86_REAL:
		if (mode == VM86_PROTECTED_TO_REAL ||
		    mode == VM86_REAL_TO_PROTECTED) {
			regs->eflags &= ~EFLAGS_TF;
			real_mode(regs);
		} else if (mode != VM86_REAL)
			panic("unexpected real mode transition");
		break;

	case VM86_REAL_TO_PROTECTED:
		if (mode == VM86_REAL) {
			regs->eflags |= EFLAGS_TF;
			saved_rm_regs.vds = regs->vds;
			saved_rm_regs.ves = regs->ves;
			saved_rm_regs.vfs = regs->vfs;
			saved_rm_regs.vgs = regs->vgs;
			saved_rm_regs.uss = regs->uss;
			oldctx.ds_sel = 0;
			oldctx.es_sel = 0;
			oldctx.fs_sel = 0;
			oldctx.gs_sel = 0;
			oldctx.ss_sel = 0;
		} else if (mode != VM86_REAL_TO_PROTECTED)
			panic("unexpected real-to-protected mode transition");
		break;

	case VM86_PROTECTED_TO_REAL:
		if (mode != VM86_PROTECTED)
			panic("unexpected protected-to-real mode transition");
		break;

	case VM86_PROTECTED:
		if (mode != VM86_REAL_TO_PROTECTED)
			panic("unexpected protected mode transition");
		protected_mode(regs);
		break;
	}

	mode = newmode;
	if (mode != VM86_PROTECTED)
		TRACE((regs, 0, states[mode]));
}

static void
jmpl(struct regs *regs, int prefix)
{
	unsigned n = regs->eip;
	unsigned cs, eip;

	eip = (prefix & DATA32) ? fetch32(regs) : fetch16(regs);
	cs = fetch16(regs);

	TRACE((regs, (regs->eip - n) + 1, "jmpl 0x%x:0x%x", cs, eip));

	regs->cs = cs;
	regs->eip = eip;

	if (mode == VM86_REAL_TO_PROTECTED)		/* jump to protected mode */
		set_mode(regs, VM86_PROTECTED);
	else if (mode == VM86_PROTECTED_TO_REAL)	/* jump to real mode */
		set_mode(regs, VM86_REAL);
	else
		panic("jmpl");
}

static void
jmpl_indirect(struct regs *regs, int prefix, unsigned modrm)
{
	unsigned n = regs->eip;
	unsigned cs, eip;
	unsigned addr;

	addr = operand(prefix, regs, modrm);

	eip = (prefix & DATA32) ? read32(addr) : read16(addr);
	addr += (prefix & DATA32) ? 4 : 2;
	cs = read16(addr);

	TRACE((regs, (regs->eip - n) + 1, "jmpl 0x%x:0x%x", cs, eip));

	regs->cs = cs;
	regs->eip = eip;

	if (mode == VM86_REAL_TO_PROTECTED)		/* jump to protected mode */
		set_mode(regs, VM86_PROTECTED);
	else if (mode == VM86_PROTECTED_TO_REAL)	/* jump to real mode */
		set_mode(regs, VM86_REAL);
	else
		panic("jmpl");
}

static void
retl(struct regs *regs, int prefix)
{
	unsigned cs, eip;

	if (prefix & DATA32) {
		eip = pop32(regs);
		cs = MASK16(pop32(regs));
	} else {
		eip = pop16(regs);
		cs = pop16(regs);
	}

	TRACE((regs, 1, "retl (to 0x%x:0x%x)", cs, eip));

	regs->cs = cs;
	regs->eip = eip;

	if (mode == VM86_REAL_TO_PROTECTED)		/* jump to protected mode */
		set_mode(regs, VM86_PROTECTED);
	else if (mode == VM86_PROTECTED_TO_REAL)	/* jump to real mode */
		set_mode(regs, VM86_REAL);
	else
		panic("retl");
}

static void
interrupt(struct regs *regs, int n)
{
	TRACE((regs, 0, "external interrupt %d", n));
	push16(regs, regs->eflags);
	push16(regs, regs->cs);
	push16(regs, regs->eip);
	regs->eflags &= ~EFLAGS_IF;
	regs->eip = read16(address(regs, 0, n * 4));
	regs->cs = read16(address(regs, 0, n * 4 + 2));
}

/*
 * Most port I/O operations are passed unmodified. We do have to be
 * careful and make sure the emulated program isn't remapping the
 * interrupt vectors. The following simple state machine catches
 * these attempts and rewrites them.
 */
static int
outbyte(struct regs *regs, unsigned prefix, unsigned opc)
{
	static char icw2[2] = { 0 };
	int al, port;

	switch (opc) {
	case 0xE6: /* outb port, al */
		port = fetch8(regs);
		break;
	case 0xEE: /* outb (%dx), al */
		port = MASK16(regs->edx);
		break;
	default:
		return 0;
	}

	al = regs->eax & 0xFF;

	switch (port) {
	case PIC_MASTER + PIC_CMD:
		if (al & (1 << 4)) /* A0=0,D4=1 -> ICW1 */
			icw2[0] = 1;
		break;
	case PIC_MASTER + PIC_IMR:
		if (icw2[0]) {
			icw2[0] = 0;
			printf("Remapping master: ICW2 0x%x -> 0x%x\n",
				al, NR_EXCEPTION_HANDLER);
			rm_irqbase[0] = al;
			al = NR_EXCEPTION_HANDLER;
		}
		break;

	case PIC_SLAVE  + PIC_CMD:
		if (al & (1 << 4)) /* A0=0,D4=1 -> ICW1 */
			icw2[1] = 1;
		break;
	case PIC_SLAVE  + PIC_IMR:
		if (icw2[1]) {
			icw2[1] = 0;
			printf("Remapping slave: ICW2 0x%x -> 0x%x\n",
				al, NR_EXCEPTION_HANDLER+8);
			rm_irqbase[1] = al;
			al = NR_EXCEPTION_HANDLER+8;
		}
		break;
	}

	outb(port, al);
	return 1;
}

static int
inbyte(struct regs *regs, unsigned prefix, unsigned opc)
{
	int port;

	switch (opc) {
	case 0xE4: /* inb al, port */
		port = fetch8(regs);
		break;
	case 0xEC: /* inb al, (%dx) */
		port = MASK16(regs->edx);
		break;
	default:
		return 0;
	}

	regs->eax = (regs->eax & ~0xFF) | inb(port);
	return 1;
}

static void
pushrm(struct regs *regs, int prefix, unsigned modrm)
{
	unsigned n = regs->eip;
	unsigned addr;
	unsigned data;

	addr = operand(prefix, regs, modrm);

	if (prefix & DATA32) {
		data = read32(addr);
		push32(regs, data);
	} else {
		data = read16(addr);
		push16(regs, data);
	}

	TRACE((regs, (regs->eip - n) + 1, "push *0x%x", addr));
}

enum { OPC_INVALID, OPC_EMULATED };

#define rdmsr(msr,val1,val2)				\
	__asm__ __volatile__(				\
		"rdmsr"					\
		: "=a" (val1), "=d" (val2)		\
		: "c" (msr))

#define wrmsr(msr,val1,val2)				\
	__asm__ __volatile__(				\
		"wrmsr"					\
		: /* no outputs */			\
		: "c" (msr), "a" (val1), "d" (val2))

/*
 * Emulate a single instruction, including all its prefixes. We only implement
 * a small subset of the opcodes, and not all opcodes are implemented for each
 * of the four modes we can operate in.
 */
static int
opcode(struct regs *regs)
{
	unsigned eip = regs->eip;
	unsigned opc, modrm, disp;
	unsigned prefix = 0;

	if (mode == VM86_PROTECTED_TO_REAL &&
		oldctx.cs_arbytes.fields.default_ops_size) {
		prefix |= DATA32;
		prefix |= ADDR32;
	}

	for (;;) {
		switch ((opc = fetch8(regs))) {

		case 0x00: /* addr32 add r8, r/m8 */
		case 0x01: /* addr32 add r16, r/m16 */
		case 0x03: /* addr32 add r/m16, r16 */
			if (mode != VM86_REAL && mode != VM86_REAL_TO_PROTECTED)
				goto invalid;
			if ((prefix & ADDR32) == 0)
				goto invalid;
			if (!add(regs, prefix, opc))
				goto invalid;
			return OPC_EMULATED;
			
		case 0x07: /* pop %es */
			regs->ves = (prefix & DATA32) ?
				pop32(regs) : pop16(regs);
			TRACE((regs, regs->eip - eip, "pop %%es"));
			if (mode == VM86_REAL_TO_PROTECTED) {
				saved_rm_regs.ves = 0;
				oldctx.es_sel = regs->ves;
			}
			return OPC_EMULATED;

		case 0x0F: /* two byte opcode */
			if (mode == VM86_PROTECTED)
				goto invalid;
			switch ((opc = fetch8(regs))) {
			case 0x01:
				switch (((modrm = fetch8(regs)) >> 3) & 7) {
				case 0: /* sgdt */
				case 1: /* sidt */
					goto invalid;
				case 2: /* lgdt */
					if (!lgdt(regs, prefix, modrm))
						goto invalid;
					return OPC_EMULATED;
				case 3: /* lidt */
					if (!lidt(regs, prefix, modrm))
						goto invalid;
					return OPC_EMULATED;
				case 4: /* smsw */
					goto invalid;
				case 5:
					goto invalid;
				case 6: /* lmsw */
					if (!lmsw(regs, prefix, modrm))
						goto invalid;
					return OPC_EMULATED;
				case 7: /* invlpg */
					goto invalid;
				}
				break;
			case 0x06: /* clts */
				oldctx.cr0 &= ~CR0_TS;
				return OPC_EMULATED;
			case 0x09: /* wbinvd */
				return OPC_EMULATED;
			case 0x20: /* mov Rd, Cd (1h) */
			case 0x22:
				if (!movcr(regs, prefix, opc))
					goto invalid;
				return OPC_EMULATED;
			case 0x30: /* WRMSR */
				wrmsr(regs->ecx, regs->eax, regs->edx);
				return OPC_EMULATED;
			case 0x32: /* RDMSR */
				rdmsr(regs->ecx, regs->eax, regs->edx);
				return OPC_EMULATED;
			default:
				goto invalid;
			}
			goto invalid;

		case 0x1F: /* pop %ds */
			regs->vds = (prefix & DATA32) ?
				pop32(regs) : pop16(regs);
			TRACE((regs, regs->eip - eip, "pop %%ds"));
			if (mode == VM86_REAL_TO_PROTECTED) {
				saved_rm_regs.vds = 0;
				oldctx.ds_sel = regs->vds;
			}
			return OPC_EMULATED;

		case 0x26:
			TRACE((regs, regs->eip - eip, "%%es:"));
			prefix |= SEG_ES;
			continue;

		case 0x2E:
			TRACE((regs, regs->eip - eip, "%%cs:"));
			prefix |= SEG_CS;
			continue;

		case 0x36:
			TRACE((regs, regs->eip - eip, "%%ss:"));
			prefix |= SEG_SS;
			continue;

		case 0x39: /* addr32 cmp r16, r/m16 */
		case 0x3B: /* addr32 cmp r/m16, r16 */
			if (mode == VM86_PROTECTED_TO_REAL || !(prefix & ADDR32))
				goto invalid;
			if (!cmp(regs, prefix, opc))
				goto invalid;
			return OPC_EMULATED;

		case 0x3E:
			TRACE((regs, regs->eip - eip, "%%ds:"));
			prefix |= SEG_DS;
			continue;

		case 0x64:
			TRACE((regs, regs->eip - eip, "%%fs:"));
			prefix |= SEG_FS;
			continue;

		case 0x65:
			TRACE((regs, regs->eip - eip, "%%gs:"));
			prefix |= SEG_GS;
			continue;

		case 0x66:
			if (mode == VM86_PROTECTED_TO_REAL &&
				oldctx.cs_arbytes.fields.default_ops_size) {
				TRACE((regs, regs->eip - eip, "data16"));
				prefix &= ~DATA32;
			} else {
				TRACE((regs, regs->eip - eip, "data32"));
				prefix |= DATA32;
			}
			continue;

		case 0x67:
			if (mode == VM86_PROTECTED_TO_REAL &&
				oldctx.cs_arbytes.fields.default_ops_size) {
				TRACE((regs, regs->eip - eip, "addr16"));
				prefix &= ~ADDR32;
			} else {
				TRACE((regs, regs->eip - eip, "addr32"));
				prefix |= ADDR32;
			}
			continue;

		case 0x88: /* addr32 mov r8, r/m8 */
		case 0x8A: /* addr32 mov r/m8, r8 */
			if (mode == VM86_PROTECTED_TO_REAL || !(prefix & ADDR32))
				goto invalid;
			if (!movr(regs, prefix, opc))
				goto invalid;
			return OPC_EMULATED;

		case 0x89: /* mov r16, r/m16 */
		case 0x8B: /* mov r/m16, r16 */
			if (mode != VM86_PROTECTED_TO_REAL && !(prefix & ADDR32))
				goto invalid;
			if (!movr(regs, prefix, opc))
				goto invalid;
			return OPC_EMULATED;

		case 0x8E: /* mov r16, sreg */
			if (!mov_to_seg(regs, prefix, opc))
				goto invalid;
			return OPC_EMULATED;

		case 0x8F: /* addr32 pop r/m16 */
			if (!(prefix & ADDR32))
				goto invalid;
			if (!pop(regs, prefix, opc))
				goto invalid;
			return OPC_EMULATED;

		case 0x90: /* nop */
			TRACE((regs, regs->eip - eip, "nop"));
			return OPC_EMULATED;

		case 0x9C: /* pushf */
			TRACE((regs, regs->eip - eip, "pushf"));
			if (prefix & DATA32)
				push32(regs, regs->eflags & ~EFLAGS_VM);
			else
				push16(regs, regs->eflags & ~EFLAGS_VM);
			return OPC_EMULATED;

		case 0x9D: /* popf */
			TRACE((regs, regs->eip - eip, "popf"));
			if (prefix & DATA32)
				regs->eflags = pop32(regs);
			else
				regs->eflags = (regs->eflags & 0xFFFF0000L) |
								pop16(regs);
			regs->eflags |= EFLAGS_VM;
			return OPC_EMULATED;

		case 0xA1: /* mov ax, r/m16 */
		{
			int addr, data;
			int seg = segment(prefix, regs, regs->vds);
			int offset = prefix & ADDR32 ? fetch32(regs) : fetch16(regs);

			if (prefix & DATA32) {
				addr = address(regs, seg, offset);
				data = read32(addr);
				setreg32(regs, 0, data);
			} else {
				addr = address(regs, seg, offset);
				data = read16(addr);
				setreg16(regs, 0, data);
			}
			TRACE((regs, regs->eip - eip, "mov *0x%x, %%ax", addr));
			return OPC_EMULATED;
		}

		case 0xA4: /* movsb */
		case 0xA5: /* movsw */
			if ((prefix & ADDR32) == 0)
				goto invalid;
			if (!movs(regs, prefix, opc))
				goto invalid;
			return OPC_EMULATED;

		case 0xAD: /* lodsw */
			if ((prefix & ADDR32) == 0)
				goto invalid;
			if (!lods(regs, prefix, opc))
				goto invalid;
			return OPC_EMULATED;
			
		case 0xBB: /* mov bx, imm16 */
		{
			int data;
			if (prefix & DATA32) {
				data = fetch32(regs);
				setreg32(regs, 3, data);
			} else {
				data = fetch16(regs);
				setreg16(regs, 3, data);
			}
			TRACE((regs, regs->eip - eip, "mov $0x%x, %%bx", data));
			return OPC_EMULATED;
		}

		case 0xC6: /* addr32 movb $imm, r/m8 */
			if (!(prefix & ADDR32))
				goto invalid;
			if (!movr(regs, prefix, opc))
				goto invalid;
			return OPC_EMULATED;

		case 0xCB: /* retl */
			if (mode == VM86_REAL_TO_PROTECTED ||
				mode == VM86_PROTECTED_TO_REAL) {
				retl(regs, prefix);
				return OPC_INVALID;
			}
			goto invalid;

		case 0xCD: /* int $n */
			TRACE((regs, regs->eip - eip, "int"));
			interrupt(regs, fetch8(regs));
			return OPC_EMULATED;

		case 0xCF: /* iret */
			if (prefix & DATA32) {
				TRACE((regs, regs->eip - eip, "data32 iretd"));
				regs->eip = pop32(regs);
				regs->cs = pop32(regs);
				regs->eflags = pop32(regs);
			} else {
				TRACE((regs, regs->eip - eip, "iret"));
				regs->eip = pop16(regs);
				regs->cs = pop16(regs);
				regs->eflags = (regs->eflags & 0xFFFF0000L) |
								pop16(regs);
			}
			return OPC_EMULATED;

		case 0xE4: /* inb al, port */
			if (!inbyte(regs, prefix, opc))
				goto invalid;
			return OPC_EMULATED;

		case 0xE6: /* outb port, al */
			if (!outbyte(regs, prefix, opc))
				goto invalid;
			return OPC_EMULATED;

		case 0xEA: /* jmpl */
			if (mode == VM86_REAL_TO_PROTECTED ||
				mode == VM86_PROTECTED_TO_REAL) {
				jmpl(regs, prefix);
				return OPC_INVALID;
			}
			goto invalid;

		case 0xFF:
		{
			unsigned modrm = fetch8(regs);
			switch((modrm >> 3) & 7) {
			case 5: /* jmpl (indirect) */
				if (mode == VM86_REAL_TO_PROTECTED ||
					mode == VM86_PROTECTED_TO_REAL) {
					jmpl_indirect(regs, prefix, modrm);
					return OPC_INVALID;
				}
				goto invalid;

			case 6: /* push r/m16 */
				pushrm(regs, prefix, modrm);
				return OPC_EMULATED;

			default:
				goto invalid;
			}
		}

		case 0xEB: /* short jump */
			if (mode == VM86_REAL_TO_PROTECTED ||
				mode == VM86_PROTECTED_TO_REAL) {
				disp = (char) fetch8(regs);
				TRACE((regs, 2, "jmp 0x%x", regs->eip + disp));
				regs->eip += disp;
				return OPC_EMULATED;
			}
			goto invalid;

		case 0xEC: /* inb al, (%dx) */
			if (!inbyte(regs, prefix, opc))
				goto invalid;
			return OPC_EMULATED;

		case 0xEE: /* outb (%dx), al */
			if (!outbyte(regs, prefix, opc))
				goto invalid;
			return OPC_EMULATED;

		case 0xF0: /* lock */
			TRACE((regs, regs->eip - eip, "lock"));
			continue;

		case 0xF4: /* hlt */
			TRACE((regs, regs->eip - eip, "hlt"));
			/* Do something power-saving here! */
			return OPC_EMULATED;

		case 0xF3: /* rep/repe/repz */
			TRACE((regs, regs->eip - eip, "rep"));
			prefix |= REP;
			continue;

		case 0xF6: /* addr32 testb $imm, r/m8 */
			if (!(prefix & ADDR32))
				goto invalid;
			if (!test(regs, prefix, opc))
				goto invalid;
			return OPC_EMULATED;

		case 0xFA: /* cli */
			TRACE((regs, regs->eip - eip, "cli"));
			regs->eflags &= ~EFLAGS_IF;
			return OPC_EMULATED;

		case 0xFB: /* sti */
			TRACE((regs, regs->eip - eip, "sti"));
			regs->eflags |= EFLAGS_IF;
			return OPC_EMULATED;

		default:
			goto invalid;
		}
	}

invalid:
	regs->eip = eip;
	TRACE((regs, regs->eip - eip, "opc 0x%x", opc));
	return OPC_INVALID;
}

void
emulate(struct regs *regs)
{
	unsigned flteip;
	int nemul = 0;
	unsigned ip;

	/* emulate as many instructions as possible */
	while (opcode(regs) != OPC_INVALID)
		nemul++;

	/* detect the case where we are not making progress */
	if (nemul == 0 && prev_eip == regs->eip) {
		flteip = address(regs, MASK16(regs->cs), regs->eip);

		printf("Undecoded sequence: \n");
		for (ip=flteip; ip < flteip+16; ip++)
			printf("0x%02x ", read8(ip));
		printf("\n");

		panic("Unknown opcode at %04x:%04x=0x%x",
			MASK16(regs->cs), regs->eip, flteip);
	} else
		prev_eip = regs->eip;
}

void
trap(int trapno, int errno, struct regs *regs)
{
	/* emulate device interrupts */
	if (trapno >= NR_EXCEPTION_HANDLER) {
		int irq = trapno - NR_EXCEPTION_HANDLER;
		if (irq < 8) 
			interrupt(regs, irq + 8);
		else
			interrupt(regs, 0x70 + (irq - 8));
		return;
	}

	switch (trapno) {
	case 1: /* Debug */
		if (regs->eflags & EFLAGS_VM) {
			/* emulate any 8086 instructions  */
			if (mode == VM86_REAL)
				return;
			if (mode != VM86_REAL_TO_PROTECTED)
				panic("not in real-to-protected mode");
			emulate(regs);
			return;
		}
		goto invalid;

	case 13: /* GPF */
		if (regs->eflags & EFLAGS_VM) {
			/* emulate any 8086 instructions  */
			if (mode == VM86_PROTECTED)
				panic("unexpected protected mode");
			emulate(regs);
			return;
		}
		goto invalid;

	default:
	invalid:
		printf("Trap (0x%x) while in %s mode\n",
			trapno, regs->eflags & EFLAGS_VM ? "real" : "protected");
		if (trapno == 14)
			printf("Page fault address 0x%x\n", get_cr2());
		dump_regs(regs);
		halt();
	}
}
