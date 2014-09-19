/*
 * Copyright (c) 2004, Intel Corporation.
 * Copyright (c) 2006, Keir Fraser, XenSource Inc.
 *
 * This program is free software; you can redistribute it and/or modify it
 * under the terms and conditions of the GNU General Public License, version 
 * 2, as published by the Free Software Foundation.
 *
 * This program is distributed in the hope it will be useful, but WITHOUT ANY 
 * WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS 
 * FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more 
 * details.
 *
 * You should have received a copy of the GNU General Public License along with
 * this program; if not, write to the Free Software Foundation, Inc., 59 Temple
 * Place - Suite 330, Boston, MA 02111-1307 USA.
 */

#include "acpi2_0.h"
#include "ssdt_tpm.h"
#include "../config.h"
#include "../util.h"

#define align16(sz)        (((sz) + 15) & ~15)
#define fixed_strcpy(d, s) strncpy((d), (s), sizeof(d))

extern struct acpi_20_rsdp Rsdp;
extern struct acpi_20_rsdt Rsdt;
extern struct acpi_20_xsdt Xsdt;
extern struct acpi_20_fadt Fadt;
extern struct acpi_20_facs Facs;
extern unsigned char AmlCode[];
extern int DsdtLen;

static void set_checksum(
    void *table, uint32_t checksum_offset, uint32_t length)
{
    uint8_t *p, sum = 0;

    p = table;
    p[checksum_offset] = 0;

    while ( length-- )
        sum = sum + *p++;

    p = table;
    p[checksum_offset] = -sum;
}

static int uart_exists(uint16_t uart_base)
{
    uint16_t ier = uart_base + 1;
    uint8_t a, b, c;

    a = inb(ier);
    outb(ier, 0);
    b = inb(ier);
    outb(ier, 0xf);
    c = inb(ier);
    outb(ier, a);

    return ((b == 0) && (c == 0xf));
}

static int construct_bios_info_table(uint8_t *buf)
{
    struct bios_info {
        uint8_t com1_present:1;
        uint8_t com2_present:1;
    } *bios_info = (struct bios_info *)buf;

    memset(bios_info, 0, sizeof(*bios_info));

    bios_info->com1_present = uart_exists(0x3f8);
    bios_info->com2_present = uart_exists(0x2f8);

    return align16(sizeof(*bios_info));
}

static int construct_madt(struct acpi_20_madt *madt)
{
    struct acpi_20_madt_intsrcovr *intsrcovr;
    struct acpi_20_madt_ioapic    *io_apic;
    struct acpi_20_madt_lapic     *lapic;
    int i, offset = 0;

    memset(madt, 0, sizeof(*madt));
    madt->header.signature    = ACPI_2_0_MADT_SIGNATURE;
    madt->header.revision     = ACPI_2_0_MADT_REVISION;
    fixed_strcpy(madt->header.oem_id, ACPI_OEM_ID);
    fixed_strcpy(madt->header.oem_table_id, ACPI_OEM_TABLE_ID);
    madt->header.oem_revision = ACPI_OEM_REVISION;
    madt->header.creator_id   = ACPI_CREATOR_ID;
    madt->header.creator_revision = ACPI_CREATOR_REVISION;
    madt->lapic_addr = LAPIC_BASE_ADDRESS;
    madt->flags      = ACPI_PCAT_COMPAT;
    offset += sizeof(*madt);

    intsrcovr = (struct acpi_20_madt_intsrcovr *)(madt + 1);
    for ( i = 0; i < 16; i++ )
    {
        memset(intsrcovr, 0, sizeof(*intsrcovr));
        intsrcovr->type   = ACPI_INTERRUPT_SOURCE_OVERRIDE;
        intsrcovr->length = sizeof(*intsrcovr);
        intsrcovr->source = i;

        if ( i == 0 )
        {
            /* ISA IRQ0 routed to IOAPIC GSI 2. */
            intsrcovr->gsi    = 2;
            intsrcovr->flags  = 0x0;
        }
        else if ( PCI_ISA_IRQ_MASK & (1U << i) )
        {
            /* PCI: active-low level-triggered. */
            intsrcovr->gsi    = i;
            intsrcovr->flags  = 0xf;
        }
        else
        {
            /* No need for a INT source override structure. */
            continue;
        }

        offset += sizeof(*intsrcovr);
        intsrcovr++;
    }

    io_apic = (struct acpi_20_madt_ioapic *)intsrcovr;
    memset(io_apic, 0, sizeof(*io_apic));
    io_apic->type        = ACPI_IO_APIC;
    io_apic->length      = sizeof(*io_apic);
    io_apic->ioapic_id   = IOAPIC_ID;
    io_apic->ioapic_addr = IOAPIC_BASE_ADDRESS;
    offset += sizeof(*io_apic);

    lapic = (struct acpi_20_madt_lapic *)(io_apic + 1);
    for ( i = 0; i < get_vcpu_nr(); i++ )
    {
        memset(lapic, 0, sizeof(*lapic));
        lapic->type    = ACPI_PROCESSOR_LOCAL_APIC;
        lapic->length  = sizeof(*lapic);
        /* Processor ID must match processor-object IDs in the DSDT. */
        lapic->acpi_processor_id = i;
        lapic->apic_id = LAPIC_ID(i);
        lapic->flags   = ACPI_LOCAL_APIC_ENABLED;
        offset += sizeof(*lapic);
        lapic++;
    }

    madt->header.length = offset;
    set_checksum(madt, offsetof(struct acpi_header, checksum), offset);

    return align16(offset);
}

static int construct_hpet(struct acpi_20_hpet *hpet)
{
    int offset;

    memset(hpet, 0, sizeof(*hpet));
    hpet->header.signature    = ACPI_2_0_HPET_SIGNATURE;
    hpet->header.revision     = ACPI_2_0_HPET_REVISION;
    fixed_strcpy(hpet->header.oem_id, ACPI_OEM_ID);
    fixed_strcpy(hpet->header.oem_table_id, ACPI_OEM_TABLE_ID);
    hpet->header.oem_revision = ACPI_OEM_REVISION;
    hpet->header.creator_id   = ACPI_CREATOR_ID;
    hpet->header.creator_revision = ACPI_CREATOR_REVISION;
    hpet->timer_block_id      = 0x8086a201;
    hpet->addr.address        = ACPI_HPET_ADDRESS;
    offset = sizeof(*hpet);

    hpet->header.length = offset;
    set_checksum(hpet, offsetof(struct acpi_header, checksum), offset);

    return offset;
}

static int construct_processor_objects(uint8_t *buf)
{
    static const char pdat[13] = { 0x5b, 0x83, 0x0b, 0x50, 0x52 };
    static const char hex[] = "0123456789ABCDEF";
    static const char pr_scope[] = "\\_PR_";
    unsigned int i, length, nr_cpus = get_vcpu_nr();
    struct acpi_header *hdr;
    uint8_t *p = buf;

    /*
     * 1. Table Header.
     */

    hdr = (struct acpi_header *)p;
    hdr->signature = ASCII32('S','S','D','T');
    hdr->revision  = 2;
    fixed_strcpy(hdr->oem_id, ACPI_OEM_ID);
    fixed_strcpy(hdr->oem_table_id, ACPI_OEM_TABLE_ID);
    hdr->oem_revision = ACPI_OEM_REVISION;
    hdr->creator_id = ACPI_CREATOR_ID;
    hdr->creator_revision = ACPI_CREATOR_REVISION;
    p += sizeof(*hdr);

    /*
     * 2. Scope Definition.
     */

    /* ScopeOp */
    *p++ = 0x10;

    /* PkgLength (includes length bytes!). */
    length = 1 + strlen(pr_scope) + (nr_cpus * sizeof(pdat));
    if ( length <= 0x3f )
    {
        *p++ = length;
    }
    else if ( ++length <= 0xfff )
    {
        *p++ = 0x40 | (length & 0xf);
        *p++ = length >> 4;
    }
    else
    {
        length++;
        *p++ = 0x80 | (length & 0xf);
        *p++ = (length >>  4) & 0xff;
        *p++ = (length >> 12) & 0xff;
    }

    /* NameString */
    strncpy((char *)p, pr_scope, strlen(pr_scope));
    p += strlen(pr_scope);

    /*
     * 3. Processor Objects.
     */

    for ( i = 0; i < nr_cpus; i++ )
    {
        memcpy(p, pdat, sizeof(pdat));
        /* ProcessorName */
        p[5] = hex[(i>>4)&15];
        p[6] = hex[(i>>0)&15];
        /* ProcessorID */
        p[7] = i;
        p += sizeof(pdat);
    }

    hdr->length = p - buf;
    set_checksum(hdr, offsetof(struct acpi_header, checksum), hdr->length);

    return hdr->length;
}

static int construct_secondary_tables(uint8_t *buf, unsigned long *table_ptrs)
{
    int offset = 0, nr_tables = 0;
    struct acpi_20_madt *madt;
    struct acpi_20_hpet *hpet;
    struct acpi_20_tcpa *tcpa;
    static const uint16_t tis_signature[] = {0x0001, 0x0001, 0x0001};
    uint16_t *tis_hdr;

    /* MADT. */
    if ( (get_vcpu_nr() > 1) || get_apic_mode() )
    {
        madt = (struct acpi_20_madt *)&buf[offset];
        offset += construct_madt(madt);
        table_ptrs[nr_tables++] = (unsigned long)madt;
    }

    /* HPET. */
    hpet = (struct acpi_20_hpet *)&buf[offset];
    offset += construct_hpet(hpet);
    table_ptrs[nr_tables++] = (unsigned long)hpet;

    /* Processor Object SSDT. */
    table_ptrs[nr_tables++] = (unsigned long)&buf[offset];
    offset += construct_processor_objects(&buf[offset]);

    /* TPM TCPA and SSDT. */
    tis_hdr = (uint16_t *)0xFED40F00;
    if ( (tis_hdr[0] == tis_signature[0]) &&
         (tis_hdr[1] == tis_signature[1]) &&
         (tis_hdr[2] == tis_signature[2]) )
    {
        memcpy(&buf[offset], AmlCode_TPM, sizeof(AmlCode_TPM));
        table_ptrs[nr_tables++] = (unsigned long)&buf[offset];
        offset += align16(sizeof(AmlCode_TPM));

        tcpa = (struct acpi_20_tcpa *)&buf[offset];
        memset(tcpa, 0, sizeof(*tcpa));
        offset += align16(sizeof(*tcpa));
        table_ptrs[nr_tables++] = (unsigned long)tcpa;

        tcpa->header.signature = ACPI_2_0_TCPA_SIGNATURE;
        tcpa->header.length    = sizeof(*tcpa);
        tcpa->header.revision  = ACPI_2_0_TCPA_REVISION;
        fixed_strcpy(tcpa->header.oem_id, ACPI_OEM_ID);
        fixed_strcpy(tcpa->header.oem_table_id, ACPI_OEM_TABLE_ID);
        tcpa->header.oem_revision = ACPI_OEM_REVISION;
        tcpa->header.creator_id   = ACPI_CREATOR_ID;
        tcpa->header.creator_revision = ACPI_CREATOR_REVISION;
        tcpa->lasa = e820_malloc(ACPI_2_0_TCPA_LAML_SIZE);
        if ( tcpa->lasa )
        {
            tcpa->laml = ACPI_2_0_TCPA_LAML_SIZE;
            memset((char *)(unsigned long)tcpa->lasa, 0, tcpa->laml);
            set_checksum(tcpa,
                         offsetof(struct acpi_header, checksum),
                         tcpa->header.length);
        }
    }

    table_ptrs[nr_tables] = 0;
    return align16(offset);
}

/* Copy all the ACPI table to buffer. */
int acpi_build_tables(uint8_t *buf)
{
    struct acpi_20_rsdp *rsdp;
    struct acpi_20_rsdt *rsdt;
    struct acpi_20_xsdt *xsdt;
    struct acpi_20_fadt *fadt;
    struct acpi_10_fadt *fadt_10;
    struct acpi_20_facs *facs;
    unsigned char       *dsdt;
    unsigned long        secondary_tables[16];
    int                  offset = 0, i;

    offset += construct_bios_info_table(&buf[offset]);

    facs = (struct acpi_20_facs *)&buf[offset];
    memcpy(facs, &Facs, sizeof(struct acpi_20_facs));
    offset += align16(sizeof(struct acpi_20_facs));

    dsdt = (unsigned char *)&buf[offset];
    memcpy(dsdt, &AmlCode, DsdtLen);
    offset += align16(DsdtLen);

    /*
     * N.B. ACPI 1.0 operating systems may not handle FADT with revision 2
     * or above properly, notably Windows 2000, which tries to copy FADT
     * into a 116 bytes buffer thus causing an overflow. The solution is to
     * link the higher revision FADT with the XSDT only and introduce a
     * compatible revision 1 FADT that is linked with the RSDT. Refer to:
     *     http://www.acpi.info/presentations/S01USMOBS169_OS%20new.ppt
     */
    fadt_10 = (struct acpi_10_fadt *)&buf[offset];
    memcpy(fadt_10, &Fadt, sizeof(struct acpi_10_fadt));
    offset += align16(sizeof(struct acpi_10_fadt));
    fadt_10->header.length = sizeof(struct acpi_10_fadt);
    fadt_10->header.revision = ACPI_1_0_FADT_REVISION;
    fadt_10->dsdt          = (unsigned long)dsdt;
    fadt_10->firmware_ctrl = (unsigned long)facs;
    set_checksum(fadt_10,
                 offsetof(struct acpi_header, checksum),
                 sizeof(struct acpi_10_fadt));

    fadt = (struct acpi_20_fadt *)&buf[offset];
    memcpy(fadt, &Fadt, sizeof(struct acpi_20_fadt));
    offset += align16(sizeof(struct acpi_20_fadt));
    fadt->dsdt   = (unsigned long)dsdt;
    fadt->x_dsdt = (unsigned long)dsdt;
    fadt->firmware_ctrl   = (unsigned long)facs;
    fadt->x_firmware_ctrl = (unsigned long)facs;
    set_checksum(fadt,
                 offsetof(struct acpi_header, checksum),
                 sizeof(struct acpi_20_fadt));

    offset += construct_secondary_tables(&buf[offset], secondary_tables);

    xsdt = (struct acpi_20_xsdt *)&buf[offset];
    memcpy(xsdt, &Xsdt, sizeof(struct acpi_header));
    xsdt->entry[0] = (unsigned long)fadt;
    for ( i = 0; secondary_tables[i]; i++ )
        xsdt->entry[i+1] = secondary_tables[i];
    xsdt->header.length = sizeof(struct acpi_header) + (i+1)*sizeof(uint64_t);
    offset += align16(xsdt->header.length);
    set_checksum(xsdt,
                 offsetof(struct acpi_header, checksum),
                 xsdt->header.length);

    rsdt = (struct acpi_20_rsdt *)&buf[offset];
    memcpy(rsdt, &Rsdt, sizeof(struct acpi_header));
    rsdt->entry[0] = (unsigned long)fadt_10;
    for ( i = 0; secondary_tables[i]; i++ )
        rsdt->entry[i+1] = secondary_tables[i];
    rsdt->header.length = sizeof(struct acpi_header) + (i+1)*sizeof(uint32_t);
    offset += align16(rsdt->header.length);
    set_checksum(rsdt,
                 offsetof(struct acpi_header, checksum),
                 rsdt->header.length);

    rsdp = (struct acpi_20_rsdp *)&buf[offset];
    memcpy(rsdp, &Rsdp, sizeof(struct acpi_20_rsdp));
    offset += align16(sizeof(struct acpi_20_rsdp));
    rsdp->rsdt_address = (unsigned long)rsdt;
    rsdp->xsdt_address = (unsigned long)xsdt;
    set_checksum(rsdp,
                 offsetof(struct acpi_10_rsdp, checksum),
                 sizeof(struct acpi_10_rsdp));
    set_checksum(rsdp,
                 offsetof(struct acpi_20_rsdp, extended_checksum),
                 sizeof(struct acpi_20_rsdp));

    return offset;
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
