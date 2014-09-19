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
 */

#ifndef _DMAR_H_
#define _DMAR_H_

#include <xen/list.h>
#include <asm/iommu.h>

extern u8 dmar_host_address_width;

struct acpi_drhd_unit {
    struct list_head list;
    unsigned long    address; /* register base address of the unit */
    struct    pci_dev *devices; /* target devices */
    int    devices_cnt;
    u8    include_all:1;
    struct iommu *iommu;
};

struct acpi_rmrr_unit {
    struct list_head list;
    unsigned long base_address;
    unsigned long end_address;
    struct pci_dev *devices; /* target devices */
    int    devices_cnt;
    u8    allow_all:1;
};

struct acpi_atsr_unit {
    struct list_head list;
    struct    pci_dev *devices; /* target devices */
    int    devices_cnt;
    u8    all_ports:1;
};

#define for_each_iommu(domain, iommu) \
    list_for_each_entry(iommu, \
        &(domain->arch.hvm_domain.hvm_iommu.iommu_list), list)

#define for_each_pdev(domain, pdev) \
    list_for_each_entry(pdev, \
         &(domain->arch.hvm_domain.hvm_iommu.pdev_list), list)

#define for_each_drhd_unit(drhd) \
    list_for_each_entry(drhd, &acpi_drhd_units, list)
#define for_each_rmrr_device(rmrr, pdev) \
    list_for_each_entry(rmrr, &acpi_rmrr_units, list) { \
        int _i; \
        for (_i = 0; _i < rmrr->devices_cnt; _i++) { \
            pdev = &(rmrr->devices[_i]);
#define end_for_each_rmrr_device(rmrr, pdev) \
        } \
    }

struct acpi_drhd_unit * acpi_find_matched_drhd_unit(struct pci_dev *dev);
struct acpi_rmrr_unit * acpi_find_matched_rmrr_unit(struct pci_dev *dev);

/* This one is for interrupt remapping */
struct acpi_ioapic_unit {
    struct list_head list;
    int apic_id;
    union {
        u16 info;
        struct {
            u16 bus: 8,
                dev: 5,
                func: 3;
        }bdf;
    }ioapic;
};

#define DMAR_OPERATION_TIMEOUT (HZ*60) /* 1m */
#define time_after(a,b)         \
        (typecheck(unsigned long, a) && \
         typecheck(unsigned long, b) && \
         ((long)(b) - (long)(a) < 0))

int vtd_hw_check(void);
int is_usb_device(struct pci_dev *pdev);

void disable_pmr(struct iommu *iommu);

#endif // _DMAR_H_
