/*
 * Copyright (c) 2004, Intel Corporation.
 * Copyright (c) 2006, Keir Fraser, XenSource Inc.
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

#include "acpi2_0.h"
#include "../config.h"
#include <xen/hvm/ioreq.h>

/*
 * Firmware ACPI Control Structure (FACS).
 */

struct acpi_20_facs Facs = {
    .signature = ACPI_2_0_FACS_SIGNATURE,
    .length    = sizeof(struct acpi_20_facs),
    .version   = ACPI_2_0_FACS_VERSION
};


/*
 * Fixed ACPI Description Table (FADT).
 */

#define ACPI_PM1A_EVT_BLK_BIT_WIDTH         0x20
#define ACPI_PM1A_EVT_BLK_BIT_OFFSET        0x00
#define ACPI_PM1A_CNT_BLK_BIT_WIDTH         0x10
#define ACPI_PM1A_CNT_BLK_BIT_OFFSET        0x00
#define ACPI_PM_TMR_BLK_BIT_WIDTH           0x20
#define ACPI_PM_TMR_BLK_BIT_OFFSET          0x00

struct acpi_20_fadt Fadt = {
    .header = {
        .signature    = ACPI_2_0_FADT_SIGNATURE,
        .length       = sizeof(struct acpi_20_fadt),
        .revision     = ACPI_2_0_FADT_REVISION,
        .oem_id       = ACPI_OEM_ID, 
        .oem_table_id = ACPI_OEM_TABLE_ID,
        .oem_revision = ACPI_OEM_REVISION,
        .creator_id   = ACPI_CREATOR_ID,
        .creator_revision = ACPI_CREATOR_REVISION
    },

    .sci_int = 9,

    .pm1a_evt_blk = ACPI_PM1A_EVT_BLK_ADDRESS,
    .pm1a_cnt_blk = ACPI_PM1A_CNT_BLK_ADDRESS,
    .pm_tmr_blk = ACPI_PM_TMR_BLK_ADDRESS,
    .pm1_evt_len = ACPI_PM1A_EVT_BLK_BIT_WIDTH / 8,
    .pm1_cnt_len = ACPI_PM1A_CNT_BLK_BIT_WIDTH / 8,
    .pm_tmr_len = ACPI_PM_TMR_BLK_BIT_WIDTH / 8,

    .p_lvl2_lat = 0x0fff, /* >100,  means we do not support C2 state */
    .p_lvl3_lat = 0x0fff, /* >1000, means we do not support C3 state */
    .iapc_boot_arch = ACPI_LEGACY_DEVICES | ACPI_8042,
    .flags = (ACPI_PROC_C1 | ACPI_SLP_BUTTON |
              ACPI_WBINVD | ACPI_PWR_BUTTON |
              ACPI_FIX_RTC | ACPI_TMR_VAL_EXT),

    .reset_reg = {
        .address_space_id    = ACPI_SYSTEM_IO,
        .register_bit_width  = 8, /* *must* be 8 */
        .register_bit_offset = 0, /* *must* be 0 */
        .address             = 0xcf9
    },
    .reset_value = 6,

    .x_pm1a_evt_blk = {
        .address_space_id    = ACPI_SYSTEM_IO,
        .register_bit_width  = ACPI_PM1A_EVT_BLK_BIT_WIDTH,
        .register_bit_offset = ACPI_PM1A_EVT_BLK_BIT_OFFSET,
        .address             = ACPI_PM1A_EVT_BLK_ADDRESS,
    },

    .x_pm1a_cnt_blk = {
        .address_space_id    = ACPI_SYSTEM_IO,
        .register_bit_width  = ACPI_PM1A_CNT_BLK_BIT_WIDTH,
        .register_bit_offset = ACPI_PM1A_CNT_BLK_BIT_OFFSET,
        .address             = ACPI_PM1A_CNT_BLK_ADDRESS,
    },

    .x_pm_tmr_blk = {
        .address_space_id    = ACPI_SYSTEM_IO,
        .register_bit_width  = ACPI_PM_TMR_BLK_BIT_WIDTH,
        .register_bit_offset = ACPI_PM_TMR_BLK_BIT_OFFSET,
        .address             = ACPI_PM_TMR_BLK_ADDRESS,
    }
};

struct acpi_20_rsdt Rsdt = {
    .header = {
        .signature    = ACPI_2_0_RSDT_SIGNATURE,
        .length       = sizeof(struct acpi_header),
        .revision     = ACPI_2_0_RSDT_REVISION,
        .oem_id       = ACPI_OEM_ID, 
        .oem_table_id = ACPI_OEM_TABLE_ID,
        .oem_revision = ACPI_OEM_REVISION,
        .creator_id   = ACPI_CREATOR_ID,
        .creator_revision = ACPI_CREATOR_REVISION
    }
};

struct acpi_20_xsdt Xsdt = {
    .header = {
        .signature    = ACPI_2_0_XSDT_SIGNATURE,
        .length       = sizeof(struct acpi_header),
        .revision     = ACPI_2_0_XSDT_REVISION,
        .oem_id       = ACPI_OEM_ID,
        .oem_table_id = ACPI_OEM_TABLE_ID,
        .oem_revision = ACPI_OEM_REVISION,
        .creator_id   = ACPI_CREATOR_ID,
        .creator_revision = ACPI_CREATOR_REVISION
    }
};


struct acpi_20_rsdp Rsdp = {
    .signature = ACPI_2_0_RSDP_SIGNATURE,
    .oem_id    = ACPI_OEM_ID,
    .revision  = ACPI_2_0_RSDP_REVISION,
    .length    = sizeof(struct acpi_20_rsdp)
};

/*
 * Local variables:
 * mode: C
 * c-set-style: "BSD"
 * c-basic-offset: 4
 * tab-width: 4
 * indent-tabs-mode: nil
 * End:
 */
