/*
 * Copyright (C) 2006 Hollis Blanchard <hollisb@us.ibm.com>, IBM Corporation
 * Tristan Gingold <tristan.gingold@bull.net>
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307 USA
 */

/*
 * This code is mostly taken from ia64-xen files xcom_mini.c and xencomm.c.
 * Changes: Dietmar Hahn <dietmar.hahn@fujitsu-siemens.com
 */


#include <os.h>
#include <hypervisor.h>
#include <xen/xencomm.h>
#include <xen/grant_table.h>


#define XENCOMM_MINI_ADDRS 3
struct xencomm_mini
{
	struct xencomm_desc _desc;
	uint64_t address[XENCOMM_MINI_ADDRS];
};

#define xen_guest_handle(hnd)  ((hnd).p)


/* Translate virtual address to physical address.  */
uint64_t
xencomm_vaddr_to_paddr(uint64_t vaddr)
{
	if (IA64_RR_EXTR(vaddr) == 5)
		return KERN_VIRT_2_PHYS(vaddr);

	if (IA64_RR_EXTR(vaddr) == 7)
		return __pa(vaddr);

	return 0;
}

#define min(a,b) (((a) < (b)) ? (a) : (b))
static int
xencomm_init_desc(struct xencomm_desc *desc, void *buffer, unsigned long bytes)
{
	unsigned long recorded = 0;
	int i = 0;

	if ((buffer == NULL) && (bytes > 0))
		BUG();

	/* record the physical pages used */
	if (buffer == NULL)
		desc->nr_addrs = 0;

	while ((recorded < bytes) && (i < desc->nr_addrs)) {
		unsigned long vaddr = (unsigned long)buffer + recorded;
		unsigned long paddr;
		int offset;
		int chunksz;

		offset = vaddr % PAGE_SIZE; /* handle partial pages */
		chunksz = min(PAGE_SIZE - offset, bytes - recorded);

		paddr = xencomm_vaddr_to_paddr(vaddr);
		if (paddr == ~0UL) {
			printk("%s: couldn't translate vaddr %lx\n",
			       __func__, vaddr);
			return -EINVAL;
		}

		desc->address[i++] = SWAP(paddr);
		recorded += chunksz;
	}
	if (recorded < bytes) {
		printk("%s: could only translate %ld of %ld bytes\n",
		       __func__, recorded, bytes);
		return -ENOSPC;
	}

	/* mark remaining addresses invalid (just for safety) */
	while (i < desc->nr_addrs)
		desc->address[i++] = SWAP(XENCOMM_INVALID);
	desc->magic = SWAP(XENCOMM_MAGIC);
	return 0;
}

static void *
xencomm_alloc_mini(struct xencomm_mini *area, int *nbr_area)
{
	unsigned long base;
	unsigned int pageoffset;

	while (*nbr_area >= 0) {
		/* Allocate an area.  */
		(*nbr_area)--;

		base = (unsigned long)(area + *nbr_area);
		pageoffset = base % PAGE_SIZE; 

		/* If the area does not cross a page, use it.  */
		if ((PAGE_SIZE - pageoffset) >= sizeof(struct xencomm_mini))
			return &area[*nbr_area];
	}
	/* No more area.  */
	return NULL;
}

int
xencomm_create_mini(struct xencomm_mini *area, int *nbr_area,
                    void *buffer, unsigned long bytes,
                    struct xencomm_handle **ret)
{
	struct xencomm_desc *desc;
	int rc;
	unsigned long res;

	desc = xencomm_alloc_mini(area, nbr_area);
	if (!desc)
		return -ENOMEM;
	desc->nr_addrs = XENCOMM_MINI_ADDRS;

	rc = xencomm_init_desc(desc, buffer, bytes);
	if (rc)
		return rc;

	res = xencomm_vaddr_to_paddr((unsigned long)desc);
	if (res == ~0UL)
		return -EINVAL;

	*ret = (struct xencomm_handle*)res;
	return 0;
}

static int
xencommize_mini_grant_table_op(struct xencomm_mini *xc_area, int *nbr_area,
                               unsigned int cmd, void *op, unsigned int count,
                               struct xencomm_handle **desc)
{
	struct xencomm_handle *desc1;
	unsigned int argsize=0;
	int rc;

	switch (cmd) {
	case GNTTABOP_map_grant_ref:
		argsize = sizeof(struct gnttab_map_grant_ref);
		break;
	case GNTTABOP_unmap_grant_ref:
		argsize = sizeof(struct gnttab_unmap_grant_ref);
		break;
	case GNTTABOP_setup_table:
	{
		struct gnttab_setup_table *setup = op;

		argsize = sizeof(*setup);

		if (count != 1)
			return -EINVAL;
		rc = xencomm_create_mini
		        (xc_area, nbr_area,
		         (void*)SWAP((uint64_t)
				     xen_guest_handle(setup->frame_list)),
		         SWAP(setup->nr_frames)
		         * sizeof(*xen_guest_handle(setup->frame_list)),
		         &desc1);
		if (rc)
			return rc;
		set_xen_guest_handle(setup->frame_list,
				     (void *)SWAP((uint64_t)desc1));
		break;
	}
	case GNTTABOP_dump_table:
		argsize = sizeof(struct gnttab_dump_table);
		break;
	case GNTTABOP_transfer:
		argsize = sizeof(struct gnttab_transfer);
		break;
	case GNTTABOP_copy:
		argsize = sizeof(struct gnttab_copy);
		break;
	default:
		printk("%s: unknown mini grant table op %d\n", __func__, cmd);
		BUG();
	}

	rc = xencomm_create_mini(xc_area, nbr_area, op, count * argsize, desc);

	return rc;
}

int
xencomm_mini_hypercall_grant_table_op(unsigned int cmd, void *op,
                                      unsigned int count)
{
	int rc;
	struct xencomm_handle *desc;
	int nbr_area = 2;
	struct xencomm_mini xc_area[2];

	rc = xencommize_mini_grant_table_op(xc_area, &nbr_area,
					    cmd, op, count, &desc);
	if (rc)
		return rc;
	return xencomm_arch_hypercall_grant_table_op(cmd, desc, count);
}

static void
gnttab_map_grant_ref_pre(struct gnttab_map_grant_ref *uop)
{
	uint32_t flags;

	flags = uop->flags;

	if (flags & GNTMAP_host_map) {
		if (flags & GNTMAP_application_map) {
			printk("GNTMAP_application_map is not supported yet: "
			       "flags 0x%x\n", flags);
			BUG();
		}
		if (flags & GNTMAP_contains_pte) {
			printk("GNTMAP_contains_pte is not supported yet flags "
			       "0x%x\n", flags);
			BUG();
		}
	} else if (flags & GNTMAP_device_map) {
		printk("GNTMAP_device_map is not supported yet 0x%x\n", flags);
		BUG();//XXX not yet. actually this flag is not used.
	} else {
		BUG();
	}
}

int
HYPERVISOR_grant_table_op(unsigned int cmd, void *uop, unsigned int count)
{
	if (cmd == GNTTABOP_map_grant_ref) {
		unsigned int i;
		for (i = 0; i < count; i++) {
			gnttab_map_grant_ref_pre(
			        (struct gnttab_map_grant_ref*)uop + i);
		}
	}
	return xencomm_mini_hypercall_grant_table_op(cmd, uop, count);
}

	/* In fw.S */
extern int xencomm_arch_hypercall_suspend(struct xencomm_handle *arg);
int
HYPERVISOR_suspend(unsigned long srec)
{
        struct sched_shutdown arg;

        arg.reason = (uint32_t)SWAP((uint32_t)SHUTDOWN_suspend);

        return xencomm_arch_hypercall_suspend(xencomm_create_inline(&arg));
}

