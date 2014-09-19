/*
 *	Intel CPU Microcode Update Driver for Linux
 *
 *	Copyright (C) 2000-2004 Tigran Aivazian
 *
 *	This driver allows to upgrade microcode on Intel processors
 *	belonging to IA-32 family - PentiumPro, Pentium II, 
 *	Pentium III, Xeon, Pentium 4, etc.
 *
 *	Reference: Section 8.10 of Volume III, Intel Pentium 4 Manual, 
 *	Order Number 245472 or free download from:
 *		
 *	http://developer.intel.com/design/pentium4/manuals/245472.htm
 *
 *	For more information, go to http://www.urbanmyth.org/microcode
 *
 *	This program is free software; you can redistribute it and/or
 *	modify it under the terms of the GNU General Public License
 *	as published by the Free Software Foundation; either version
 *	2 of the License, or (at your option) any later version.
 *
 *	1.0	16 Feb 2000, Tigran Aivazian <tigran@sco.com>
 *		Initial release.
 *	1.01	18 Feb 2000, Tigran Aivazian <tigran@sco.com>
 *		Added read() support + cleanups.
 *	1.02	21 Feb 2000, Tigran Aivazian <tigran@sco.com>
 *		Added 'device trimming' support. open(O_WRONLY) zeroes
 *		and frees the saved copy of applied microcode.
 *	1.03	29 Feb 2000, Tigran Aivazian <tigran@sco.com>
 *		Made to use devfs (/dev/cpu/microcode) + cleanups.
 *	1.04	06 Jun 2000, Simon Trimmer <simon@veritas.com>
 *		Added misc device support (now uses both devfs and misc).
 *		Added MICROCODE_IOCFREE ioctl to clear memory.
 *	1.05	09 Jun 2000, Simon Trimmer <simon@veritas.com>
 *		Messages for error cases (non Intel & no suitable microcode).
 *	1.06	03 Aug 2000, Tigran Aivazian <tigran@veritas.com>
 *		Removed ->release(). Removed exclusive open and status bitmap.
 *		Added microcode_rwsem to serialize read()/write()/ioctl().
 *		Removed global kernel lock usage.
 *	1.07	07 Sep 2000, Tigran Aivazian <tigran@veritas.com>
 *		Write 0 to 0x8B msr and then cpuid before reading revision,
 *		so that it works even if there were no update done by the
 *		BIOS. Otherwise, reading from 0x8B gives junk (which happened
 *		to be 0 on my machine which is why it worked even when I
 *		disabled update by the BIOS)
 *		Thanks to Eric W. Biederman <ebiederman@lnxi.com> for the fix.
 *	1.08	11 Dec 2000, Richard Schaal <richard.schaal@intel.com> and
 *			     Tigran Aivazian <tigran@veritas.com>
 *		Intel Pentium 4 processor support and bugfixes.
 *	1.09	30 Oct 2001, Tigran Aivazian <tigran@veritas.com>
 *		Bugfix for HT (Hyper-Threading) enabled processors
 *		whereby processor resources are shared by all logical processors
 *		in a single CPU package.
 *	1.10	28 Feb 2002 Asit K Mallick <asit.k.mallick@intel.com> and
 *		Tigran Aivazian <tigran@veritas.com>,
 *		Serialize updates as required on HT processors due to speculative
 *		nature of implementation.
 *	1.11	22 Mar 2002 Tigran Aivazian <tigran@veritas.com>
 *		Fix the panic when writing zero-length microcode chunk.
 *	1.12	29 Sep 2003 Nitin Kamble <nitin.a.kamble@intel.com>, 
 *		Jun Nakajima <jun.nakajima@intel.com>
 *		Support for the microcode updates in the new format.
 *	1.13	10 Oct 2003 Tigran Aivazian <tigran@veritas.com>
 *		Removed ->read() method and obsoleted MICROCODE_IOCFREE ioctl
 *		because we no longer hold a copy of applied microcode 
 *		in kernel memory.
 *	1.14	25 Jun 2004 Tigran Aivazian <tigran@veritas.com>
 *		Fix sigmatch() macro to handle old CPUs with pf == 0.
 *		Thanks to Stuart Swales for pointing out this bug.
 */

#include <xen/config.h>
#include <xen/lib.h>
#include <xen/kernel.h>
#include <xen/init.h>
#include <xen/sched.h>
#include <xen/smp.h>
#include <xen/spinlock.h>

#include <asm/current.h>
#include <asm/msr.h>
#include <asm/uaccess.h>
#include <asm/processor.h>

#define pr_debug(x...) ((void)0)
#define DEFINE_MUTEX(_m) DEFINE_SPINLOCK(_m)
#define mutex_lock(_m) spin_lock(_m)
#define mutex_unlock(_m) spin_unlock(_m)
#define vmalloc(_s) xmalloc_bytes(_s)
#define vfree(_p) xfree(_p)

#if 0
MODULE_DESCRIPTION("Intel CPU (IA-32) Microcode Update Driver");
MODULE_AUTHOR("Tigran Aivazian <tigran@veritas.com>");
MODULE_LICENSE("GPL");
#endif

static int verbose;
boolean_param("microcode.verbose", verbose);

#define MICROCODE_VERSION 	"1.14a"

#define DEFAULT_UCODE_DATASIZE 	(2000) 	  /* 2000 bytes */
#define MC_HEADER_SIZE		(sizeof (microcode_header_t))  	  /* 48 bytes */
#define DEFAULT_UCODE_TOTALSIZE (DEFAULT_UCODE_DATASIZE + MC_HEADER_SIZE) /* 2048 bytes */
#define EXT_HEADER_SIZE		(sizeof (struct extended_sigtable)) /* 20 bytes */
#define EXT_SIGNATURE_SIZE	(sizeof (struct extended_signature)) /* 12 bytes */
#define DWSIZE			(sizeof (u32))
#define get_totalsize(mc) \
	(((microcode_t *)mc)->hdr.totalsize ? \
	 ((microcode_t *)mc)->hdr.totalsize : DEFAULT_UCODE_TOTALSIZE)
#define get_datasize(mc) \
	(((microcode_t *)mc)->hdr.datasize ? \
	 ((microcode_t *)mc)->hdr.datasize : DEFAULT_UCODE_DATASIZE)

#define sigmatch(s1, s2, p1, p2) \
	(((s1) == (s2)) && (((p1) & (p2)) || (((p1) == 0) && ((p2) == 0))))

#define exttable_size(et) ((et)->count * EXT_SIGNATURE_SIZE + EXT_HEADER_SIZE)

/* serialize access to the physical write to MSR 0x79 */
static DEFINE_SPINLOCK(microcode_update_lock);

/* no concurrent ->write()s are allowed on /dev/cpu/microcode */
static DEFINE_MUTEX(microcode_mutex);

static void __user *user_buffer;	/* user area microcode data buffer */
static unsigned int user_buffer_size;	/* it's size */

typedef enum mc_error_code {
	MC_SUCCESS 	= 0,
	MC_IGNORED 	= 1,
	MC_NOTFOUND 	= 2,
	MC_MARKED 	= 3,
	MC_ALLOCATED 	= 4,
} mc_error_code_t;

static struct ucode_cpu_info {
	unsigned int sig;
	unsigned int pf, orig_pf;
	unsigned int rev;
	unsigned int cksum;
	mc_error_code_t err;
	microcode_t *mc;
} ucode_cpu_info[NR_CPUS];
				
static void collect_cpu_info (void *unused)
{
	int cpu_num = smp_processor_id();
	struct cpuinfo_x86 *c = cpu_data + cpu_num;
	struct ucode_cpu_info *uci = ucode_cpu_info + cpu_num;
	unsigned int val[2];

	uci->sig = uci->pf = uci->rev = uci->cksum = 0;
	uci->err = MC_NOTFOUND;
	uci->mc = NULL;

	if (c->x86_vendor != X86_VENDOR_INTEL || c->x86 < 6 ||
	    	cpu_has(c, X86_FEATURE_IA64)) {
		printk(KERN_ERR "microcode: CPU%d not a capable Intel processor\n", cpu_num);
		return;
	} else {
		uci->sig = cpuid_eax(0x00000001);

		if ((c->x86_model >= 5) || (c->x86 > 6)) {
			/* get processor flags from MSR 0x17 */
			rdmsr(MSR_IA32_PLATFORM_ID, val[0], val[1]);
			uci->pf = 1 << ((val[1] >> 18) & 7);
		}
		uci->orig_pf = uci->pf;
	}

	wrmsr(MSR_IA32_UCODE_REV, 0, 0);
	/* see notes above for revision 1.07.  Apparent chip bug */
	sync_core();
	/* get the current revision from MSR 0x8B */
	rdmsr(MSR_IA32_UCODE_REV, val[0], uci->rev);
	pr_debug("microcode: collect_cpu_info : sig=0x%x, pf=0x%x, rev=0x%x\n",
			uci->sig, uci->pf, uci->rev);
}

static inline void mark_microcode_update (int cpu_num, microcode_header_t *mc_header, int sig, int pf, int cksum)
{
	struct ucode_cpu_info *uci = ucode_cpu_info + cpu_num;

	pr_debug("Microcode Found.\n");
	pr_debug("   Header Revision 0x%x\n", mc_header->hdrver);
	pr_debug("   Loader Revision 0x%x\n", mc_header->ldrver);
	pr_debug("   Revision 0x%x \n", mc_header->rev);
	pr_debug("   Date %x/%x/%x\n",
		((mc_header->date >> 24 ) & 0xff),
		((mc_header->date >> 16 ) & 0xff),
		(mc_header->date & 0xFFFF));
	pr_debug("   Signature 0x%x\n", sig);
	pr_debug("   Type 0x%x Family 0x%x Model 0x%x Stepping 0x%x\n",
		((sig >> 12) & 0x3),
		((sig >> 8) & 0xf),
		((sig >> 4) & 0xf),
		((sig & 0xf)));
	pr_debug("   Processor Flags 0x%x\n", pf);
	pr_debug("   Checksum 0x%x\n", cksum);

	if (mc_header->rev < uci->rev) {
		if (uci->err == MC_NOTFOUND) {
			uci->err = MC_IGNORED;
			uci->cksum = mc_header->rev;
		} else if (uci->err == MC_IGNORED && uci->cksum < mc_header->rev)
			uci->cksum = mc_header->rev;
	} else if (mc_header->rev == uci->rev) {
		if (uci->err < MC_MARKED) {
			/* notify the caller of success on this cpu */
			uci->err = MC_SUCCESS;
		}
	} else if (uci->err != MC_ALLOCATED || mc_header->rev > uci->mc->hdr.rev) {
		pr_debug("microcode: CPU%d found a matching microcode update with "
			" revision 0x%x (current=0x%x)\n", cpu_num, mc_header->rev, uci->rev);
		uci->cksum = cksum;
		uci->pf = pf; /* keep the original mc pf for cksum calculation */
		uci->err = MC_MARKED; /* found the match */
		for_each_online_cpu(cpu_num) {
			if (ucode_cpu_info + cpu_num != uci
			    && ucode_cpu_info[cpu_num].mc == uci->mc) {
				uci->mc = NULL;
				break;
			}
		}
		if (uci->mc != NULL) {
			vfree(uci->mc);
			uci->mc = NULL;
		}
	}
	return;
}

static int find_matching_ucodes (void) 
{
	int cursor = 0;
	int error = 0;

	while (cursor + MC_HEADER_SIZE < user_buffer_size) {
		microcode_header_t mc_header;
		void *newmc = NULL;
		int i, sum, cpu_num, allocated_flag, total_size, data_size, ext_table_size;

		if (copy_from_user(&mc_header, user_buffer + cursor, MC_HEADER_SIZE)) {
			printk(KERN_ERR "microcode: error! Can not read user data\n");
			error = -EFAULT;
			goto out;
		}

		total_size = get_totalsize(&mc_header);
		if (cursor + total_size > user_buffer_size) {
			printk(KERN_ERR "microcode: error! Bad data in microcode data file\n");
			error = -EINVAL;
			goto out;
		}

		data_size = get_datasize(&mc_header);
		if (data_size + MC_HEADER_SIZE > total_size) {
			printk(KERN_ERR "microcode: error! Bad data in microcode data file\n");
			error = -EINVAL;
			goto out;
		}

		if (mc_header.ldrver != 1 || mc_header.hdrver != 1) {
			printk(KERN_ERR "microcode: error! Unknown microcode update format\n");
			error = -EINVAL;
			goto out;
		}

		for_each_online_cpu(cpu_num) {
			struct ucode_cpu_info *uci = ucode_cpu_info + cpu_num;

			if (sigmatch(mc_header.sig, uci->sig, mc_header.pf, uci->orig_pf))
				mark_microcode_update(cpu_num, &mc_header, mc_header.sig, mc_header.pf, mc_header.cksum);
		}

		ext_table_size = total_size - (MC_HEADER_SIZE + data_size);
		if (ext_table_size) {
			struct extended_sigtable ext_header;
			struct extended_signature ext_sig;
			int ext_sigcount;

			if ((ext_table_size < EXT_HEADER_SIZE) 
					|| ((ext_table_size - EXT_HEADER_SIZE) % EXT_SIGNATURE_SIZE)) {
				printk(KERN_ERR "microcode: error! Bad data in microcode data file\n");
				error = -EINVAL;
				goto out;
			}
			if (copy_from_user(&ext_header, user_buffer + cursor 
					+ MC_HEADER_SIZE + data_size, EXT_HEADER_SIZE)) {
				printk(KERN_ERR "microcode: error! Can not read user data\n");
				error = -EFAULT;
				goto out;
			}
			if (ext_table_size != exttable_size(&ext_header)) {
				printk(KERN_ERR "microcode: error! Bad data in microcode data file\n");
				error = -EFAULT;
				goto out;
			}

			ext_sigcount = ext_header.count;
			
			for (i = 0; i < ext_sigcount; i++) {
				if (copy_from_user(&ext_sig, user_buffer + cursor + MC_HEADER_SIZE + data_size + EXT_HEADER_SIZE 
						+ EXT_SIGNATURE_SIZE * i, EXT_SIGNATURE_SIZE)) {
					printk(KERN_ERR "microcode: error! Can not read user data\n");
					error = -EFAULT;
					goto out;
				}
				for_each_online_cpu(cpu_num) {
					struct ucode_cpu_info *uci = ucode_cpu_info + cpu_num;

					if (sigmatch(ext_sig.sig, uci->sig, ext_sig.pf, uci->orig_pf)) {
						mark_microcode_update(cpu_num, &mc_header, ext_sig.sig, ext_sig.pf, ext_sig.cksum);
					}
				}
			}
		}
		/* now check if any cpu has matched */
		allocated_flag = 0;
		sum = 0;
		for_each_online_cpu(cpu_num) {
			if (ucode_cpu_info[cpu_num].err == MC_MARKED) { 
				struct ucode_cpu_info *uci = ucode_cpu_info + cpu_num;
				if (!allocated_flag) {
					allocated_flag = 1;
					newmc = vmalloc(total_size);
					if (!newmc) {
						printk(KERN_ERR "microcode: error! Can not allocate memory\n");
						error = -ENOMEM;
						goto out;
					}
					if (copy_from_user(newmc + MC_HEADER_SIZE, 
								user_buffer + cursor + MC_HEADER_SIZE, 
								total_size - MC_HEADER_SIZE)) {
						printk(KERN_ERR "microcode: error! Can not read user data\n");
						vfree(newmc);
						error = -EFAULT;
						goto out;
					}
					memcpy(newmc, &mc_header, MC_HEADER_SIZE);
					/* check extended table checksum */
					if (ext_table_size) {
						int ext_table_sum = 0;
						int * ext_tablep = (((void *) newmc) + MC_HEADER_SIZE + data_size);
						i = ext_table_size / DWSIZE;
						while (i--) ext_table_sum += ext_tablep[i];
						if (ext_table_sum) {
							printk(KERN_WARNING "microcode: aborting, bad extended signature table checksum\n");
							vfree(newmc);
							error = -EINVAL;
							goto out;
						}
					}

					/* calculate the checksum */
					i = (MC_HEADER_SIZE + data_size) / DWSIZE;
					while (i--) sum += ((int *)newmc)[i];
					sum -= (mc_header.sig + mc_header.pf + mc_header.cksum);
				}
				ucode_cpu_info[cpu_num].mc = newmc;
				ucode_cpu_info[cpu_num].err = MC_ALLOCATED; /* mc updated */
				if (sum + uci->sig + uci->pf + uci->cksum != 0) {
					printk(KERN_ERR "microcode: CPU%d aborting, bad checksum\n", cpu_num);
					error = -EINVAL;
					goto out;
				}
			}
		}
		cursor += total_size; /* goto the next update patch */
	} /* end of while */
out:
	return error;
}

static void do_update_one (void * unused)
{
	unsigned long flags;
	unsigned int val[2];
	int cpu_num = smp_processor_id();
	struct ucode_cpu_info *uci = ucode_cpu_info + cpu_num;

	if (uci->mc == NULL) {
		if (verbose) {
			if (uci->err == MC_SUCCESS)
				printk(KERN_INFO "microcode: CPU%d already at revision 0x%x\n",
					cpu_num, uci->rev);
			else
				printk(KERN_INFO "microcode: No new microcode data for CPU%d\n", cpu_num);
		}
		return;
	}

	/* serialize access to the physical write to MSR 0x79 */
	spin_lock_irqsave(&microcode_update_lock, flags);          

	/* write microcode via MSR 0x79 */
	wrmsr(MSR_IA32_UCODE_WRITE,
		(unsigned long) uci->mc->bits, 
		(unsigned long) uci->mc->bits >> 16 >> 16);
	wrmsr(MSR_IA32_UCODE_REV, 0, 0);

	/* see notes above for revision 1.07.  Apparent chip bug */
	sync_core();

	/* get the current revision from MSR 0x8B */
	rdmsr(MSR_IA32_UCODE_REV, val[0], val[1]);

	/* notify the caller of success on this cpu */
	uci->err = MC_SUCCESS;
	spin_unlock_irqrestore(&microcode_update_lock, flags);
	printk(KERN_INFO "microcode: CPU%d updated from revision "
	       "0x%x to 0x%x, date = %08x \n", 
	       cpu_num, uci->rev, val[1], uci->mc->hdr.date);
	return;
}

static int do_microcode_update (void)
{
	int i, error;

	if (on_each_cpu(collect_cpu_info, NULL, 1, 1) != 0) {
		printk(KERN_ERR "microcode: Error! Could not run on all processors\n");
		error = -EIO;
		goto out;
	}

	if ((error = find_matching_ucodes())) {
		printk(KERN_ERR "microcode: Error in the microcode data\n");
		goto out_free;
	}

	if (on_each_cpu(do_update_one, NULL, 1, 1) != 0) {
		printk(KERN_ERR "microcode: Error! Could not run on all processors\n");
		error = -EIO;
	}

out_free:
	for_each_online_cpu(i) {
		if (ucode_cpu_info[i].mc) {
			int j;
			void *tmp = ucode_cpu_info[i].mc;
			vfree(tmp);
			for_each_online_cpu(j) {
				if (ucode_cpu_info[j].mc == tmp)
					ucode_cpu_info[j].mc = NULL;
			}
		}
		if (ucode_cpu_info[i].err == MC_IGNORED && verbose)
			printk(KERN_WARNING "microcode: CPU%d not 'upgrading' to earlier revision"
			       " 0x%x (current=0x%x)\n", i, ucode_cpu_info[i].cksum, ucode_cpu_info[i].rev);
	}
out:
	return error;
}

int microcode_update(XEN_GUEST_HANDLE(void) buf, unsigned long len)
{
	int ret;

	if (len != (typeof(user_buffer_size))len) {
		printk(KERN_ERR "microcode: too much data\n");
		return -E2BIG;
	}

	mutex_lock(&microcode_mutex);

	user_buffer = buf.p;
	user_buffer_size = len;

	ret = do_microcode_update();

	mutex_unlock(&microcode_mutex);

	return ret;
}