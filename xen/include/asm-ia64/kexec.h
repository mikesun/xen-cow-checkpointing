#ifndef __IA64_KEXEC_H__
#define __IA64_KEXEC_H__

#include <xen/types.h>
#include <xen/kexec.h>

extern const unsigned int relocate_new_kernel_size;
extern void relocate_new_kernel(unsigned long, unsigned long,
                                struct ia64_boot_param *, unsigned long);
void crash_save_xen_notes(void);
void machine_kexec(xen_kexec_image_t *image);
unsigned long kdump_find_rsvd_region(unsigned long size,
                                     struct rsvd_region *rsvd_regions, int n);

#endif /* __IA64_KEXEC_H__ */
