/* -*-  Mode:C; c-basic-offset:4; tab-width:4; indent-tabs-mode:nil -*- */
/*
 * vmx.h: prototype for generial vmx related interface
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
 * 	Kun Tian (Kevin Tian) (kevin.tian@intel.com)
 */

#ifndef _ASM_IA64_VT_H
#define _ASM_IA64_VT_H

#include <public/hvm/ioreq.h>
#define vmx_user_mode(regs) (((struct ia64_psr *)&(regs)->cr_ipsr)->vm == 1)

#define VCPU_LID(v) (((u64)(v)->vcpu_id)<<24)

extern void identify_vmx_feature(void);
extern unsigned int vmx_enabled;
extern void vmx_init_env(void);
extern int vmx_final_setup_guest(struct vcpu *v);
extern void vmx_save_state(struct vcpu *v);
extern void vmx_load_state(struct vcpu *v);
extern int vmx_setup_platform(struct domain *d);
extern void vmx_do_resume(struct vcpu *v);
extern void vmx_io_assist(struct vcpu *v);
extern int ia64_hypercall (struct pt_regs *regs);
extern void vmx_save_state(struct vcpu *v);
extern void vmx_load_state(struct vcpu *v);
extern unsigned long __gpfn_to_mfn_foreign(struct domain *d, unsigned long gpfn);
extern void sync_split_caches(void);
extern void set_privileged_operation_isr (struct vcpu *vcpu,int inst);
extern void privilege_op (struct vcpu *vcpu);
extern void set_ifa_itir_iha (struct vcpu *vcpu, u64 vadr,
          int set_ifa, int set_itir, int set_iha);
extern void inject_guest_interruption(struct vcpu *vcpu, u64 vec);
extern void set_illegal_op_isr (struct vcpu *vcpu);
extern void illegal_op (struct vcpu *vcpu);
extern void set_rsv_reg_field_isr (struct vcpu *vcpu);
extern void rsv_reg_field (struct vcpu *vcpu);
extern void vmx_relinquish_guest_resources(struct domain *d);
extern void vmx_relinquish_vcpu_resources(struct vcpu *v);
extern void vmx_die_if_kernel(char *str, struct pt_regs *regs, long err);
extern void vmx_send_assist_req(struct vcpu *v);
extern void deliver_pal_init(struct vcpu *vcpu);
extern void vmx_pend_pal_init(struct domain *d);

static inline vcpu_iodata_t *get_vio(struct vcpu *v)
{
    struct domain *d = v->domain;
    shared_iopage_t *p = (shared_iopage_t *)d->arch.vmx_platform.ioreq.va;
    ASSERT((v == current) || spin_is_locked(&d->arch.vmx_platform.ioreq.lock));
    ASSERT(d->arch.vmx_platform.ioreq.va != NULL);
    return &p->vcpu_iodata[v->vcpu_id];
}
#endif /* _ASM_IA64_VT_H */
