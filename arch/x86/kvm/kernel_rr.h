#ifndef __KVM_X86_KERNEL_RR_H
#define __KVM_X86_KERNEL_RR_H

// #include <linux/kvm_host.h>
#include <asm/kernel_rr.h>

void rr_record_event(struct kvm_vcpu *vcpu, int event_type, void *opaque);
lapic_log* create_lapic_log(int delivery_mode, int vector, int trig_mode);
int rr_in_record(void);
int rr_in_replay(void);
void rr_set_in_record(struct kvm *kvm, int record, struct rr_record_data data);
void rr_set_in_replay(struct kvm_vcpu *vcpu, int replay);
void rr_get_regs(struct kvm_vcpu *vcpu, struct kvm_regs *regs);
void rr_set_regs(struct kvm_vcpu *vcpu, struct kvm_regs *regs);
void clear_events(void);
void rr_get_sregs(struct kvm_vcpu *vcpu, __maybe_unused struct kvm_sregs *sregs);

unsigned long get_rsi(struct kvm_vcpu *vcpu);

int rr_handle_breakpoint(struct kvm_vcpu *vcpu);

int rr_do_singlestep(struct kvm_vcpu *vcpu);
void rr_update_apicv_inhibit(struct kvm *kvm);

void rr_set_reg(struct kvm_vcpu *vcpu, int index, unsigned long val);

void kvm_start_inst_cnt(struct kvm_vcpu *vcpu);
void kvm_stop_inst_cnt(struct kvm_vcpu *vcpu);
u64 kvm_get_inst_cnt(struct kvm_vcpu *vcpu);

int rr_get_event_list_length(void);
void rr_copy_to_event_list(struct rr_event_list_t *event_list, int len);
rr_event_log rr_get_next_event(void);

void rr_trace_memory_write(struct kvm_vcpu *vcpu, gpa_t gpa);
rr_mem_access_log rr_get_next_mem_log(void);
int rr_get_mem_log_list_length(void);
void rr_clear_mem_log(void);

void handle_hypercall_cfu(struct kvm_vcpu *vcpu,
                          unsigned long src,
                          unsigned long dest,
                          unsigned long len);
void handle_hypercall_random(struct kvm_vcpu *vcpu,
                                unsigned long buf,
                                unsigned long len);
void handle_hypercall_getuser(struct kvm_vcpu *vcpu,
                              unsigned long val);


void rr_register_ivshmem(struct kvm *kvm, unsigned long addr);
void rr_sync_inst_cnt(struct kvm_vcpu *vcpu, unsigned long spin_cnt);
void put_result_buffer(unsigned long user_addr);
unsigned long get_result_buffer(void);
void set_buffer_inject_flag(int bit);
int rr_queue_full(void);
#endif /* __KVM_X86_KERNEL_RR_H */