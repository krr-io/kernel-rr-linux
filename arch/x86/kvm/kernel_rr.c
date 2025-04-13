#include <linux/fs.h>
#include <asm/segment.h>
#include <asm/uaccess.h>
#include <linux/buffer_head.h>
#include <linux/spinlock.h>
#include <asm/debugreg.h>

#include "x86.h"
#include "kvm_cache_regs.h"
#include "kvm_emulate.h"

#include <asm/kernel_rr.h>

#include "kernel_rr.h"

static void handle_event_interrupt(struct kvm_vcpu *vcpu, void *opaque);

int in_record = 0;
int in_replay = 0;

DEFINE_SPINLOCK(queue_lock);

rr_event_log *rr_event_log_head = NULL;
rr_event_log *rr_event_log_tail = NULL;
rr_event_log *rr_event_cur = NULL;
int total_event_cnt = 0;

rr_mem_access_log *rr_mem_log_head = NULL;
rr_mem_access_log *rr_mem_log_tail = NULL;
rr_mem_access_log *rr_mem_log_cur = NULL;

rr_random *random_cur = NULL;

// == with hypercall
const unsigned long syscall_addr = 0xffffffff81800000; // info addr entry_SYSCALL_64
const unsigned long pf_excep_addr = 0xffffffff81741960; // info addr exc_page_fault
const unsigned long copy_from_iter_addr = 0xffffffff8144af0d; // lib/iov_iter.c:186
const unsigned long copy_from_user_addr = 0xffffffff814528e7; // lib/usercopy.c:21
const unsigned long copy_page_from_iter_addr = 0xffffffff8144dd7e;
const unsigned long strncpy_addr = 0xffffffff81483732; // lib/strncpy_from_user.c:141
const unsigned long get_user_addr = 0xffffffff816c2220; // arch/x86/lib/getuser.S:103
const unsigned long strnlen_user_addr = 0xffffffff8146bb66; // lib/strnlen_user.c:115

const unsigned long random_bytes_addr_start = 0xffffffff81533660; // b _get_random_bytes
const unsigned long random_bytes_addr_end = 0xffffffff81533800; // b drivers/char/random.c:382

const unsigned long last_removed_addr = 0;

const unsigned long uaccess_begin = 0xffffffff811e084c;
const unsigned long default_idle_addr = 0xffffffff81741feb; // arch/x86/kernel/process.c:731
const unsigned long wait_lock_addr = 0xffffffff810ee480; //


static unsigned long ivshmem_base_addr = 0;

static unsigned long user_result_buffer;

static volatile unsigned long buffer_inject_flag = 0;


void set_buffer_inject_flag(int bit)
{
    set_bit(bit, &buffer_inject_flag);
}

void put_result_buffer(unsigned long user_addr)
{
    user_result_buffer = user_addr;
}

unsigned long get_result_buffer(void)
{
    return user_result_buffer;
}

/* ======== RR shared memory functions =========== */


static void rr_modify_rdtsc(struct kvm_vcpu *vcpu, unsigned long inst_cnt, unsigned long rip)
{
    rr_event_guest_queue_header header;
    rr_event_entry_header entry_header;
    rr_io_input input;
    unsigned long entry_size = sizeof(rr_io_input) + sizeof(rr_event_entry_header);

    if (__copy_from_user(&header, (void __user *)ivshmem_base_addr, sizeof(rr_event_guest_queue_header))) {
        printk(KERN_WARNING "Failed to read from user memory\n");
        return;
    }

    if (__copy_from_user(&entry_header, (void __user *)ivshmem_base_addr + header.current_byte - entry_size, sizeof(rr_event_entry_header))) {
        printk(KERN_WARNING "Failed to read from user memory\n");
        return;
    }

    if (entry_header.type != EVENT_TYPE_RDTSC) {
        printk(KERN_WARNING "Current not rdtsc\n");
        return;
    }

    if (__copy_from_user(&input, (void __user *)ivshmem_base_addr + header.current_byte - entry_size + sizeof(rr_event_entry_header), sizeof(rr_io_input))) {
        printk(KERN_WARNING "Failed to read from user memory\n");
        return;
    }

    input.inst_cnt = inst_cnt;
    input.rip = rip;
    input.id = vcpu->vcpu_id;

    if (__copy_to_user((void __user *)ivshmem_base_addr + header.current_byte - entry_size + sizeof(rr_event_entry_header),
                       &input, sizeof(rr_io_input))) {
        printk(KERN_WARNING "Failed to write to user memory\n");
        return;
    }
}


static void rr_append_to_queue(void *event, unsigned long size, int type)
{
    rr_event_guest_queue_header header;
    rr_event_entry_header entry_header = {
        .type = type,
    };

    if (__copy_from_user(&header, (void __user *)ivshmem_base_addr, sizeof(rr_event_guest_queue_header))) {
        printk(KERN_WARNING "Failed to read from user memory\n");
    }

    if (header.current_byte + \
		sizeof(rr_event_entry_header) + \
		size > header.total_size) {
        printk(KERN_WARNING "RR queue is full, drop from start, current_byte=%lu\n",
               header.current_byte);
    }

    if (__copy_to_user((void __user *)(ivshmem_base_addr + header.current_byte),
        &entry_header, sizeof(rr_event_entry_header))) {
        printk(KERN_WARNING "Failed to copy to user memory\n");
    }
    header.current_byte += sizeof(rr_event_entry_header);

    if (__copy_to_user((void __user *)(ivshmem_base_addr + header.current_byte),
        event, size)) {
        printk(KERN_WARNING "Failed to copy to user memory\n");
    }
    header.current_byte += size;

    // printk(KERN_INFO "[%d]Event %d header %d size %lu loc 0x%lx\n",
    //        header.current_pos, type, sizeof(rr_event_entry_header),
    //        size, ivshmem_base_addr + header.current_byte);

    header.current_pos++;

    if (__copy_to_user((void __user *)ivshmem_base_addr,
        &header, sizeof(rr_event_guest_queue_header))) {
        printk(KERN_WARNING "Failed to copy from user memory\n");
    }

    return;
}

static void handle_event_io_in_shm(struct kvm_vcpu *vcpu, void *opaque)
{
    void *io_val = opaque;
    // unsigned long inst_cnt, rip = kvm_get_inst_cnt(vcpu), kvm_get_linear_rip(vcpu);
    // int id = vcpu->vcpu_id;
    rr_io_input event = {
        .value = *((unsigned long *)io_val),
        .inst_cnt = kvm_get_inst_cnt(vcpu),
        .rip = kvm_get_linear_rip(vcpu),
        .id = vcpu->vcpu_id,
    };
    int i;

    if (!event.inst_cnt)
        printk(KERN_WARNING "kernel_rr inst_cnt 0");

    if (vcpu->arch.pio.count > 0) {
        // if (vcpu->arch.pio.count > 1)
        //     printk(KERN_INFO "Repetitive pio inst %d, %lu", vcpu->arch.pio.count, event.inst_cnt);
        // else
        //     printk(KERN_INFO "original pio 0x%lx", *((unsigned long *)io_val));
        for (i = 0; i < vcpu->arch.pio.count; i++) {
            // event.value = *((unsigned long *)io_val);
            memcpy(&event.value, io_val, vcpu->arch.pio.size);
            rr_append_to_queue(&event, sizeof(rr_io_input), EVENT_TYPE_IO_IN);
            io_val += vcpu->arch.pio.size;
        }
    } else {
        event.value = *((unsigned long *)io_val);
        rr_append_to_queue(&event, sizeof(rr_io_input), EVENT_TYPE_IO_IN);
    }
    // printk(KERN_INFO "rdtsc: inst=%lu\n", event.inst_cnt);
}

static void handle_event_interrupt_shm(struct kvm_vcpu *vcpu, void *opaque)
{
    unsigned int *int_vector = (unsigned int *)opaque;
    rr_interrupt event = {
        .id = vcpu->vcpu_id,
        .vector = *int_vector,
        .inst_cnt = kvm_get_inst_cnt(vcpu),
        .rip = kvm_get_linear_rip(vcpu),
        .from = 0,
    };

    rr_get_regs(vcpu, &event.regs);

    WARN_ON(is_guest_mode(vcpu));

    // if (test_and_clear_bit(INJ_DMA_NET_BUF_BIT, &buffer_inject_flag)) {
    //     event.inject_buf_flag |= (1 << (INJ_DMA_NET_BUF_BIT - 1));
    // }

    rr_append_to_queue(&event, sizeof(rr_interrupt), EVENT_TYPE_INTERRUPT);

    if (vcpu->enable_trace) {
        if (static_call(kvm_x86_get_cpl)(vcpu) == 0)
            rr_reset_gp_inst_counter(vcpu, true, false);
    }
    // printk(KERN_INFO "interrupt in kernel %d: inst=%lu\n", event.event.interrupt.vector, event.inst_cnt);
}

static void handle_event_rdtsc_shm(struct kvm_vcpu *vcpu, void *opaque)
{
    // unsigned long *tsc_val = (unsigned long *)opaque;    
    // rr_io_input event = {
    //     .value = *tsc_val,
    //     .inst_cnt = kvm_get_inst_cnt(vcpu),
    //     .rip = kvm_get_linear_rip(vcpu),
    //     .id = vcpu->vcpu_id,
    // };

    rr_modify_rdtsc(vcpu, kvm_get_inst_cnt(vcpu), kvm_get_linear_rip(vcpu));

    // printk(KERN_INFO "rdtsc: inst=%lu\n", event.inst_cnt);
    // rr_append_to_queue(&event, sizeof(rr_io_input), EVENT_TYPE_RDTSC);
}

static void handle_event_exception_shm(struct kvm_vcpu *vcpu, void *opaque)
{
    struct rr_exception_detail *excp = (struct rr_exception_detail *)opaque;
    unsigned long dr6;
    struct kvm_sregs sregs;

    rr_exception event = {
        .id = vcpu->vcpu_id,
        .exception_index = excp->vector,
        .cr2 = excp->dr6,
        .inst_cnt = kvm_get_inst_cnt(vcpu),
    };

    rr_get_sregs(vcpu, &sregs);
    rr_get_regs(vcpu, &event.regs);

    rr_append_to_queue(&event, sizeof(rr_exception), EVENT_TYPE_EXCEPTION);
}

/* =================== */

static rr_exception* new_rr_exception(int vector, int error_code, unsigned long cr2)
{
    rr_exception *excp_log;

    excp_log = kmalloc(sizeof(rr_exception), GFP_KERNEL);

    excp_log->exception_index = vector;
    excp_log->error_code = error_code;

    return excp_log;
}

__maybe_unused static void rr_print_regs(struct kvm_regs *regs)
{
    printk(KERN_INFO "[RR Print Regs]\n"
           "rax=%llu, rbx=%llu, rcx=%llu, rdx=%llu,"
           "rsi=%llu, rdi=%llu, rsp=%llu, rbp=%llu"
           "rip=%llu",
           regs->rax, regs->rbx, regs->rcx, regs->rdx,
           regs->rsi, regs->rdi, regs->rsp, regs->rbp,
           regs->rip);
}

__maybe_unused static void rr_record_regs(struct kvm_regs *dest_regs, struct kvm_regs *src_regs)
{
    dest_regs->rax = src_regs->rax;
    dest_regs->rbx = src_regs->rbx;
    dest_regs->rcx = src_regs->rcx;
    dest_regs->rdx = src_regs->rdx;
    
    dest_regs->rsi = src_regs->rsi;
    dest_regs->rdi = src_regs->rdi;
    dest_regs->rsp = src_regs->rsp;
    dest_regs->rbp = src_regs->rbp;

    dest_regs->r8 = src_regs->r8;
    dest_regs->r9 = src_regs->r9;
    dest_regs->r10 = src_regs->r10;
    dest_regs->r11 = src_regs->r11;

    dest_regs->r12 = src_regs->r12;
    dest_regs->r13 = src_regs->r13;
    dest_regs->r14 = src_regs->r14;
    dest_regs->r15 = src_regs->r15;

    // dest_regs->rip = src_regs->rip;
    // dest_regs->rflags = src_regs->rflags;
}

int rr_get_event_list_length(void)
{
    rr_event_log *event = rr_event_log_head;
    int len = 0;

    while (event != NULL) {
        len++;
        event = event->next;
    }

    return len;
}

int rr_get_mem_log_list_length(void)
{
    rr_mem_access_log *log;
    int len = 0;

    if (rr_mem_log_head == NULL) {
        return 0;
    }

    log = rr_mem_log_head;
    while (log != NULL) {
        len++;
        log = log->next;
    }

    return len;
}

void rr_copy_to_event_list(struct rr_event_list_t *event_list, int len)
{
    rr_event_log *event = rr_event_log_head;
    event_list->length = 0;

    while (event != NULL) {
        
        event = event->next;
    }
}

rr_event_log rr_get_next_event(void)
{
    rr_event_log *event = kmalloc(sizeof(struct rr_event_log_t), GFP_KERNEL);

    if (rr_event_cur == NULL) {
        return *event;
    }

    memcpy(event, rr_event_cur, sizeof(struct rr_event_log_t));

    rr_event_cur = rr_event_cur->next;

    return *event;
}

rr_mem_access_log rr_get_next_mem_log(void)
{
    rr_mem_access_log *log = kmalloc(sizeof(struct rr_mem_access_log_t), GFP_KERNEL);

    if (rr_mem_log_cur == NULL) {
        return *log;
    }

    memcpy(log, rr_mem_log_cur, sizeof(struct rr_mem_access_log_t));

    rr_mem_log_cur = rr_mem_log_cur->next;

    return *log;
}

static int rr_post_handle_event(struct kvm_vcpu *vcpu, rr_event_log *event)
{
    unsigned long cnt = kvm_get_inst_cnt(vcpu) - vcpu->rr_start_point;

    if (rr_event_cur != NULL && cnt == rr_event_cur->inst_cnt) {
        return 0;
    }

    event->inst_cnt = cnt;

    return 1;
}

static void rr_insert_event_log(rr_event_log *event)
{
    spin_lock(&queue_lock);
    if (rr_event_log_tail == NULL) {
        rr_event_log_head = event;
        rr_event_log_tail = event;
    } else {
        rr_event_log_tail->next = event;
        rr_event_log_tail = rr_event_log_tail->next;
    }

    rr_event_log_tail->next = NULL;

    spin_unlock(&queue_lock);
}

// Deprecated: old way of recording syscall
static void handle_event_syscall(struct kvm_vcpu *vcpu, void *opaque)
{
    struct kvm_regs *regs;
    rr_event_log *event_log;
    rr_syscall *syscall_log;
    u64 gsbase, kernel_gsbase;
    // struct kvm_segment *seg;

    regs = kmalloc(sizeof(struct kvm_regs), GFP_KERNEL);
    event_log = kmalloc(sizeof(rr_event_log), GFP_KERNEL);
    syscall_log = kmalloc(sizeof(rr_syscall), GFP_KERNEL);
    // seg = kmalloc(sizeof(struct kvm_segment), GFP_KERNEL);

    rr_get_regs(vcpu, regs);

    syscall_log->cr3 = kvm_read_cr3(vcpu);

    // kvm_get_segment(vcpu, seg, VCPU_SREG_GS);

    kvm_get_msr(vcpu, MSR_GS_BASE, &gsbase);
    kvm_get_msr(vcpu, MSR_KERNEL_GS_BASE, &kernel_gsbase);

    syscall_log->regs = *regs;
    syscall_log->msr_gsbase = gsbase;
    syscall_log->kernel_gsbase = kernel_gsbase;

    event_log->event.syscall = *syscall_log;
    event_log->type = EVENT_TYPE_SYSCALL;
    event_log->next = NULL;

    // printk(KERN_INFO "sycall: gsbase=0x%lx, gsbase_kernel=0x%lx\n",
    //        syscall_log->msr_gsbase , syscall_log->kernel_gsbase);

    if (rr_post_handle_event(vcpu, event_log)) {
        rr_insert_event_log(event_log);
    }
    
    rr_mem_log_cur = rr_mem_log_head;
}

static void handle_event_interrupt(struct kvm_vcpu *vcpu, void *opaque)
{

    struct kvm_regs *regs;
    rr_event_log *event_log;
    unsigned long rip;
    unsigned int *int_vector = (unsigned int *)opaque;

    WARN_ON(is_guest_mode(vcpu));

    event_log = kmalloc(sizeof(rr_event_log), GFP_KERNEL);

    event_log->id = vcpu->vcpu_id;
    event_log->event.interrupt.vector = *int_vector;
    event_log->event.interrupt.from = 3;
    event_log->type = EVENT_TYPE_INTERRUPT;
    event_log->next = NULL;

    event_log->rip = kvm_arch_vcpu_get_ip(vcpu);

    event_log->inst_cnt = kvm_get_inst_cnt(vcpu);

    rr_get_regs(vcpu, &event_log->event.interrupt.regs);

    rr_insert_event_log(event_log);
}

// Deprecated: old way of recording cfu
static void handle_event_cfu(struct kvm_vcpu *vcpu, void *opaque)
{

    struct kvm_regs *regs;
    struct kvm_sregs *sregs;
    rr_event_log *event_log;
    void *val;
    int ret;
    struct x86_emulate_ctxt *emulate_ctxt;
    rr_cfu *cfu_log;
    int i;
    unsigned long long dest_addr, src_addr;
    unsigned long *cfu_ip = (unsigned long *)opaque;
    unsigned long len;
    bool do_read_mem = false;
    int j;
    __maybe_unused u8 dest_data[4096];

    cfu_log = kmalloc(sizeof(rr_cfu), GFP_KERNEL);

    regs = kmalloc(sizeof(struct kvm_regs), GFP_KERNEL);
    sregs = kmalloc(sizeof(struct kvm_sregs), GFP_KERNEL);
    event_log = kmalloc(sizeof(rr_event_log), GFP_KERNEL);

    event_log->type = EVENT_TYPE_CFU;

    rr_get_regs(vcpu, regs);
    rr_get_sregs(vcpu, sregs);

    emulate_ctxt = vcpu->arch.emulate_ctxt;

    if (*cfu_ip == copy_from_iter_addr) {
        // === Kernel Version 1 ===
        // len = regs->r14;
        // dest_addr = regs->rdi - len;
        // src_addr = regs->rsi - len;
        // === End ===

        // === Kernel Version 2 ===
        len = regs->rdx;
        dest_addr = regs->rdi - len;
        src_addr = regs->rsi - len;
        // === End ===

        do_read_mem = true;
    } else if (*cfu_ip == copy_from_user_addr) {
        // === Kernel Version 1 ===
        // len = regs->rbx;
        // src_addr = regs->rsi - len;
        // dest_addr = regs->rdi - len;
        // === End ===

        // === Kernel Version 1 ===
        len = regs->rbp;
        src_addr = regs->rsi - len;
        dest_addr = regs->rdi - len;
        // === End ===

        do_read_mem = true;
    } else if (*cfu_ip == copy_page_from_iter_addr) {
        len = regs->rbx;
        src_addr = regs->rsi - len;
        dest_addr = regs->rdi - len;
        do_read_mem = true;
    } else if (*cfu_ip == strncpy_addr) {
        // === Kernel version 1 ===
        // len = regs->rax;
        // src_addr = regs->r8;
        // dest_addr = regs->rdi;
        // === End ===

        // === Kernel version 2 ===
        // len = regs->rax;
        // src_addr = regs->rbp;
        // dest_addr = regs->r12;
        // === End ===

        // === Kernel version 3 ===
        len = regs->rax;
        src_addr = regs->rdi;
        dest_addr = regs->r8;
        do_read_mem = true;
    } else if (*cfu_ip == get_user_addr) {
       cfu_log->rdx = regs->rdx;
       cfu_log->src_addr = 0;
       cfu_log->dest_addr = 0;
    //    printk(KERN_INFO "get user log: %lx\n", cfu_log->rdx);
    } else if (*cfu_ip == strnlen_user_addr) {
        cfu_log->len = regs->rax;
        // printk(KERN_INFO "strnlen_user_addr happened: %d\n", cfu_log->len);
    } else if (*cfu_ip == uaccess_begin) {
        cfu_log->src_addr = regs->rax;
        cfu_log->len = sregs->cs.base;
        printk(KERN_INFO "Read from src=0x%lx, dest=0x%lx, len=%lu\n", cfu_log->src_addr, cfu_log->dest_addr, cfu_log->len);
    }

    if (do_read_mem) {
        cfu_log->src_addr = src_addr;
        cfu_log->dest_addr = dest_addr;
        cfu_log->len = len;

        if (cfu_log->len > 4096) {
            printk(KERN_WARNING "Oversized: 0x%lx, %lu, addr=0x%lx\n", dest_addr, cfu_log->len, regs->rip);
        } else {
            // printk(KERN_INFO "Read from src=0x%lx, dest=0x%lx, len=%lu\n", cfu_log->src_addr, cfu_log->dest_addr, cfu_log->len);

            ret = rr_kvm_read_guest_virt(vcpu,
                                      cfu_log->src_addr, cfu_log->data, cfu_log->len,
                                      &emulate_ctxt->exception, PFERR_USER_MASK);

            // ret = rr_kvm_read_guest_virt(vcpu,
            //                           cfu_log->dest_addr, dest_data, cfu_log->len,
            //                           &emulate_ctxt->exception, 0);

            if (ret != X86EMUL_CONTINUE) {
                printk(KERN_WARNING "Failed to read addr 0x%lx, ret %d\n",
                    cfu_log->src_addr, ret);
            }
        }

        // if (strcmp(cfu_log->data, dest_data) == 0) {
        //     printk(KERN_WARNING "read data matched\n");
        // }

        // printk(KERN_INFO "CFU: read from addr=0x%lx, len=%d, ret=%d, rip=0x%lx\n",
        //        cfu_log->dest_addr, len, ret, regs->rip);

        // if (ret != X86EMUL_PROPAGATE_FAULT) {
        //     printk(KERN_WARNING "Failed to read addr 0x%lx, ret %d\n",
        //            cfu_log->dest_addr, ret);
        // }
    }

    event_log->event.cfu = *cfu_log;

    event_log->rip = kvm_arch_vcpu_get_ip(vcpu);

    if (rr_post_handle_event(vcpu, event_log))
        rr_insert_event_log(event_log);

    return;
}

static void handle_event_random_generator(struct kvm_vcpu *vcpu, void *opaque)
{
    struct kvm_regs *regs;
    rr_event_log *event_log;
    rr_random *rand_log;
    struct x86_emulate_ctxt *emulate_ctxt;
    int ret = 0;
    unsigned long rip = kvm_arch_vcpu_get_ip(vcpu);

    if (rip == random_bytes_addr_start) {
        if (random_cur != NULL) {
            printk(KERN_WARNING "Intercept random in middle of a random");
        }

        regs = kzalloc(sizeof(struct kvm_regs), GFP_KERNEL_ACCOUNT);
        rand_log = kmalloc(sizeof(rr_random), GFP_KERNEL);

        rr_get_regs(vcpu, regs);

        rand_log->len = regs->rsi;
        rand_log->buf = regs->rdi;

        random_cur = rand_log;
    } else {
        rand_log = random_cur;

        if (random_cur == NULL) {
            return;
        }
        
        printk(KERN_INFO "Random read from 0x%lx, len=%d\n", rand_log->buf, rand_log->len);

        event_log = kmalloc(sizeof(rr_event_log), GFP_KERNEL);
        
        event_log->type = EVENT_TYPE_RANDOM;

        emulate_ctxt = vcpu->arch.emulate_ctxt;

        ret = emulate_ctxt->ops->read_emulated(vcpu->arch.emulate_ctxt,
                                            rand_log->buf, rand_log->data, rand_log->len,
                                            &emulate_ctxt->exception);
        if (ret != X86EMUL_PROPAGATE_FAULT) {
            printk(KERN_WARNING "Failed to read addr 0x%lx, ret %d\n",
                rand_log->buf, ret);
        }

        memcpy(&event_log->event.rand, rand_log, sizeof(rr_random));
        event_log->rip = rip;

        random_cur = NULL;

        if (rr_post_handle_event(vcpu, event_log))
            rr_insert_event_log(event_log);
    }
}

static void handle_event_io_in(struct kvm_vcpu *vcpu, void *opaque)
{
    rr_event_log *event_log;
    unsigned long *io_val = (unsigned long *)opaque;
    rr_io_input *io_input;
    
    event_log = kmalloc(sizeof(rr_event_log), GFP_KERNEL);
    io_input = kmalloc(sizeof(rr_io_input), GFP_KERNEL);

    // printk(KERN_INFO "Recording IO IN: %lx\n", *io_val);

    io_input->value = *io_val;

    event_log->type = EVENT_TYPE_IO_IN;
    event_log->rip = kvm_arch_vcpu_get_ip(vcpu);
    event_log->event.io_input = *io_input;
    event_log->next = NULL;

    if (rr_post_handle_event(vcpu, event_log))
        rr_insert_event_log(event_log);

    // printk(KERN_WARNING "IO event\n");

    return;
}

void handle_hypercall_random(struct kvm_vcpu *vcpu,
                             unsigned long buf,
                             unsigned long len)
{
    rr_event_log_guest event_log = {
        .type = EVENT_TYPE_RANDOM
    };
    struct x86_emulate_ctxt *emulate_ctxt;
    int ret = 0;

    event_log.event.rand.buf = buf;
    event_log.event.rand.len = len;

    event_log.inst_cnt = kvm_get_inst_cnt(vcpu);

    emulate_ctxt = vcpu->arch.emulate_ctxt;

    ret = emulate_ctxt->ops->read_emulated(vcpu->arch.emulate_ctxt,
                                           event_log.event.rand.buf,
                                           event_log.event.rand.data,
                                           event_log.event.rand.len,
                                           &emulate_ctxt->exception);
    if (ret != X86EMUL_CONTINUE) {
        printk(KERN_WARNING "Failed to read addr 0x%lx, ret %d\n",
               event_log.event.rand.buf, ret);
    }

    rr_append_to_queue(&event_log, sizeof(rr_random), EVENT_TYPE_RANDOM);
}

void handle_hypercall_cfu(struct kvm_vcpu *vcpu,
                          unsigned long src,
                          unsigned long dest,
                          unsigned long len)
{
    rr_event_log *event_log;
    struct x86_emulate_ctxt *emulate_ctxt;
    rr_cfu *cfu_log;
    int ret;

    cfu_log = kmalloc(sizeof(rr_cfu), GFP_KERNEL);

    event_log = kmalloc(sizeof(rr_event_log), GFP_KERNEL);

    cfu_log->src_addr = src;
    cfu_log->dest_addr = dest;
    cfu_log->len = len;

    emulate_ctxt = vcpu->arch.emulate_ctxt;
    event_log->type = EVENT_TYPE_CFU;

    if (cfu_log->len > 4096) {
        printk(KERN_WARNING "Oversized: 0x%lx, %lu\n", dest, len);
    } else {
        // printk(KERN_INFO "Read from src=0x%lx, dest=0x%lx, len=%lu\n", cfu_log->src_addr, cfu_log->dest_addr, cfu_log->len);
        ret = rr_kvm_read_guest_virt(vcpu,
                                    cfu_log->src_addr, cfu_log->data, cfu_log->len,
                                    &emulate_ctxt->exception, PFERR_USER_MASK);
        if (ret != X86EMUL_CONTINUE) {
            printk(KERN_WARNING "Failed to read addr 0x%lx, ret %d\n",
                cfu_log->src_addr, ret);
        }
    }

    event_log->event.cfu = *cfu_log;

    if (rr_post_handle_event(vcpu, event_log))
        rr_insert_event_log(event_log);
}

void handle_hypercall_getuser(struct kvm_vcpu *vcpu,
                              unsigned long val)
{
    rr_event_log *event_log;
    rr_gfu *gfu_log;

    gfu_log = kmalloc(sizeof(rr_gfu), GFP_KERNEL);

    event_log = kmalloc(sizeof(rr_event_log), GFP_KERNEL);

    gfu_log->val = val;
    event_log->type = EVENT_TYPE_GFU;
    event_log->event.gfu = *gfu_log;

    if (rr_post_handle_event(vcpu, event_log))
        rr_insert_event_log(event_log);
}

static void handle_event_rdtsc(struct kvm_vcpu *vcpu, void *opaque)
{
    rr_event_log *event_log;
    unsigned long *tsc_val = (unsigned long *)opaque;
    rr_io_input *io_input;
    
    event_log = kmalloc(sizeof(rr_event_log), GFP_KERNEL);
    io_input = kmalloc(sizeof(rr_io_input), GFP_KERNEL);

    io_input->value = *tsc_val;

    event_log->type = EVENT_TYPE_RDTSC;
    event_log->rip = kvm_arch_vcpu_get_ip(vcpu);
    event_log->event.io_input = *io_input;
    event_log->next = NULL;

    if (rr_post_handle_event(vcpu, event_log))
        rr_insert_event_log(event_log);

    return;
}

static void handle_event_dma_done_shm(struct kvm_vcpu *vcpu, void *opaque)
{
    rr_dma_done event = {
        .id = vcpu->vcpu_id,
        // When vcpu is in user mode, inst_cnt might be 0.
        .inst_cnt = kvm_get_inst_cnt(vcpu),
    };

    WARN_ON(is_guest_mode(vcpu));

    rr_append_to_queue(&event, sizeof(rr_dma_done), EVENT_TYPE_DMA_DONE);
}

static void report_record_stat(int cpu_id)
{
    rr_event_log *event = rr_event_log_head;
    int event_int_num = 0;
    int event_syscall_num = 0;
    int event_pf_excep = 0;
    int event_io_in = 0;
    int event_cfu = 0;
    int event_random = 0;
    int event_dma_done = 0;
    int event_gfu = 0;

    rr_event_guest_queue_header header;

    if (__copy_from_user(&header, (void __user *)ivshmem_base_addr, sizeof(rr_event_guest_queue_header))) {
        printk(KERN_WARNING "Failed to read from user memory\n");
    }

    printk(KERN_WARNING "=== Report recorded events ===\n");
    while (event != NULL) {
        if (event->type == EVENT_TYPE_INTERRUPT) {
            event_int_num++;
        //     // if (event->event.interrupt.lapic.vector == 33)
        //     printk(KERN_INFO "RR Interrupt: vecter=%lu RIP=%llx, inst_cnt=%lu",
        //            event->event.interrupt.vector, event->rip, event->inst_cnt);
        }

        if (event->type == EVENT_TYPE_SYSCALL) {
            event_syscall_num++;
            // printk(KERN_INFO "RR Record: Syscall Num=%lu", event->event.syscall.regs.rax);
        }

        if (event->type == EVENT_TYPE_EXCEPTION) {
            // printk(KERN_WARNING "except vector=%d error code=%d, addr=%x",
            //        event->event.exception.exception_index,
            //        event->event.exception.error_code,
            //        event->event.exception.cr2);
            event_pf_excep++;
        }

        if (event->type == EVENT_TYPE_IO_IN) {
            event_io_in++;
            // printk(KERN_INFO "RR Record: IO IN=%lx", event->event.io_input.value);
        }

        if (event->type == EVENT_TYPE_RDTSC) {
            event_io_in++;
            // printk(KERN_INFO "RR Record: IO IN=%lx", event->event.io_input.value);
        }

        if (event->type == EVENT_TYPE_CFU) {
            event_cfu++;
            // printk(KERN_INFO "RR Record: CFU rip=0x%lx, addr=0x%lx, inst_cnt=%lu", event->rip, event->event.cfu.dest_addr, event->inst_cnt);
        }

        if (event->type == EVENT_TYPE_GFU) {
            event_gfu++;
            // printk(KERN_INFO "RR Record: DMA Done");
        }

        if (event->type == EVENT_TYPE_RANDOM) {
            event_random++;
            // printk(KERN_INFO "RR Record: Random rip=0x%lx, buf=0x%lx, len=%lu, inst_cnt=%lu",
            //         event->rip, event->event.rand.buf, event->event.rand.len, event->inst_cnt);
        }

        if (event->type == EVENT_TYPE_DMA_DONE) {
            event_dma_done++;
            // printk(KERN_INFO "RR Record: DMA Done");
        }

        total_event_cnt++;

        event = event->next;

    }

    printk(KERN_INFO "CPU %d: syscall=%d, interrupt=%d, pf=%d,"\
           "io_in=%d, cfu=%d, dma_done=%d, gfu=%d\n",
           cpu_id, event_syscall_num, event_int_num, event_pf_excep,
           event_io_in, event_cfu, event_dma_done, event_gfu);
}

static void rr_vcpu_set_in_record(struct kvm_vcpu *vcpu, int record, struct rr_record_data data)
{
    if (!record) {
        report_record_stat(vcpu->vcpu_id);

        kvm_make_request(KVM_REQ_END_RECORD, vcpu);

        vcpu->int_injected = 0;
    } else {
        printk(KERN_INFO "RR initialized\n");

        kvm_make_request(KVM_REQ_START_RECORD, vcpu);
        vcpu->int_injected = 0;

        vcpu->enable_trace = data.enable_trace;
        vcpu->trace_interval = data.trace_interval;
        vcpu->executed_inst = 0;
        vcpu->checkpoint = false;
        vcpu->overflowed = false;
        if (vcpu->enable_trace)
            printk(KERN_INFO "RR trace enabled, interval is %lu\n", vcpu->trace_interval);
    }

}

void rr_set_in_record(struct kvm *kvm, int record, struct rr_record_data data)
{
    unsigned long i;
    struct kvm_vcpu *vcpu;

    in_record = record;
    total_event_cnt = 0;

    if (in_record) {
        clear_events();
    }

    kvm_for_each_vcpu(i, vcpu, kvm) {
        rr_vcpu_set_in_record(vcpu, record, data);
    }

    if (!record) {
        rr_event_cur = rr_event_log_head;
        rr_mem_log_cur = rr_mem_log_head;
    }

    rr_clear_mem_log();
}

void clear_events(void)
{
    if (rr_event_log_head != NULL) {
        rr_event_log *pre_event = rr_event_log_head;
        rr_event_log *event;

        while (pre_event != NULL) {
            event = pre_event->next;
            kfree(pre_event);
            pre_event = event;
        }
    }

    rr_event_log_head = NULL;
    rr_event_log_tail = NULL;
    printk(KERN_INFO "Records cleard\n");
}

void rr_clear_mem_log(void)
{
    if (rr_mem_log_head != NULL) {
        rr_mem_log_head = NULL;
        rr_mem_log_tail = NULL;
        rr_mem_log_cur = NULL;
    }
}

void rr_set_in_replay(struct kvm_vcpu *vcpu, int replay)
{
    in_replay = replay;
}

int rr_in_replay(void)
{
    return in_replay;
}

int rr_in_record(void)
{
    return in_record;
}
EXPORT_SYMBOL_GPL(rr_in_record);

lapic_log* create_lapic_log(int delivery_mode, int vector, int trig_mode)
{
    lapic_log *log = kmalloc(sizeof(lapic_log), GFP_KERNEL);

    log->delivery_mode = delivery_mode;
    log->vector = vector;
    log->trig_mode = trig_mode;
    
    return log;
}

static int get_lock_owner(void) {
    int cpu_id;

    if (get_user(cpu_id, (int __user *)(ivshmem_base_addr + sizeof(rr_event_guest_queue_header)))) {
        printk(KERN_WARNING "Failed to read owner id\n");
    }

    return cpu_id;
}

void rr_sync_inst_cnt(struct kvm_vcpu *vcpu)
{
    rr_event_log_guest event = {};
    event.inst_cnt = kvm_get_inst_cnt(vcpu);
    event.rip = kvm_get_linear_rip(vcpu);
    event.id = vcpu->vcpu_id;

    rr_append_to_queue(&event, sizeof(rr_event_log_guest), EVENT_TYPE_INST_SYNC);
}

int rr_queue_full(void)
{
    rr_event_guest_queue_header header;

    if (__copy_from_user(&header, (void __user *)ivshmem_base_addr, sizeof(rr_event_guest_queue_header))) {
        printk(KERN_WARNING "Failed to read from user memory\n");
    }

    if (header.current_byte + \
		sizeof(rr_event_entry_header) + \
		sizeof(rr_interrupt) >= header.total_size) {
        return 1;
    }

    return 0;
}

void rr_record_event(struct kvm_vcpu *vcpu, int event_type, void *opaque)
{
    switch (event_type)
    {
    case EVENT_TYPE_INTERRUPT:
        bool hypervisor_record = false;
        unsigned long addr = kvm_get_linear_rip(vcpu);

        if (atomic_read(&vcpu->kvm->online_vcpus) > 1) {
            if (static_call(kvm_x86_get_cpl)(vcpu) > 0 || get_lock_owner() != vcpu->vcpu_id) {
                hypervisor_record = true;
            }
        }

        if (hypervisor_record) {
            handle_event_interrupt(vcpu, opaque);
        } else {
            handle_event_interrupt_shm(vcpu, opaque);
        }
        break;
    case EVENT_TYPE_EXCEPTION:
        handle_event_exception_shm(vcpu, opaque);
        break;
    case EVENT_TYPE_SYSCALL:
        handle_event_syscall(vcpu, opaque);
        break;
    case EVENT_TYPE_IO_IN:
        // handle_event_io_in(vcpu, opaque);
        handle_event_io_in_shm(vcpu, opaque);
        break;
    case EVENT_TYPE_CFU:
        handle_event_cfu(vcpu, opaque);
        break;
    case EVENT_TYPE_RANDOM:
        handle_event_random_generator(vcpu, opaque);
        break;
    case EVENT_TYPE_RDTSC:
        // handle_event_rdtsc(vcpu, opaque);
        handle_event_rdtsc_shm(vcpu, opaque);
        break;
    case EVENT_TYPE_DMA_DONE:
        handle_event_dma_done_shm(vcpu, opaque);
        break;
    default:
        break;
    }
}
EXPORT_SYMBOL_GPL(rr_record_event);

void rr_trace_memory_write(struct kvm_vcpu *vcpu, gpa_t gpa)
{
    unsigned long rip;
    rr_mem_access_log *log;
    
    rip = kvm_get_linear_rip(vcpu);
    log = kmalloc(sizeof(rr_mem_access_log), GFP_KERNEL);

    log->gpa = gpa;
    log->rip = rip;
    log->inst_cnt = kvm_get_inst_cnt(vcpu) - vcpu->rr_start_point;

    // printk(KERN_INFO "RR record mem access: %lx\n", log->gpa);

    log->next = NULL;

    if (rr_mem_log_tail == NULL) {
        rr_mem_log_head = log;
        rr_mem_log_tail = log;
    } else {
        rr_mem_log_tail->next = log;
        rr_mem_log_tail = rr_mem_log_tail->next;
    }
}

int rr_handle_breakpoint(struct kvm_vcpu *vcpu)
{
    unsigned long addr;

    if (!rr_in_record()) {
        return 0;
    }

    addr = kvm_get_linear_rip(vcpu);

    // printk(KERN_INFO "breakpoint addr 0x%lx\n", addr);

    switch(addr) {
        case syscall_addr:
            rr_record_event(vcpu, EVENT_TYPE_SYSCALL, NULL);
            break;
        case pf_excep_addr:
            rr_record_event(vcpu, EVENT_TYPE_EXCEPTION, new_rr_exception(PF_VECTOR, 0, 0));
            break;
        case copy_from_iter_addr:
        case copy_from_user_addr:
        case strncpy_addr:
        case get_user_addr:
        case strnlen_user_addr:
        case copy_page_from_iter_addr:
            rr_record_event(vcpu, EVENT_TYPE_CFU, &addr);
            break;
        case random_bytes_addr_start:
        case random_bytes_addr_end:
            rr_record_event(vcpu, EVENT_TYPE_RANDOM, NULL);
        default:
            break;
    }

    return 0;
}

void rr_register_ivshmem(unsigned long addr)
{
    rr_event_guest_queue_header header;

    ivshmem_base_addr = addr;

    if (__copy_from_user(&header, (void __user *)ivshmem_base_addr, sizeof(rr_event_guest_queue_header))) {
        printk(KERN_WARNING "Failed to read from user memory\n");
    }

    printk(KERN_WARNING "Header info: total_pos=%u, cur_pos=%u, rr_endabled=%u\n",
           header.total_pos, header.current_pos, header.rr_enabled);
}

EXPORT_SYMBOL_GPL(rr_handle_breakpoint);
