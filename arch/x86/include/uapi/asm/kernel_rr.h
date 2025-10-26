#ifndef __KERNEL_RR_H__
#define __KERNEL_RR_H__

#include <asm/kvm.h>

#define EVENT_TYPE_INTERRUPT 0
#define EVENT_TYPE_EXCEPTION 1
#define EVENT_TYPE_SYSCALL   2
#define EVENT_TYPE_IO_IN     3
#define EVENT_TYPE_CFU       4
#define EVENT_TYPE_RANDOM    5
#define EVENT_TYPE_RDTSC     6
#define EVENT_TYPE_DMA_DONE  7
#define EVENT_TYPE_GFU       8
#define EVENT_TYPE_STRNLEN   9
#define EVENT_TYPE_RDSEED    10
#define EVENT_TYPE_RELEASE   11
#define EVENT_TYPE_INST_SYNC 12

#define KRR_COUNTER_BIT 1ULL << 3

#define CFU_BUFFER_SIZE     4096

#define INJ_DMA_NET_BUF_BIT 1

enum REGS {
    ZERO,
    RR_RAX,
    RR_RCX,
	RR_RDX,
	RR_RBX,
	RR_RSP,
	RR_RBP,
	RR_RSI,
	RR_RDI,
	RR_R8,
	RR_R9,
	RR_R10,
	RR_R11,
	RR_R12,
	RR_R13,
	RR_R14,
	RR_R15,
	RR_RIP,
	RR_NR_VCPU_REGS,
};

typedef struct {
    int delivery_mode;
	int vector;
    int trig_mode;
} lapic_log;

typedef struct {
    int id;
    unsigned long value;
    unsigned long inst_cnt;
    unsigned long rip;
} rr_io_input;

typedef struct {
    int id;
    int vector;
    unsigned long ecx;
    int from;
    unsigned long spin_count;
    unsigned long inst_cnt;
    unsigned long rip;
    struct kvm_regs regs;
} rr_interrupt;

typedef struct {
    int id;
    unsigned long val;
    unsigned long ptr;
    int size;
} rr_gfu;

typedef struct {
    int id;
    unsigned long src_addr;
    unsigned long dest_addr;
    unsigned long len;
    unsigned long rdx;
    unsigned char *data;
} rr_cfu;

typedef struct {
    int id;
    int exception_index;
    int error_code;
    unsigned long cr2, cr3;
    struct kvm_regs regs;
    unsigned long spin_count;
    unsigned long inst_cnt;
} rr_exception;

typedef struct {
    int id;
    struct kvm_regs regs;
    unsigned long kernel_gsbase, msr_gsbase, cr3;
    unsigned long spin_count;
} rr_syscall;

typedef struct {
    int id;
    unsigned long buf;
    unsigned long len;
    unsigned char data[1024];
} rr_random;

typedef struct rr_dma_done_t {
    int id;
    unsigned long inst_cnt;
} rr_dma_done;

typedef struct rr_event_log_t{
    int type;
    int id;
    union {
        rr_interrupt interrupt;
        rr_exception exception;
        rr_syscall  syscall;
        rr_io_input io_input;
        rr_cfu cfu;
        rr_random rand;
        rr_gfu gfu;
        rr_dma_done dma_done;
    } event;
    struct rr_event_log_t *next;
    unsigned long inst_cnt;
    unsigned long rip;
    int user_mode;
} rr_event_log;

typedef struct rr_event_log_guest_t {
    int type;
    int id;
    union {
        rr_interrupt interrupt;
        rr_exception exception;
        rr_syscall  syscall;
        rr_io_input io_input;
        rr_cfu cfu;
        rr_random rand;
        rr_gfu gfu;
    } event;
    unsigned long inst_cnt;
    unsigned long rip;
} rr_event_log_guest;


typedef struct rr_event_guest_queue_header_t {
    unsigned int current_pos;
    unsigned int total_pos;
    unsigned int header_size;
    unsigned int entry_size;
    unsigned int rr_enabled;
    unsigned long current_byte;
    unsigned long total_size;
    unsigned long rotated_bytes;
} rr_event_guest_queue_header;

typedef struct rr_event_entry_header_t {
    int type;
} rr_event_entry_header;


typedef struct rr_mem_access_log_t {
    unsigned long gpa;
    unsigned long rip;
    unsigned long inst_cnt;
    struct rr_mem_access_log_t *next;
} rr_mem_access_log;

typedef struct rr_event_list_t {
    rr_event_log *item;
    int length;
} rr_event_list;

struct rr_event_info {
    int event_number;
};

struct rr_record_data {
    unsigned long shm_base_addr;
    int enable_trace;
    unsigned long trace_interval;
};

struct rr_exception_detail {
    unsigned vector;
    unsigned long dr6;
};

#define ROUND_INSTRUCTION_NUMBER 50000

/* === Return code === */
#define RR_HIT_BREAKPOINT -199
#define RR_HANDLE_EVENT_FAILED -205
#define RR_RECORD_SETUP_FAILED -206

#endif
