#include <linux/module.h> // Required for all kernel modules
#include <linux/kernel.h> // Required for kernel logging functions
#include <linux/proc_fs.h> // Required for /proc file system functions
#include <linux/slab.h> // Required for kernel logging functions

#include <asm/msr.h> // msr
#include <asm/io.h> // addr translation
#include <linux/seq_file.h>

#include <linux/kallsyms.h>
MODULE_LICENSE("GPL");
u64 kernel_start_addr;
u64 kernel_end_addr;
u64 start_addr;
u64 end_addr;

union snp_vmpl_request {
	struct {
		u64 values[3];
	};
	struct {
		u64 npages : 12;
		u64 gpn : 52;
		u64 op : 32;
		u64 cpu : 32;
		u64 other;
	};
};

enum VMPLCode {
	WakupAp = 0xfffffffe,
	SetPrivate = 0x1,
	SetShared = 0x2,
	Register = 0x3,
	ExtendPcr = 0x4,
	LockKernExe = 0x5,
	Attest = 0x6,
	Secret = 0x7,
	Encrypt = 0x8,
	Decrypt = 0x9,
};

struct LockReq {
	u64 start;
	u64 end;
};

#define VERISMO_ATTEST 0xfffffffdUL
#define VERISMO_OK 0x0UL
#define HVCALL_VTL_CALL (0x0011UL << 52UL)
#define GHCB_INFO_SPECIAL_HYPERCALL 0xf00UL

static u64 snp_send_vmpl_via_ghcb_msr(union snp_vmpl_request *req)
{
	u32 *low, *high;
	u64 msr_val;
	u64 oldghcb;
	msr_val = GHCB_INFO_SPECIAL_HYPERCALL | HVCALL_VTL_CALL;
	low = (u32 *)&msr_val;
	high = low + 1;
	rdmsrl_safe(MSR_AMD64_SEV_ES_GHCB, &oldghcb);
	wrmsrl(MSR_AMD64_SEV_ES_GHCB, msr_val);
	asm volatile("rep; vmmcall\n\r"
		     : "=b"(req->values[0]), "=c"(req->values[1]),
		       "=d"(req->values[2])
		     : "a"(0xfeeddead), "b"(req->values[0]),
		       "c"(req->values[1]), "d"(req->values[2]));
	wrmsrl(MSR_AMD64_SEV_ES_GHCB, oldghcb);
	return 0;
}

static int msg_len = 0;

DEFINE_PER_CPU(void *, cpu_msg);

#define msg this_cpu_read(cpu_msg)

static void *test_pages = 0;
static int buffer_len = 4096;

void verismo_request(union snp_vmpl_request *req, void *this_msg)
{
	struct LockReq *lock_req = NULL;
	unsigned long long start = 0, end = 0;
    	bool use_out_msg = false;
	req->values[2] = 0;
	switch (req->op) {
	case Attest: {
        use_out_msg = true;
		break;
	}
	case ExtendPcr: {
		break;
	}
	case Register: {
		req->values[0] = virt_to_phys(this_msg);
		break;
	}
	case LockKernExe: {
		kernel_start_addr =
			(u64)virt_to_phys((void *)0xffffffff90000000);
		kernel_end_addr = (u64)virt_to_phys((void *)0xffffffff90d2f624);
		req->values[0] = (u64)virt_to_phys(this_msg);
		lock_req = (struct LockReq *)this_msg;
		lock_req->start =
			(u64)virt_to_phys((void *)0xffffffff90000000) >> 12;
		lock_req->end = (u64)(virt_to_phys((void *)0xffffffff9080092a) +
				      0xfff) >>
				12;
		lock_req += 1;
		lock_req->start =
			(u64)virt_to_phys((void *)0xffffffff90cfd000) >> 12;
		lock_req->end = (u64)(virt_to_phys((void *)0xffffffff90d2f67a) +
				      0xfff) >>
				12;
		lock_req += 1;
		lock_req->start = (u64)(start_addr + 0xfff) >> 12;
		lock_req->end = (u64)(end_addr + 0xfff) >> 12;
		break;
	}
	default: {
		break;
	}
	}
	if ((req->op == SetPrivate) || (req->op == SetShared)) {
		printk("count = %lld\n", req->values[0]);
		req->values[0] = (u64)virt_to_phys(test_pages) +
				 ((req->values[0] % 16) << 12);
	} else if (req->op != WakupAp) {
		req->values[0] = (u64)virt_to_phys(this_msg);
	}

	printk("req %x %llx %llx %llx\n", req->op, req->values[0],
	       req->values[1], req->values[2]);
	start = rdtsc();
	if (req->op != WakupAp) {
		snp_send_vmpl_via_ghcb_msr(req);
	}
	end = rdtsc();
	printk("req->op = %x, time = %lld\n", req->op, end - start);
    if (use_out_msg)
	    print_hex_dump(KERN_INFO, "resp : ", DUMP_PREFIX_NONE, 128, 1, this_msg,
		       128, false);
}

// Function to be called when write to /proc/verismo
ssize_t verismo_write(struct file *f, const char __user *buf, size_t len,
		      loff_t *pos)
{
	char input_buffer[512];
	union snp_vmpl_request req;

	if (copy_from_user(input_buffer, buf, len)) {
		return -EFAULT;
	}
	msg_len = len;
	memset(&req, 0, sizeof(req));
	printk("%s", input_buffer);
	preempt_disable();
	local_irq_disable();
	memset(msg, 0, 4096);
	sscanf(input_buffer, "%lld %lld %s", &req.values[1], &req.values[0],
	       (char *)msg);
	verismo_request(&req, msg);
	local_irq_enable();
	preempt_enable();
	*pos = len;
	return len;
}

static int verismo_seq_show(struct seq_file *seq, void *offset)
{
	seq_write(seq, msg, buffer_len);
	return 0;
}

static int verismo_open(struct inode *inode, struct file *file)
{
	return single_open(file, verismo_seq_show, NULL);
}

// Structure for /proc/hello_world file
struct proc_dir_entry *verismo_proc_file;

// Structure for /proc/hello_world file
static const struct proc_ops verismo_fops = {
	.proc_write = verismo_write,
	.proc_read = seq_read,
	.proc_lseek = seq_lseek,
	.proc_release = single_release,
	.proc_open = verismo_open,
};

static const struct proc_ops verismo_count_fops = {
	.proc_write = verismo_write,
	.proc_read = seq_read,
	.proc_lseek = seq_lseek,
	.proc_release = single_release,
	.proc_open = verismo_open,
};

static void verismo_init_percpu(void *unused)
{
	this_cpu_write(cpu_msg, (void *)get_zeroed_page(GFP_KERNEL));
	union snp_vmpl_request req;
	memset((void *)&req, 0, sizeof(req));
	req.op = Register;
	verismo_request(&req, msg);
}

static void verismo_free_percpu(void *unused)
{
	if (msg) {
		kfree(msg);
		this_cpu_write(cpu_msg, 0);
	}
}
// Function to be called when the module is loaded
static int __init init_verismo(void)
{
	// Create the /proc/hello_world file
	const struct module *mod = THIS_MODULE;
	// Get the base address of the module
	start_addr = (u64)virt_to_phys(mod->core_layout.base);
	end_addr = (u64)virt_to_phys(mod->core_layout.base +
				     mod->core_layout.text_size);
	printk("kernel  [%llx: %llx]\n", kernel_start_addr, kernel_end_addr);
	printk("module  [%llx: %llx]\n", start_addr, end_addr);
	verismo_proc_file = proc_create("verismo", 0444, NULL, &verismo_fops);

	test_pages = (void *)__get_free_pages(GFP_KERNEL, 4);
	on_each_cpu(verismo_init_percpu, NULL, true);
	printk("an extra page = %llx", (u64)virt_to_phys(test_pages));
	if (!verismo_proc_file) {
		printk(KERN_ALERT
		       "Error: Could not initialize /proc/verismo\n");
		return -ENOMEM;
	}

	printk(KERN_INFO
	       "verismo[flush]! Usage: req.values[1] req.values[0](count for page) msg\n");
	return 0;
}

// Function to be called when the module is unloaded
static void __exit remove_verismo(void)
{
	// Remove the /proc/hello_world file
	on_each_cpu(verismo_free_percpu, NULL, true);

	if (test_pages) {
		kfree(test_pages);
		test_pages = NULL;
	}

	proc_remove(verismo_proc_file);

	printk(KERN_INFO "Goodbye, verismo module unloaded!\n");
}

module_init(init_verismo);
module_exit(remove_verismo);