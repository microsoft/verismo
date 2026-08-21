# 4. Verified task scheduler

*Status: planned.* No implementation yet.

The scheduler is listed separately from the components above because its
defining properties are *temporal*: they are about what eventually happens, not
about what never happens. None of the safety machinery used elsewhere in this
repository proves them, so the proof framework is an open decision rather than a
detail.

## 4.1 Liveness

Every runnable task eventually runs, and a task blocked on a resource eventually
becomes runnable once that resource is released.

This is only provable under an explicit fairness assumption about the
environment — that timer interrupts are eventually delivered, and that a task
holding a lock eventually releases it. Those assumptions belong in the trusted
base and should be stated as plainly as the machine model's `asm!` contracts.

Verus proves safety properties. Liveness needs reasoning over infinite
behaviours (TLA-style), so it is expected to be a separate layer with an
explicit interface to the safety proofs: the safety layer supplies the state
machine and its invariants, the temporal layer supplies fairness and derives
eventuality.

## 4.2 Fairness

No task is starved: bounded waiting under the chosen policy, and priority
inversion either impossible or bounded by an inheritance protocol.

Fairness is where the policy stops being an implementation detail. A bound has
to be stated in terms the policy defines (rounds, quanta, priority levels), so
the specification and the scheduling algorithm have to be designed together.

## 4.3 Concurrency

The run queue and per-CPU state stay correct under concurrent access: a task is
never on two run queues, never runs on two CPUs, and migration preserves both.
This is a safety property and is in reach of the same token/state-machine
approach used for the page table ([§3.3](page-table.md#33-concurrency-correctness)).

Context switching also has to preserve the machine model. A switched-to task
resumes with a register state satisfying `rust_abi_wf`
([§1.1](machine-model.md#11-register-state)) — in particular RFLAGS.DF clear —
and with the paging invariant
([§1.2](machine-model.md#12-paging-view-of-register-state)) re-established if
the switch changed `CR3`. Save/restore is therefore a register-token transfer,
not an opaque assembly routine, and is the point where the scheduler proof meets
the machine model.
