---- MODULE BtrfsExtentBufferLockRefinement ----
(*
 * Model: Refinement mapping from Concrete to Abstract
 *
 * This module imports the concrete model and defines the refinement mapping
 * to the abstract model. We then assert that the concrete specification
 * implies the abstract specification.
 *)

EXTENDS BtrfsExtentBufferLockConcrete

\* Import the abstract model, substituting its variables with expressions
\* over the concrete model's variables.
\* The refinement mapping:
\* - eb_lock_state maps directly to eb_wlock (both store the owning thread ID)
\* - thread_held maps directly
\* - thread_target maps directly
\* - thread_pc: the concrete "Waiting" state (queued in wait queue) corresponds
\*   to the abstract "AcquireWrite" state (trying to acquire a lock)
AbstractPC(t) ==
    IF thread_pc[t] = "Waiting" THEN "AcquireWrite"
    ELSE thread_pc[t]

Abstract == INSTANCE BtrfsExtentBufferLock WITH
    eb_wlock      <- eb_lock_state,
    thread_held   <- thread_held,
    thread_pc     <- [t \in Threads |-> AbstractPC(t)],
    thread_target <- thread_target

\* The refinement property: The concrete Spec implies the abstract Spec.
Refinement == Abstract!FixedSpec

=============================================================================