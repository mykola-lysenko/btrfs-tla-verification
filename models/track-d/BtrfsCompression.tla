---------------------------- MODULE BtrfsCompression ----------------------------
(*
 * Model: Btrfs compression worker page eviction race
 *
 * Bug description:
 * When Btrfs writes compressed data, it allocates temporary pages to hold the
 * compressed output before submitting it to disk. These pages are attached to
 * a shrinker or managed in a way that makes them susceptible to memory pressure.
 * A race condition occurs if the system memory management (eviction) frees
 * one of these temporary compression pages while the async compression worker
 * is still using it to compress data or submit the bio. This results in a
 * Use-After-Free (UAF) or data corruption (writing garbage to disk).
 *
 * Sequence (buggy):
 * 1. Compression worker allocates a page (page_state = "Valid").
 * 2. Compression worker starts compressing data into the page.
 * 3. Memory pressure triggers eviction; the evictor frees the page
 *    (page_state = "Freed") because it wasn't properly pinned or locked.
 * 4. Compression worker finishes compression and submits the bio, reading
 *    from the freed page -> UAF / Data Corruption.
 *
 * Fix: The compression worker must properly pin/lock the page (e.g., taking
 * an extra reference count or locking the page) so that the evictor cannot
 * free it while it's in use.
 *
 * Variables:
 *   page_state: "Valid" | "Freed"
 *   worker_pc: "Init" | "Alloc" | "Compress" | "Submit" | "Done"
 *   evictor_pc: "Init" | "Evict" | "Done"
 *   page_refcount: 0 | 1 | 2
 *
 * Invariant: NoUAF (if worker_pc = "Submit", page_state must be "Valid")
 *)

EXTENDS Integers, TLC

VARIABLES
    page_state,
    worker_pc,
    evictor_pc,
    page_refcount

vars == <<page_state, worker_pc, evictor_pc, page_refcount>>

Init ==
    /\ page_state = "Freed"
    /\ worker_pc = "Init"
    /\ evictor_pc = "Init"
    /\ page_refcount = 0

(* ===========================================================================
 * BUGGY VARIANT: Compression worker doesn't pin the page properly
 * =========================================================================== *)

BuggyWorkerAlloc ==
    /\ worker_pc = "Init"
    /\ page_state' = "Valid"
    /\ page_refcount' = 1  \* Basic allocation refcount
    /\ worker_pc' = "Compress"
    /\ UNCHANGED <<evictor_pc>>

BuggyWorkerCompress ==
    /\ worker_pc = "Compress"
    /\ worker_pc' = "Submit"
    /\ UNCHANGED <<page_state, evictor_pc, page_refcount>>

BuggyWorkerSubmit ==
    /\ worker_pc = "Submit"
    \* BUG: Submits bio, accessing the page. If page_state is "Freed", this is UAF.
    /\ worker_pc' = "Done"
    /\ UNCHANGED <<page_state, evictor_pc, page_refcount>>

BuggyEvictorEvict ==
    /\ evictor_pc = "Init"
    /\ page_state = "Valid"
    \* BUG: Evictor steals the page if refcount is 1 (assumes it's reclaimable cache)
    /\ page_refcount = 1
    /\ page_state' = "Freed"
    /\ page_refcount' = 0
    /\ evictor_pc' = "Done"
    /\ UNCHANGED <<worker_pc>>

BuggyDone ==
    /\ worker_pc = "Done"
    /\ evictor_pc = "Done"
    /\ UNCHANGED vars

BuggyNext ==
    \/ BuggyWorkerAlloc
    \/ BuggyWorkerCompress
    \/ BuggyWorkerSubmit
    \/ BuggyEvictorEvict
    \/ BuggyDone

BuggyFairness ==
    /\ WF_vars(BuggyWorkerAlloc)
    /\ WF_vars(BuggyWorkerCompress)
    /\ WF_vars(BuggyWorkerSubmit)
    /\ WF_vars(BuggyEvictorEvict)

BuggySpec == Init /\ [][BuggyNext]_vars /\ BuggyFairness

(* ===========================================================================
 * FIXED VARIANT: Compression worker takes an extra refcount (pins the page)
 * =========================================================================== *)

FixedWorkerAlloc ==
    /\ worker_pc = "Init"
    /\ page_state' = "Valid"
    \* FIX: Worker allocates and immediately pins the page (refcount = 2)
    \* 1 for the cache, 1 for the active worker
    /\ page_refcount' = 2
    /\ worker_pc' = "Compress"
    /\ UNCHANGED <<evictor_pc>>

FixedWorkerCompress ==
    /\ worker_pc = "Compress"
    /\ worker_pc' = "Submit"
    /\ UNCHANGED <<page_state, evictor_pc, page_refcount>>

FixedWorkerSubmit ==
    /\ worker_pc = "Submit"
    /\ worker_pc' = "Done"
    \* Worker releases its pin after submission
    /\ page_refcount' = page_refcount - 1
    /\ UNCHANGED <<page_state, evictor_pc>>

FixedEvictorEvict ==
    /\ evictor_pc = "Init"
    /\ page_state = "Valid"
    \* FIX: Evictor can only reclaim if refcount is exactly 1 (not pinned)
    /\ page_refcount = 1
    /\ page_state' = "Freed"
    /\ page_refcount' = 0
    /\ evictor_pc' = "Done"
    /\ UNCHANGED <<worker_pc>>

\* Evictor can also just do nothing if it tries to evict and fails
FixedEvictorSkip ==
    /\ evictor_pc = "Init"
    /\ page_refcount > 1
    /\ evictor_pc' = "Done"
    /\ UNCHANGED <<page_state, worker_pc, page_refcount>>

FixedDone ==
    /\ worker_pc = "Done"
    /\ evictor_pc = "Done"
    /\ UNCHANGED vars

FixedNext ==
    \/ FixedWorkerAlloc
    \/ FixedWorkerCompress
    \/ FixedWorkerSubmit
    \/ FixedEvictorEvict
    \/ FixedEvictorSkip
    \/ FixedDone

FixedFairness ==
    /\ WF_vars(FixedWorkerAlloc)
    /\ WF_vars(FixedWorkerCompress)
    /\ WF_vars(FixedWorkerSubmit)
    /\ WF_vars(FixedEvictorEvict)
    /\ WF_vars(FixedEvictorSkip)

FixedSpec == Init /\ [][FixedNext]_vars /\ FixedFairness

(* ===========================================================================
 * Invariants
 * =========================================================================== *)

\* When the worker submits the bio, the page must still be valid (not freed).
NoUAF ==
    worker_pc = "Submit" => page_state = "Valid"

(* ===========================================================================
 * Liveness Properties (Track E)
 * =========================================================================== *)

EventualCompletion ==
    <>(worker_pc = "Done" /\ evictor_pc = "Done")

==============================================================================
