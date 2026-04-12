------------------------ MODULE BtrfsDelayedRefsMultiAborter ------------------------
(*
 * Model: Two concurrent aborters racing on the same delayed ref head
 *
 * Real code: btrfs_destroy_delayed_refs() in delayed-ref.c
 *   The function holds delayed_refs->lock, iterates the XArray, and for each
 *   head calls btrfs_delayed_ref_lock() (a mutex_trylock loop) before freeing.
 *   If two aborters run concurrently (e.g., two error paths both calling
 *   btrfs_destroy_delayed_refs), they can both see the same head, both call
 *   mutex_trylock, and the loser will try to free an already-freed head.
 *
 * Bug surface:
 *   - Aborter A: reads head H, trylock succeeds, frees H
 *   - Aborter B: reads head H (before A freed it), trylock also succeeds
 *     (lock was released by A during free), frees H again -> double-free
 *
 * Fix: The tree lock (delayed_refs->lock) must be held continuously while
 *   iterating. Only one aborter can hold the tree lock at a time. The second
 *   aborter must wait for the first to finish, then find an empty tree.
 *
 * Correspondence:
 *   - head_live[h]     : head exists in the XArray (protected by tree_lock)
 *   - head_lock[h]     : per-head mutex (btrfs_delayed_ref_lock)
 *   - tree_lock        : delayed_refs->lock (spinlock)
 *   - aborter_pc[a]    : program counter for aborter a
 *     "Idle" -> "AcquireTreeLock" -> "Scan" -> "TryLockHead" -> "FreeHead"
 *     -> "ReleaseTreeLock" -> "Done"
 *
 * Invariants:
 *   NoDoubleFree: a head is never freed twice
 *   NoFreeWithoutLock: a head is only freed when the aborter holds head_lock
 *)

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS NumHeads, NumAborters  \* NumHeads: delayed ref heads; NumAborters: concurrent aborters

ASSUME NumHeads \in 1..4 /\ NumAborters \in 2..3

Heads   == 1..NumHeads
Aborters == 1..NumAborters

(* ---------------------------------------------------------------------------
 * State variables
 * --------------------------------------------------------------------------- *)
VARIABLES
    head_live,      \* head_live[h] : TRUE if head h exists in the XArray
    head_lock,      \* head_lock[h] : TRUE if the per-head mutex is held
    head_lock_by,   \* head_lock_by[h] : which aborter holds the head lock (0 = none)
    free_count,     \* free_count[h] : how many times head h has been freed (for NoDoubleFree)
    tree_lock,      \* tree_lock : TRUE if the tree spinlock is held
    tree_lock_by,   \* tree_lock_by : which aborter holds the tree lock (0 = none)
    aborter_pc,     \* aborter_pc[a] : program counter
    aborter_target  \* aborter_target[a] : which head the aborter is currently working on

vars == <<head_live, head_lock, head_lock_by, free_count,
          tree_lock, tree_lock_by, aborter_pc, aborter_target>>

(* ---------------------------------------------------------------------------
 * Initial state: all heads live, no locks held
 * --------------------------------------------------------------------------- *)
Init ==
    /\ head_live    = [h \in Heads |-> TRUE]
    /\ head_lock    = [h \in Heads |-> FALSE]
    /\ head_lock_by = [h \in Heads |-> 0]
    /\ free_count   = [h \in Heads |-> 0]
    /\ tree_lock    = FALSE
    /\ tree_lock_by = 0
    /\ aborter_pc   = [a \in Aborters |-> "Idle"]
    /\ aborter_target = [a \in Aborters |-> 0]

(* ---------------------------------------------------------------------------
 * Buggy aborter actions (no tree lock held continuously)
 *
 * The bug: the aborter releases the tree lock before acquiring the head lock,
 * creating a window where another aborter can see and free the same head.
 * --------------------------------------------------------------------------- *)

\* Aborter starts: acquire tree lock
BuggyAborterStart(a) ==
    /\ aborter_pc[a] = "Idle"
    /\ ~tree_lock
    /\ tree_lock'    = TRUE
    /\ tree_lock_by' = a
    /\ aborter_pc'   = [aborter_pc EXCEPT ![a] = "Scan"]
    /\ UNCHANGED <<head_live, head_lock, head_lock_by, free_count, aborter_target>>

\* Aborter scans: pick a live head and RELEASE tree lock before locking head
\* (this is the bug: releasing tree lock creates a race window)
BuggyAborterScan(a) ==
    /\ aborter_pc[a] = "Scan"
    /\ tree_lock_by = a
    /\ \E h \in Heads : head_live[h]   \* there is a live head
    /\ LET h == CHOOSE h \in Heads : head_live[h] IN
       /\ aborter_target' = [aborter_target EXCEPT ![a] = h]
       /\ tree_lock'    = FALSE          \* BUG: release tree lock before head lock
       /\ tree_lock_by' = 0
       /\ aborter_pc'   = [aborter_pc EXCEPT ![a] = "TryLockHead"]
    /\ UNCHANGED <<head_live, head_lock, head_lock_by, free_count>>

\* Aborter tries to lock the head (mutex_trylock)
BuggyAborterTryLock(a) ==
    /\ aborter_pc[a] = "TryLockHead"
    /\ LET h == aborter_target[a] IN
       /\ ~head_lock[h]                  \* trylock succeeds
       /\ head_lock'    = [head_lock    EXCEPT ![h] = TRUE]
       /\ head_lock_by' = [head_lock_by EXCEPT ![h] = a]
       /\ aborter_pc'   = [aborter_pc EXCEPT ![a] = "FreeHead"]
    /\ UNCHANGED <<head_live, free_count, tree_lock, tree_lock_by, aborter_target>>

\* Aborter frees the head (while holding head lock)
BuggyAborterFreeHead(a) ==
    /\ aborter_pc[a] = "FreeHead"
    /\ LET h == aborter_target[a] IN
       /\ head_lock_by[h] = a            \* aborter holds the head lock
       /\ head_live'    = [head_live    EXCEPT ![h] = FALSE]
       /\ free_count'   = [free_count   EXCEPT ![h] = free_count[h] + 1]
       /\ head_lock'    = [head_lock    EXCEPT ![h] = FALSE]
       /\ head_lock_by' = [head_lock_by EXCEPT ![h] = 0]
       /\ aborter_pc'   = [aborter_pc EXCEPT ![a] = "Done"]
    /\ UNCHANGED <<tree_lock, tree_lock_by, aborter_target>>

\* Aborter done: reset
BuggyAborterDone(a) ==
    /\ aborter_pc[a] = "Done"
    /\ aborter_pc'     = [aborter_pc     EXCEPT ![a] = "Idle"]
    /\ aborter_target' = [aborter_target EXCEPT ![a] = 0]
    /\ UNCHANGED <<head_live, head_lock, head_lock_by, free_count,
                   tree_lock, tree_lock_by>>

\* Aborter stutter when no live heads remain
BuggyAborterNoHeads(a) ==
    /\ aborter_pc[a] = "Scan"
    /\ tree_lock_by = a
    /\ ~\E h \in Heads : head_live[h]   \* no live heads
    /\ tree_lock'    = FALSE
    /\ tree_lock_by' = 0
    /\ aborter_pc'   = [aborter_pc EXCEPT ![a] = "Done"]
    /\ UNCHANGED <<head_live, head_lock, head_lock_by, free_count, aborter_target>>

(* ---------------------------------------------------------------------------
 * Invariants
 * --------------------------------------------------------------------------- *)

\* A head must never be freed more than once
NoDoubleFree == \A h \in Heads : free_count[h] <= 1

\* A head must only be freed when the aborter holds the head lock
NoFreeWithoutLock ==
    \A a \in Aborters :
        aborter_pc[a] = "FreeHead" =>
            head_lock_by[aborter_target[a]] = a

\* The tree lock must be held by at most one aborter
TreeLockMutex ==
    Cardinality({a \in Aborters : tree_lock_by = a}) <= 1

(* ---------------------------------------------------------------------------
 * Next and Spec
 * --------------------------------------------------------------------------- *)
BuggyNext ==
    \E a \in Aborters :
        \/ BuggyAborterStart(a)
        \/ BuggyAborterScan(a)
        \/ BuggyAborterTryLock(a)
        \/ BuggyAborterFreeHead(a)
        \/ BuggyAborterDone(a)
        \/ BuggyAborterNoHeads(a)

BuggyFairness ==
    /\ \A a \in Aborters :
           WF_vars(BuggyAborterStart(a))
        /\ WF_vars(BuggyAborterScan(a))
        /\ WF_vars(BuggyAborterTryLock(a))
        /\ WF_vars(BuggyAborterFreeHead(a))
        /\ WF_vars(BuggyAborterDone(a))
        /\ WF_vars(BuggyAborterNoHeads(a))

BuggySpec == Init /\ [][BuggyNext]_vars /\ BuggyFairness

==============================================================================
