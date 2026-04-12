------------------ MODULE BtrfsDelayedRefsMultiAborterFixed ------------------
(*
 * Fixed model: tree lock held continuously during the entire destroy loop.
 * Only one aborter can run at a time. The second aborter waits, then finds
 * an empty tree and exits immediately.
 *
 * This matches the real btrfs_destroy_delayed_refs() which holds
 * delayed_refs->lock (a spinlock) across the entire XArray iteration.
 *)

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS NumHeads, NumAborters

ASSUME NumHeads \in 1..4 /\ NumAborters \in 2..3

Heads    == 1..NumHeads
Aborters == 1..NumAborters

VARIABLES
    head_live,
    head_lock,
    head_lock_by,
    free_count,
    tree_lock,
    tree_lock_by,
    aborter_pc,
    aborter_target

vars == <<head_live, head_lock, head_lock_by, free_count,
          tree_lock, tree_lock_by, aborter_pc, aborter_target>>

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
 * Fixed aborter actions: tree lock held throughout the loop
 * --------------------------------------------------------------------------- *)

\* Aborter starts: acquire tree lock (blocks if another aborter holds it)
FixedAborterStart(a) ==
    /\ aborter_pc[a] = "Idle"
    /\ ~tree_lock
    /\ tree_lock'    = TRUE
    /\ tree_lock_by' = a
    /\ aborter_pc'   = [aborter_pc EXCEPT ![a] = "Scan"]
    /\ UNCHANGED <<head_live, head_lock, head_lock_by, free_count, aborter_target>>

\* Aborter scans: pick a live head WHILE HOLDING tree lock
\* FIX: tree lock is NOT released before locking the head
FixedAborterScan(a) ==
    /\ aborter_pc[a] = "Scan"
    /\ tree_lock_by = a
    /\ \E h \in Heads : head_live[h]
    /\ LET h == CHOOSE h \in Heads : head_live[h] IN
       /\ aborter_target' = [aborter_target EXCEPT ![a] = h]
       /\ aborter_pc'     = [aborter_pc EXCEPT ![a] = "TryLockHead"]
    /\ UNCHANGED <<head_live, head_lock, head_lock_by, free_count,
                   tree_lock, tree_lock_by>>

\* Aborter locks the head (while still holding tree lock)
FixedAborterLockHead(a) ==
    /\ aborter_pc[a] = "TryLockHead"
    /\ tree_lock_by = a                  \* still holding tree lock
    /\ LET h == aborter_target[a] IN
       /\ ~head_lock[h]
       /\ head_lock'    = [head_lock    EXCEPT ![h] = TRUE]
       /\ head_lock_by' = [head_lock_by EXCEPT ![h] = a]
       /\ aborter_pc'   = [aborter_pc EXCEPT ![a] = "FreeHead"]
    /\ UNCHANGED <<head_live, free_count, tree_lock, tree_lock_by, aborter_target>>

\* Aborter frees the head, releases head lock, continues scan
FixedAborterFreeHead(a) ==
    /\ aborter_pc[a] = "FreeHead"
    /\ tree_lock_by = a                  \* still holding tree lock
    /\ LET h == aborter_target[a] IN
       /\ head_lock_by[h] = a
       /\ head_live'    = [head_live    EXCEPT ![h] = FALSE]
       /\ free_count'   = [free_count   EXCEPT ![h] = free_count[h] + 1]
       /\ head_lock'    = [head_lock    EXCEPT ![h] = FALSE]
       /\ head_lock_by' = [head_lock_by EXCEPT ![h] = 0]
       /\ aborter_target' = [aborter_target EXCEPT ![a] = 0]
       /\ aborter_pc'   = [aborter_pc EXCEPT ![a] = "Scan"]  \* continue loop
    /\ UNCHANGED <<tree_lock, tree_lock_by>>

\* Aborter finishes: no more live heads, release tree lock
FixedAborterNoHeads(a) ==
    /\ aborter_pc[a] = "Scan"
    /\ tree_lock_by = a
    /\ ~\E h \in Heads : head_live[h]
    /\ tree_lock'    = FALSE
    /\ tree_lock_by' = 0
    /\ aborter_pc'   = [aborter_pc EXCEPT ![a] = "Done"]
    /\ UNCHANGED <<head_live, head_lock, head_lock_by, free_count, aborter_target>>

\* Aborter done: reset
FixedAborterDone(a) ==
    /\ aborter_pc[a] = "Done"
    /\ aborter_pc'     = [aborter_pc     EXCEPT ![a] = "Idle"]
    /\ aborter_target' = [aborter_target EXCEPT ![a] = 0]
    /\ UNCHANGED <<head_live, head_lock, head_lock_by, free_count,
                   tree_lock, tree_lock_by>>

(* ---------------------------------------------------------------------------
 * Invariants
 * --------------------------------------------------------------------------- *)
NoDoubleFree == \A h \in Heads : free_count[h] <= 1

NoFreeWithoutLock ==
    \A a \in Aborters :
        aborter_pc[a] = "FreeHead" =>
            head_lock_by[aborter_target[a]] = a

TreeLockMutex ==
    Cardinality({a \in Aborters : tree_lock_by = a}) <= 1

\* Liveness: all heads are eventually freed
AllHeadsEventuallyFreed ==
    <>(\A h \in Heads : ~head_live[h])

(* ---------------------------------------------------------------------------
 * Next and Spec
 * --------------------------------------------------------------------------- *)
FixedNext ==
    \E a \in Aborters :
        \/ FixedAborterStart(a)
        \/ FixedAborterScan(a)
        \/ FixedAborterLockHead(a)
        \/ FixedAborterFreeHead(a)
        \/ FixedAborterNoHeads(a)
        \/ FixedAborterDone(a)

FixedFairness ==
    /\ \A a \in Aborters :
           SF_vars(FixedAborterStart(a))
        /\ WF_vars(FixedAborterScan(a))
        /\ WF_vars(FixedAborterLockHead(a))
        /\ WF_vars(FixedAborterFreeHead(a))
        /\ WF_vars(FixedAborterNoHeads(a))
        /\ WF_vars(FixedAborterDone(a))

Spec == Init /\ [][FixedNext]_vars /\ FixedFairness

==============================================================================
