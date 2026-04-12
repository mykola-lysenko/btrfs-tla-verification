------------------------ MODULE BtrfsQgroupLD ------------------------
EXTENDS Integers, FiniteSets, TLC

(*
 * BtrfsQgroupLD.tla — CVE-2025-39759 using LockDiscipline module
 *
 * This spec re-models the qgroup lockless-free race using the reusable
 * LockDiscipline module. It demonstrates how to use LockRequired() as
 * a guard in actions that access protected data structures.
 *
 * Two variants are controlled by the CONSTANT UseLock:
 *   UseLock = TRUE  -> correct: free_config holds qgroup_lock while iterating
 *   UseLock = FALSE -> buggy:   free_config does NOT hold the lock
 *)

INSTANCE LockDiscipline WITH
    Locks   <- {"qgroup_lock"},
    Threads <- {1, 2, 3}   \* 1=rescan, 2=free_config_1, 3=free_config_2

CONSTANTS
    Nodes,
    UseLock   \* BOOLEAN: TRUE=fixed, FALSE=buggy

ASSUME Nodes /= {}

VARIABLES
    qgroup_tree,
    freed_nodes,
    held_locks,   \* [Threads -> SUBSET {"qgroup_lock"}]
    rescan_pc,
    fc_pc,        \* [2..3 -> {"Idle","Iterate","Done"}]
    fc_iter       \* [2..3 -> Nodes \union {0}]

vars == <<qgroup_tree, freed_nodes, held_locks, rescan_pc, fc_pc, fc_iter>>

FCW == {2, 3}

Init ==
    /\ qgroup_tree = Nodes
    /\ freed_nodes = {}
    /\ held_locks  = [t \in {1,2,3} |-> {}]
    /\ rescan_pc   = "Idle"
    /\ fc_pc  = [f \in FCW |-> "Idle"]
    /\ fc_iter = [f \in FCW |-> 0]

\* ---- Rescan worker (thread 1) ----

RescanLock ==
    /\ rescan_pc = "Idle"
    /\ LockFree(held_locks, "qgroup_lock")
    /\ qgroup_tree /= {}
    /\ held_locks' = AcquireLock(held_locks, 1, "qgroup_lock")
    /\ rescan_pc' = "Free"
    /\ UNCHANGED <<qgroup_tree, freed_nodes, fc_pc, fc_iter>>

RescanFree ==
    /\ rescan_pc = "Free"
    /\ HoldsLock(held_locks, 1, "qgroup_lock")
    /\ LET n == CHOOSE n \in qgroup_tree : TRUE IN
       /\ qgroup_tree' = qgroup_tree \ {n}
       /\ freed_nodes' = freed_nodes \union {n}
    /\ rescan_pc' = "Unlock"
    /\ UNCHANGED <<held_locks, fc_pc, fc_iter>>

RescanUnlock ==
    /\ rescan_pc = "Unlock"
    /\ held_locks' = ReleaseLock(held_locks, 1, "qgroup_lock")
    /\ rescan_pc' = "Idle"
    /\ UNCHANGED <<qgroup_tree, freed_nodes, fc_pc, fc_iter>>

\* ---- free_config workers (threads 2 and 3) ----

FCStart(f) ==
    /\ fc_pc[f] = "Idle"
    /\ qgroup_tree /= {}
    /\ IF UseLock THEN
           /\ LockFree(held_locks, "qgroup_lock")
           /\ held_locks' = AcquireLock(held_locks, f, "qgroup_lock")
       ELSE
           /\ UNCHANGED <<held_locks>>
    /\ fc_pc'  = [fc_pc  EXCEPT ![f] = "Iterate"]
    /\ fc_iter' = [fc_iter EXCEPT ![f] = CHOOSE n \in qgroup_tree : TRUE]
    /\ UNCHANGED <<qgroup_tree, freed_nodes, rescan_pc>>

FCIterate(f) ==
    /\ fc_pc[f] = "Iterate"
    /\ fc_iter[f] /= 0
    \* Discipline check: if UseLock=TRUE, the lock must be held; otherwise this fires regardless
    /\ IF UseLock THEN
           LockRequired(held_locks, f, "qgroup_lock")
       ELSE
           TRUE
    \* UAF check
    /\ Assert(fc_iter[f] \notin freed_nodes,
              "UAF: free_config accessed a freed qgroup node!")
    /\ LET remaining == qgroup_tree \ {fc_iter[f]} IN
       IF remaining = {} THEN
           /\ fc_pc'  = [fc_pc  EXCEPT ![f] = IF UseLock THEN "Unlock" ELSE "Done"]
           /\ fc_iter' = [fc_iter EXCEPT ![f] = 0]
       ELSE
           /\ fc_iter' = [fc_iter EXCEPT ![f] = CHOOSE n \in remaining : TRUE]
           /\ UNCHANGED <<fc_pc>>
    /\ UNCHANGED <<qgroup_tree, freed_nodes, held_locks, rescan_pc>>

FCUnlock(f) ==
    /\ fc_pc[f] = "Unlock"
    /\ UseLock
    /\ held_locks' = ReleaseLock(held_locks, f, "qgroup_lock")
    /\ fc_pc' = [fc_pc EXCEPT ![f] = "Idle"]
    /\ UNCHANGED <<qgroup_tree, freed_nodes, rescan_pc, fc_iter>>

FCDone(f) ==
    /\ fc_pc[f] = "Done"
    /\ ~UseLock
    /\ fc_pc' = [fc_pc EXCEPT ![f] = "Idle"]
    /\ UNCHANGED <<qgroup_tree, freed_nodes, held_locks, rescan_pc, fc_iter>>

Next ==
    \/ RescanLock \/ RescanFree \/ RescanUnlock
    \/ \E f \in FCW : FCStart(f) \/ FCIterate(f) \/ FCUnlock(f) \/ FCDone(f)
    \/ /\ rescan_pc = "Idle"
       /\ \A f \in FCW : fc_pc[f] = "Idle"
       /\ UNCHANGED vars

MutexInvariant == MutualExclusion(held_locks, "qgroup_lock")

NoUAF == \A f \in FCW : fc_iter[f] \notin freed_nodes

Spec == Init /\ [][Next]_vars

=============================================================================
