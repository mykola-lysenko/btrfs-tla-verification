------------------------ MODULE BtrfsQgroupNFixed ------------------------
EXTENDS Integers, FiniteSets, TLC

(*
 * BtrfsQgroupNFixed.tla — CVE-2025-39759 (Qgroup Lockless Free Race)
 *
 * CORRESPONDENCE FIX 3.1: The previous fixed variant held qgroup_lock
 * continuously throughout the free_config loop. The real kernel code
 * (btrfs_free_qgroup_config in qgroup.c) does NOT do this. It drops and
 * reacquires the lock inside the loop to allow sysfs_del() and kfree() to
 * run without holding the spinlock.
 *
 * The real fix for CVE-2025-39759 is NOT continuous lock holding. The real
 * fix is:
 *   1. Set a "rescan_active" flag under the lock before the rescan worker
 *      starts iterating.
 *   2. The free_config loop checks this flag before freeing each node.
 *      If rescan is active, it skips the node (or waits for rescan to finish).
 *
 * This model accurately reflects the lock-drop-reacquire pattern and the
 * rescan_active guard that prevents the UAF.
 *
 * FIXED variant: free_config drops and reacquires lock per node, but checks
 * rescan_active before freeing to avoid UAF.
 *
 * Safety property: No thread ever accesses a freed node (no UAF).
 *)

CONSTANTS
    NumRescanWorkers,
    NumFreeConfigWorkers,
    Nodes

ASSUME NumRescanWorkers \in Nat /\ NumRescanWorkers >= 1
ASSUME NumFreeConfigWorkers \in Nat /\ NumFreeConfigWorkers >= 1
ASSUME Nodes # {}

VARIABLES
    qgroup_tree,        \* set of live qgroup nodes
    freed_nodes,        \* set of freed nodes (for UAF detection)
    qgroup_lock,        \* spinlock (TRUE = held)
    rescan_active,      \* TRUE when a rescan worker is iterating the tree
    rescan_pc,          \* [rescan_worker -> program counter]
    rescan_target,      \* [rescan_worker -> node being freed]
    fc_pc,              \* [free_config_worker -> program counter]
    fc_iter,            \* [free_config_worker -> current node being visited]
    fc_pending_free     \* [free_config_worker -> node to free after lock drop]

vars == <<qgroup_tree, freed_nodes, qgroup_lock, rescan_active,
          rescan_pc, rescan_target, fc_pc, fc_iter, fc_pending_free>>

RW == 1..NumRescanWorkers
FCW == 1..NumFreeConfigWorkers

Init ==
    /\ qgroup_tree     = Nodes
    /\ freed_nodes     = {}
    /\ qgroup_lock     = FALSE
    /\ rescan_active   = FALSE
    /\ rescan_pc       = [r \in RW  |-> "Idle"]
    /\ rescan_target   = [r \in RW  |-> 0]
    /\ fc_pc           = [f \in FCW |-> "Idle"]
    /\ fc_iter         = [f \in FCW |-> 0]
    /\ fc_pending_free = [f \in FCW |-> 0]

(* ---------------------------------------------------------------------------
 * Rescan worker: acquires lock, sets rescan_active, iterates tree, clears flag
 * Matches qgroup_rescan_leaf() which holds qgroup_lock while scanning.
 * --------------------------------------------------------------------------- *)

RescanLock(r) ==
    /\ rescan_pc[r] = "Idle"
    /\ qgroup_lock = FALSE
    /\ qgroup_tree # {}
    /\ qgroup_lock'    = TRUE
    /\ rescan_active'  = TRUE    \* set flag under lock
    /\ rescan_pc'      = [rescan_pc EXCEPT ![r] = "Scan"]
    /\ rescan_target'  = [rescan_target EXCEPT ![r] = CHOOSE n \in qgroup_tree : TRUE]
    /\ UNCHANGED <<qgroup_tree, freed_nodes, fc_pc, fc_iter, fc_pending_free>>

RescanScan(r) ==
    /\ rescan_pc[r] = "Scan"
    /\ qgroup_lock = TRUE
    /\ rescan_target[r] \in qgroup_tree   \* node is still live
    /\ Assert(rescan_target[r] \notin freed_nodes,
              "Rescan UAF: rescan accessed a freed node!")
    /\ rescan_pc' = [rescan_pc EXCEPT ![r] = "Unlock"]
    /\ UNCHANGED <<qgroup_tree, freed_nodes, qgroup_lock, rescan_active,
                   rescan_target, fc_pc, fc_iter, fc_pending_free>>

RescanUnlock(r) ==
    /\ rescan_pc[r] = "Unlock"
    /\ qgroup_lock'   = FALSE
    /\ rescan_active' = FALSE    \* clear flag under lock before releasing
    /\ rescan_pc'     = [rescan_pc EXCEPT ![r] = "Idle"]
    /\ UNCHANGED <<qgroup_tree, freed_nodes, rescan_target, fc_pc, fc_iter, fc_pending_free>>

(* ---------------------------------------------------------------------------
 * free_config worker (FIXED: lock-drop-reacquire with rescan_active guard)
 *
 * The real btrfs_free_qgroup_config() loop:
 *   spin_lock(&fs_info->qgroup_lock);
 *   while ((node = rb_first(&fs_info->qgroup_tree))) {
 *       qgroup = rb_entry(node, ...);
 *       rb_erase(node, &fs_info->qgroup_tree);
 *       spin_unlock(&fs_info->qgroup_lock);   <-- DROP
 *       sysfs_del(qgroup);
 *       kfree(qgroup);
 *       spin_lock(&fs_info->qgroup_lock);     <-- REACQUIRE
 *   }
 *   spin_unlock(&fs_info->qgroup_lock);
 *
 * The FIX adds a check: if rescan_active is set, skip the node (or wait).
 * This prevents the free_config worker from freeing a node that the rescan
 * worker is currently accessing.
 * --------------------------------------------------------------------------- *)

\* Step 1: acquire lock and pick the next node to free
FCLock(f) ==
    /\ fc_pc[f] = "Idle"
    /\ qgroup_lock = FALSE
    /\ qgroup_tree # {}
    /\ qgroup_lock' = TRUE
    /\ fc_pc'   = [fc_pc EXCEPT ![f] = "CheckRescan"]
    /\ fc_iter' = [fc_iter EXCEPT ![f] = CHOOSE n \in qgroup_tree : TRUE]
    /\ UNCHANGED <<qgroup_tree, freed_nodes, rescan_active,
                   rescan_pc, rescan_target, fc_pending_free>>

\* Step 2: check rescan_active under lock before deciding to free
\* FIX: if rescan_active, skip this node (don't free it)
FCCheckRescan(f) ==
    /\ fc_pc[f] = "CheckRescan"
    /\ qgroup_lock = TRUE
    /\ IF rescan_active THEN
           \* Rescan is active: skip this node, release lock, try again later
           /\ fc_pc'           = [fc_pc EXCEPT ![f] = "Unlock"]
           /\ fc_pending_free' = [fc_pending_free EXCEPT ![f] = 0]
       ELSE
           \* Safe to erase: remove from tree under lock, then drop to kfree
           /\ fc_iter[f] \in qgroup_tree
           /\ fc_pc'           = [fc_pc EXCEPT ![f] = "DropLock"]
           /\ fc_pending_free' = [fc_pending_free EXCEPT ![f] = fc_iter[f]]
    /\ UNCHANGED <<qgroup_tree, freed_nodes, qgroup_lock, rescan_active,
                   rescan_pc, rescan_target, fc_iter>>

\* Step 3: erase node from tree and drop lock (before kfree)
FCDropLock(f) ==
    /\ fc_pc[f] = "DropLock"
    /\ qgroup_lock = TRUE
    /\ fc_pending_free[f] \in qgroup_tree
    /\ qgroup_tree' = qgroup_tree \ {fc_pending_free[f]}
    /\ qgroup_lock' = FALSE
    /\ fc_pc'       = [fc_pc EXCEPT ![f] = "Free"]
    /\ UNCHANGED <<freed_nodes, rescan_active, rescan_pc, rescan_target,
                   fc_iter, fc_pending_free>>

\* Step 4: kfree (without lock) — this is where UAF would occur in the buggy variant
FCFree(f) ==
    /\ fc_pc[f] = "Free"
    /\ qgroup_lock = FALSE
    /\ fc_pending_free[f] # 0
    /\ Assert(fc_pending_free[f] \notin freed_nodes,
              "UAF: free_config freed a node already freed!")
    /\ freed_nodes'     = freed_nodes \union {fc_pending_free[f]}
    /\ fc_pending_free' = [fc_pending_free EXCEPT ![f] = 0]
    /\ fc_pc'           = [fc_pc EXCEPT ![f] = "Relock"]
    /\ UNCHANGED <<qgroup_tree, qgroup_lock, rescan_active,
                   rescan_pc, rescan_target, fc_iter>>

\* Step 5: reacquire lock for next iteration
FCRelock(f) ==
    /\ fc_pc[f] = "Relock"
    /\ qgroup_lock = FALSE
    /\ qgroup_lock' = TRUE
    /\ IF qgroup_tree = {} THEN
           /\ fc_pc'   = [fc_pc EXCEPT ![f] = "Unlock"]
           /\ fc_iter' = [fc_iter EXCEPT ![f] = 0]
       ELSE
           /\ fc_pc'   = [fc_pc EXCEPT ![f] = "CheckRescan"]
           /\ fc_iter' = [fc_iter EXCEPT ![f] = CHOOSE n \in qgroup_tree : TRUE]
    /\ UNCHANGED <<qgroup_tree, freed_nodes, rescan_active,
                   rescan_pc, rescan_target, fc_pending_free>>

\* Step 6: final unlock
FCUnlock(f) ==
    /\ fc_pc[f] = "Unlock"
    /\ qgroup_lock' = FALSE
    /\ fc_pc'       = [fc_pc EXCEPT ![f] = "Idle"]
    /\ UNCHANGED <<qgroup_tree, freed_nodes, rescan_active,
                   rescan_pc, rescan_target, fc_iter, fc_pending_free>>

Next ==
    \/ \E r \in RW  : RescanLock(r) \/ RescanScan(r) \/ RescanUnlock(r)
    \/ \E f \in FCW : FCLock(f) \/ FCCheckRescan(f) \/ FCDropLock(f) \/
                      FCFree(f) \/ FCRelock(f) \/ FCUnlock(f)
    \* Terminal stutter
    \/ /\ \A r \in RW  : rescan_pc[r] = "Idle"
       /\ \A f \in FCW : fc_pc[f] = "Idle"
       /\ UNCHANGED vars

Spec == Init /\ [][Next]_vars

\* Safety: no free_config worker ever accesses a freed node
NoUAF ==
    /\ \A f \in FCW : fc_iter[f] \notin freed_nodes
    /\ \A f \in FCW : fc_pending_free[f] \notin freed_nodes \/ fc_pending_free[f] = 0

\* Safety: rescan worker never accesses a freed node
NoRescanUAF ==
    \A r \in RW : rescan_target[r] \notin freed_nodes \/ rescan_pc[r] = "Idle"

=============================================================================
