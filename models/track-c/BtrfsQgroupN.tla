------------------------ MODULE BtrfsQgroupN ------------------------
EXTENDS Integers, FiniteSets, TLC

(*
 * BtrfsQgroupN.tla — CVE-2025-39759 (Qgroup Lockless Free Race)
 *
 * Scaled to N concurrent threads:
 *   - NumRescanWorkers rescan workers, each of which may acquire qgroup_lock
 *     and free a node from the tree.
 *   - NumFreeConfigWorkers free_config threads, each of which iterates the
 *     qgroup tree.
 *
 * BUGGY variant: free_config threads do NOT hold qgroup_lock while iterating.
 *
 * Safety property: No thread ever accesses a freed node (no UAF).
 *
 * Symmetry: Both worker sets are symmetric, so TLC can use symmetry reduction.
 *)

CONSTANTS
    NumRescanWorkers,     \* e.g., 2
    NumFreeConfigWorkers, \* e.g., 2
    Nodes                 \* e.g., {1, 2, 3}

ASSUME NumRescanWorkers \in Nat /\ NumRescanWorkers >= 1
ASSUME NumFreeConfigWorkers \in Nat /\ NumFreeConfigWorkers >= 1
ASSUME Nodes # {}

VARIABLES
    qgroup_tree,     \* Set of live node IDs
    freed_nodes,     \* Set of freed node IDs
    qgroup_lock,     \* BOOLEAN (mutex)
    rescan_pc,       \* [1..NumRescanWorkers -> {"Idle","Lock","Free","Unlock"}]
    rescan_target,   \* [1..NumRescanWorkers -> Nodes \union {0}]
    fc_pc,           \* [1..NumFreeConfigWorkers -> {"Idle","Iterate","Done"}]
    fc_iter          \* [1..NumFreeConfigWorkers -> Nodes \union {0}]

vars == <<qgroup_tree, freed_nodes, qgroup_lock, rescan_pc, rescan_target, fc_pc, fc_iter>>

RW == 1..NumRescanWorkers
FCW == 1..NumFreeConfigWorkers

TypeOK ==
    /\ qgroup_tree \subseteq Nodes
    /\ freed_nodes \subseteq Nodes
    /\ qgroup_lock \in BOOLEAN
    /\ rescan_pc \in [RW -> {"Idle","Lock","Free","Unlock"}]
    /\ rescan_target \in [RW -> Nodes \union {0}]
    /\ fc_pc \in [FCW -> {"Idle","Iterate","Done"}]
    /\ fc_iter \in [FCW -> Nodes \union {0}]

Init ==
    /\ qgroup_tree = Nodes
    /\ freed_nodes = {}
    /\ qgroup_lock = FALSE
    /\ rescan_pc = [r \in RW |-> "Idle"]
    /\ rescan_target = [r \in RW |-> 0]
    /\ fc_pc = [f \in FCW |-> "Idle"]
    /\ fc_iter = [f \in FCW |-> 0]

\* ---- Rescan worker ----

RescanLock(r) ==
    /\ rescan_pc[r] = "Idle"
    /\ qgroup_lock = FALSE
    /\ qgroup_tree # {}
    /\ qgroup_lock' = TRUE
    /\ rescan_pc' = [rescan_pc EXCEPT ![r] = "Free"]
    /\ rescan_target' = [rescan_target EXCEPT ![r] = CHOOSE n \in qgroup_tree : TRUE]
    /\ UNCHANGED <<qgroup_tree, freed_nodes, fc_pc, fc_iter>>

RescanFree(r) ==
    /\ rescan_pc[r] = "Free"
    /\ qgroup_lock = TRUE
    /\ LET n == rescan_target[r] IN
       /\ n \in qgroup_tree
       /\ qgroup_tree' = qgroup_tree \ {n}
       /\ freed_nodes' = freed_nodes \union {n}
    /\ rescan_pc' = [rescan_pc EXCEPT ![r] = "Unlock"]
    /\ UNCHANGED <<qgroup_lock, rescan_target, fc_pc, fc_iter>>

RescanUnlock(r) ==
    /\ rescan_pc[r] = "Unlock"
    /\ qgroup_lock' = FALSE
    /\ rescan_pc' = [rescan_pc EXCEPT ![r] = "Idle"]
    /\ UNCHANGED <<qgroup_tree, freed_nodes, rescan_target, fc_pc, fc_iter>>

\* ---- free_config worker (BUGGY: no lock) ----

FCStart(f) ==
    /\ fc_pc[f] = "Idle"
    /\ qgroup_tree # {}
    /\ fc_pc' = [fc_pc EXCEPT ![f] = "Iterate"]
    /\ fc_iter' = [fc_iter EXCEPT ![f] = CHOOSE n \in qgroup_tree : TRUE]
    /\ UNCHANGED <<qgroup_tree, freed_nodes, qgroup_lock, rescan_pc, rescan_target>>

FCIterate(f) ==
    /\ fc_pc[f] = "Iterate"
    /\ fc_iter[f] # 0
    \* UAF check: accessing a freed node is a bug
    /\ Assert(fc_iter[f] \notin freed_nodes,
              "UAF: free_config accessed a freed qgroup node!")
    \* Advance to next node (or finish)
    /\ LET remaining == qgroup_tree \ {fc_iter[f]} IN
       IF remaining = {} THEN
           /\ fc_pc' = [fc_pc EXCEPT ![f] = "Done"]
           /\ fc_iter' = [fc_iter EXCEPT ![f] = 0]
       ELSE
           /\ fc_iter' = [fc_iter EXCEPT ![f] = CHOOSE n \in remaining : TRUE]
           /\ UNCHANGED <<fc_pc>>
    /\ UNCHANGED <<qgroup_tree, freed_nodes, qgroup_lock, rescan_pc, rescan_target>>

FCDone(f) ==
    /\ fc_pc[f] = "Done"
    /\ fc_pc' = [fc_pc EXCEPT ![f] = "Idle"]
    /\ UNCHANGED <<qgroup_tree, freed_nodes, qgroup_lock, rescan_pc, rescan_target, fc_iter>>

Next ==
    \/ \E r \in RW  : RescanLock(r) \/ RescanFree(r) \/ RescanUnlock(r)
    \/ \E f \in FCW : FCStart(f) \/ FCIterate(f) \/ FCDone(f)
    \* Terminal stutter
    \/ /\ \A r \in RW  : rescan_pc[r] = "Idle"
       /\ \A f \in FCW : fc_pc[f] = "Idle"
       /\ UNCHANGED vars

Spec == Init /\ [][Next]_vars

\* Safety: no thread ever touches a freed node
NoUAF == \A f \in FCW : fc_iter[f] \notin freed_nodes

=============================================================================
