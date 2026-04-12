------------------------ MODULE BtrfsQgroupBuggy ------------------------
EXTENDS Integers, Sequences, TLC

(*
This model demonstrates CVE-2025-39759: qgroup UAF.
The bug occurs because `btrfs_free_qgroup_config()` iterates the qgroup tree
without holding the `qgroup_lock`, while a rescan worker might be modifying it
or freeing nodes.
*)

VARIABLES
    qgroup_tree,       \* Set of node IDs currently in the tree
    freed_nodes,       \* Set of node IDs that have been freed
    qgroup_lock,       \* BOOLEAN
    rescan_pc,         \* {"Init", "Lock", "Modify", "Unlock", "Done"}
    free_config_pc,    \* {"Init", "Iterate", "Done"}
    iter_current       \* Node ID currently being visited by free_config

vars == <<qgroup_tree, freed_nodes, qgroup_lock, rescan_pc, free_config_pc, iter_current>>

Init ==
    /\ qgroup_tree = {1, 2}
    /\ freed_nodes = {}
    /\ qgroup_lock = FALSE
    /\ rescan_pc = "Init"
    /\ free_config_pc = "Init"
    /\ iter_current = 0

\* Rescan worker takes the lock and modifies/frees nodes
RescanStep1 ==
    /\ rescan_pc = "Init"
    /\ qgroup_lock = FALSE
    /\ qgroup_lock' = TRUE
    /\ rescan_pc' = "Modify"
    /\ UNCHANGED <<qgroup_tree, freed_nodes, free_config_pc, iter_current>>

RescanStep2 ==
    /\ rescan_pc = "Modify"
    /\ qgroup_lock = TRUE
    \* It removes node 2 from the tree and frees it
    /\ qgroup_tree' = qgroup_tree \ {2}
    /\ freed_nodes' = freed_nodes \union {2}
    /\ rescan_pc' = "Unlock"
    /\ UNCHANGED <<qgroup_lock, free_config_pc, iter_current>>

RescanStep3 ==
    /\ rescan_pc = "Unlock"
    /\ qgroup_lock' = FALSE
    /\ rescan_pc' = "Done"
    /\ UNCHANGED <<qgroup_tree, freed_nodes, free_config_pc, iter_current>>

\* free_config thread iterates the tree (BUGGY: doesn't take the lock!)
FreeConfigStep1 ==
    /\ free_config_pc = "Init"
    /\ free_config_pc' = "Iterate"
    /\ iter_current' = 1
    /\ UNCHANGED <<qgroup_tree, freed_nodes, qgroup_lock, rescan_pc>>

FreeConfigStep2 ==
    /\ free_config_pc = "Iterate"
    /\ iter_current \in {1, 2}
    \* It accesses the current node. If it's in freed_nodes, that's a UAF!
    /\ Assert(iter_current \notin freed_nodes, "Use-After-Free: Accessing a freed qgroup node!")
    /\ IF iter_current = 1 THEN
          /\ iter_current' = 2
          /\ free_config_pc' = "Iterate"
       ELSE
          /\ iter_current' = 0
          /\ free_config_pc' = "Done"
    /\ UNCHANGED <<qgroup_tree, freed_nodes, qgroup_lock, rescan_pc>>

Next ==
    \/ RescanStep1 \/ RescanStep2 \/ RescanStep3
    \/ FreeConfigStep1 \/ FreeConfigStep2
    \/ /\ rescan_pc = "Done"
       /\ free_config_pc = "Done"
       /\ UNCHANGED vars

Spec == Init /\ [][Next]_vars

=============================================================================
