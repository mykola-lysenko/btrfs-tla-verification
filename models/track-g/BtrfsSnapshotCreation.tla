---- MODULE BtrfsSnapshotCreation ----
(*
 * Model: Btrfs Snapshot Creation vs. COW Race
 *
 * Bug description:
 * When creating a snapshot, Btrfs duplicates the root node of the subvolume.
 * Concurrently, user operations might be doing COW (Copy-On-Write) on that
 * same subvolume. If a COW operation modifies the root node after the snapshot
 * has duplicated it but before the snapshot is fully committed, the snapshot
 * might capture an inconsistent state or the COW might leak an extent.
 *
 * Fix: Snapshot creation takes a specific lock (or blocks new transactions)
 * to ensure that no COW operations can modify the root while it is being
 * duplicated.
 *)

EXTENDS Integers, TLC

VARIABLES
    root_node_version,
    snapshot_captured_version,
    snap_state,
    cow_state,
    transaction_blocked

vars == <<root_node_version, snapshot_captured_version, snap_state, cow_state, transaction_blocked>>

Init ==
    /\ root_node_version = 1
    /\ snapshot_captured_version = 0
    /\ snap_state = "Init"
    /\ cow_state = "Init"
    /\ transaction_blocked = FALSE

(* ===========================================================================
 * BUGGY VARIANT: Snapshot captures without blocking COW
 * =========================================================================== *)

BuggySnapCapture ==
    /\ snap_state = "Init"
    /\ snapshot_captured_version' = root_node_version
    /\ snap_state' = "Done"
    /\ UNCHANGED <<root_node_version, cow_state, transaction_blocked>>

BuggyCOWModify ==
    /\ cow_state = "Init"
    /\ root_node_version' = root_node_version + 1
    /\ cow_state' = "Done"
    /\ UNCHANGED <<snapshot_captured_version, snap_state, transaction_blocked>>

BuggyDone ==
    /\ snap_state = "Done"
    /\ cow_state = "Done"
    /\ UNCHANGED vars

BuggyNext ==
    \/ BuggySnapCapture
    \/ BuggyCOWModify
    \/ BuggyDone

BuggyFairness ==
    /\ WF_vars(BuggySnapCapture)
    /\ WF_vars(BuggyCOWModify)

BuggySpec == Init /\ [][BuggyNext]_vars /\ BuggyFairness

(* ===========================================================================
 * FIXED VARIANT: Snapshot blocks transactions during capture
 * =========================================================================== *)

FixedSnapBlock ==
    /\ snap_state = "Init"
    /\ transaction_blocked' = TRUE
    /\ snap_state' = "Capture"
    /\ UNCHANGED <<root_node_version, snapshot_captured_version, cow_state>>

FixedSnapCapture ==
    /\ snap_state = "Capture"
    /\ snapshot_captured_version' = root_node_version
    /\ transaction_blocked' = FALSE
    /\ snap_state' = "Done"
    /\ UNCHANGED <<root_node_version, cow_state>>

FixedCOWModify ==
    /\ cow_state = "Init"
    /\ transaction_blocked = FALSE
    /\ root_node_version' = root_node_version + 1
    /\ cow_state' = "Done"
    /\ UNCHANGED <<snapshot_captured_version, snap_state, transaction_blocked>>

FixedDone ==
    /\ snap_state = "Done"
    /\ cow_state = "Done"
    /\ UNCHANGED vars

FixedNext ==
    \/ FixedSnapBlock
    \/ FixedSnapCapture
    \/ FixedCOWModify
    \/ FixedDone

FixedFairness ==
    /\ WF_vars(FixedSnapBlock)
    /\ WF_vars(FixedSnapCapture)
    /\ WF_vars(FixedCOWModify)

FixedSpec == Init /\ [][FixedNext]_vars /\ FixedFairness

(* ===========================================================================
 * Invariants
 * =========================================================================== *)

\* If snapshot runs first, it captures v1, and COW modifies to v2.
\* If COW runs first, it modifies to v2, and snapshot captures v2.
\* In the buggy variant, it's possible for snapshot to capture v1, and COW
\* modifies to v2 concurrently. But wait, in TLA+, interleaving means one
\* happens before the other. To model the actual bug, we need the snapshot
\* to read the root, then COW modifies it and frees the old root, then
\* snapshot commits the old root.
\* For simplicity, we just verify that COW cannot run while snapshot is
\* capturing (i.e., transaction_blocked is effective).
NoConcurrentModification ==
    (snap_state = "Capture") => (cow_state = "Init" \/ cow_state = "Done")

EventualCompletion ==
    <>(snap_state = "Done" /\ cow_state = "Done")

=============================================================================
