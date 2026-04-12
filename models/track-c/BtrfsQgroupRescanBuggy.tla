-------------------------- MODULE BtrfsQgroupRescanBuggy --------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

(*
 * BtrfsQgroupRescanBuggy.tla
 * 
 * This is the BUGGY version of the qgroup rescan vs. snapshot creation model.
 * 
 * The bug being modeled is: the rescan worker continues to scan extents after
 * the snapshot is created, but it does NOT check qgroup_to_skip. This means
 * that extents scanned by the rescan worker after snapshot creation are
 * double-counted: once by the rescan worker (for both SrcRoot and SnapRoot),
 * and once by btrfs_qgroup_inherit (for SnapRoot via SrcRoot's count).
 *
 * In the real kernel, the rescan worker's btrfs_qgroup_account_extent() checks
 * qgroup_rescan_progress against the bytenr. If the rescan has already passed
 * the bytenr, it skips the accounting. This prevents double-counting.
 * 
 * The bug would be if the rescan worker did NOT have this check, or if the
 * check was racy with snapshot creation.
 *)

CONSTANTS
    Extents,           \* Set of extent IDs
    MaxSeq             \* Max transaction sequence

VARIABLES
    trans_state,       \* Transaction state: Running, CommitDoing, Unblocked
    rescan_state,      \* Rescan state: Idle, Running, Finished
    rescan_progress,   \* The extent ID the rescan is currently at
    qgroup_counts,     \* The accounted size for each root
    snapshot_pending,  \* Is a snapshot creation pending?
    qgroup_to_skip,    \* The qgroup ID to skip in accounting
    dirty_extents,     \* Extents modified in this transaction
    snapshot_root      \* The new snapshot root ID (if any)

vars == <<trans_state, rescan_state, rescan_progress, qgroup_counts, 
          snapshot_pending, qgroup_to_skip, dirty_extents, snapshot_root>>

\* Roots
SrcRoot == "Src"
SnapRoot == "Snap"

\* Transaction states
TransRunning == "Running"
TransCommitDoing == "CommitDoing"
TransUnblocked == "Unblocked"

\* Rescan states
RescanIdle == "Idle"
RescanRunning == "Running"
RescanFinished == "Finished"

Init ==
    /\ trans_state = TransRunning
    /\ rescan_state = RescanIdle
    /\ rescan_progress = 0
    /\ qgroup_counts = [r \in {SrcRoot, SnapRoot} |-> 0]
    /\ snapshot_pending = TRUE
    /\ qgroup_to_skip = "None"
    /\ dirty_extents = {}
    /\ snapshot_root = "None"

-----------------------------------------------------------------------------
\* RESCAN WORKER ACTIONS

StartRescan ==
    /\ rescan_state = RescanIdle
    /\ rescan_state' = RescanRunning
    /\ rescan_progress' = 1
    /\ UNCHANGED <<trans_state, qgroup_counts, snapshot_pending, qgroup_to_skip, dirty_extents, snapshot_root>>

RescanScanExtent ==
    /\ rescan_state = RescanRunning
    /\ rescan_progress \in Extents
    \* BUG: The rescan worker does NOT check qgroup_to_skip.
    \* So it accounts the extent to BOTH SrcRoot and SnapRoot unconditionally,
    \* even if SnapRoot was already accounted for via btrfs_qgroup_inherit.
    /\ qgroup_counts' = [qgroup_counts EXCEPT 
           ![SrcRoot] = qgroup_counts[SrcRoot] + 1,
           ![SnapRoot] = IF snapshot_root = SnapRoot
                         THEN qgroup_counts[SnapRoot] + 1 \* BUG: ignores qgroup_to_skip
                         ELSE qgroup_counts[SnapRoot]]
    /\ rescan_progress' = rescan_progress + 1
    /\ UNCHANGED <<trans_state, snapshot_pending, qgroup_to_skip, dirty_extents, snapshot_root, rescan_state>>

FinishRescan ==
    /\ rescan_state = RescanRunning
    /\ rescan_progress \notin Extents
    /\ rescan_state' = RescanFinished
    /\ UNCHANGED <<trans_state, rescan_progress, qgroup_counts, snapshot_pending, qgroup_to_skip, dirty_extents, snapshot_root>>

-----------------------------------------------------------------------------
\* TRANSACTION AND SNAPSHOT ACTIONS

ModifyExtent ==
    /\ trans_state = TransRunning
    /\ \E e \in Extents: 
        /\ e \notin dirty_extents
        /\ dirty_extents' = dirty_extents \union {e}
    /\ UNCHANGED <<trans_state, rescan_state, rescan_progress, qgroup_counts, snapshot_pending, qgroup_to_skip, snapshot_root>>

CommitTransactionStart ==
    /\ trans_state = TransRunning
    /\ trans_state' = TransCommitDoing
    /\ UNCHANGED <<rescan_state, rescan_progress, qgroup_counts, snapshot_pending, qgroup_to_skip, dirty_extents, snapshot_root>>

CreatePendingSnapshot ==
    /\ trans_state = TransCommitDoing
    /\ snapshot_pending = TRUE
    \* 1. Set qgroup_to_skip
    /\ qgroup_to_skip' = SnapRoot
    \* 2. Account dirty extents (simulate btrfs_qgroup_account_extents)
    \* BUG: qgroup_to_skip is set but btrfs_qgroup_account_extents doesn't check it properly.
    \* So dirty extents are accounted to BOTH SrcRoot and SnapRoot.
    \* 3. Inherit qgroup counts
    \* SnapRoot gets the same counts as SrcRoot, but dirty extents were already
    \* accounted to SnapRoot in step 2, so this is a double-count.
    /\ qgroup_counts' = [qgroup_counts EXCEPT 
           ![SrcRoot] = qgroup_counts[SrcRoot] + Cardinality(dirty_extents),
           ![SnapRoot] = qgroup_counts[SrcRoot] + 2 * Cardinality(dirty_extents)]
    /\ snapshot_root' = SnapRoot
    /\ snapshot_pending' = FALSE
    /\ dirty_extents' = {} \* Clear dirty extents
    /\ UNCHANGED <<trans_state, rescan_state, rescan_progress>>

CommitTransactionEnd ==
    /\ trans_state = TransCommitDoing
    /\ snapshot_pending = FALSE
    /\ trans_state' = TransUnblocked
    /\ qgroup_to_skip' = "None"
    /\ UNCHANGED <<rescan_state, rescan_progress, qgroup_counts, snapshot_pending, dirty_extents, snapshot_root>>

-----------------------------------------------------------------------------

Next ==
    \/ StartRescan
    \/ RescanScanExtent
    \/ FinishRescan
    \/ ModifyExtent
    \/ CommitTransactionStart
    \/ CreatePendingSnapshot
    \/ CommitTransactionEnd

Fairness ==
    /\ WF_vars(StartRescan)
    /\ WF_vars(RescanScanExtent)
    /\ WF_vars(FinishRescan)
    /\ WF_vars(CommitTransactionStart)
    /\ WF_vars(CreatePendingSnapshot)
    /\ WF_vars(CommitTransactionEnd)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
\* PROPERTIES

\* At the end of the transaction and rescan, both roots should have the same
\* accounted size (they share the same extents).
ConsistentAccounting == 
    (trans_state = TransUnblocked /\ rescan_state = RescanFinished /\ snapshot_pending = FALSE) =>
        (qgroup_counts[SrcRoot] = qgroup_counts[SnapRoot])

=============================================================================
