--------------------------- MODULE BtrfsQgroupRescan ---------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

(*
 * BtrfsQgroupRescan.tla
 * 
 * This model captures the interaction between btrfs qgroup rescan and snapshot
 * creation during transaction commit.
 * 
 * The kernel uses several mechanisms to prevent double-accounting or missed
 * accounting when a snapshot is created while a qgroup rescan is running:
 * 1. Snapshot creation happens in TRANS_STATE_COMMIT_DOING
 * 2. It sets delayed_refs->qgroup_to_skip to the new snapshot's qgroup ID
 * 3. It calls qgroup_account_snapshot() which flushes delayed refs, commits
 *    fs roots, and runs btrfs_qgroup_account_extents() BEFORE inheriting
 * 4. It inherits the qgroup counts (btrfs_qgroup_inherit)
 * 5. The rescan worker holds qgroup_rescan_lock while scanning leaves, and
 *    btrfs_qgroup_account_extent() also checks qgroup_rescan_progress.
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
    \* In reality, rescan reads the extent and adds it to the qgroup if it belongs to it.
    \* For simplicity, we just say it accounts the extent to SrcRoot if it's not skipped.
    \* If snapshot_root is created and we aren't skipping it, it gets the extent too.
    \* Note: btrfs_qgroup_account_extent checks qgroup_rescan_progress.
    \* If rescan has passed this extent (progress > extent), it's already accounted.
    \* Here we just say the rescan worker accounts it directly.
    /\ qgroup_counts' = [qgroup_counts EXCEPT 
           ![SrcRoot] = qgroup_counts[SrcRoot] + 1,
           ![SnapRoot] = IF snapshot_root = SnapRoot
                         THEN qgroup_counts[SnapRoot] + 1 
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
    \* It checks qgroup_to_skip. So it accounts dirty extents to SrcRoot, but NOT SnapRoot.
    \* 3. Inherit qgroup counts
    \* SnapRoot gets the same counts as SrcRoot, including the dirty extents we just accounted to SrcRoot.
    \* BUT, what about extents that were already scanned by rescan?
    \* If rescan hasn't finished, the counts might be partial. 
    \* Let's say we inherit the exact current count of SrcRoot + dirty extents.
    \* We must be careful not to double count if rescan already counted it.
    \* For simplicity in this abstract model, if an extent is dirty, it is a newly allocated extent.
    \* If it's newly allocated, rescan hasn't seen it (rescan only scans old commit root).
    \* So we add Cardinality(dirty_extents).
    /\ qgroup_counts' = [qgroup_counts EXCEPT 
           ![SrcRoot] = qgroup_counts[SrcRoot] + Cardinality(dirty_extents),
           ![SnapRoot] = qgroup_counts[SrcRoot] + Cardinality(dirty_extents)]
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
\* accounted size, which should equal the total number of extents (since all
\* extents belong to the source root, and the snapshot shares them).
TotalExtents == Cardinality(Extents) + Cardinality(dirty_extents)

\* We define TotalExtents as the total number of extents including dirty ones that have been accounted
ConsistentAccounting == 
    (trans_state = TransUnblocked /\ rescan_state = RescanFinished /\ snapshot_pending = FALSE) =>
        (qgroup_counts[SrcRoot] = qgroup_counts[SnapRoot])

=============================================================================
