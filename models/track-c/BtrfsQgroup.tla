---------------------------- MODULE BtrfsQgroup ----------------------------
(*
 * Model: Btrfs qgroup double-counting race during snapshot operations
 *
 * Bug description:
 * When creating a snapshot, the qgroup accounting must track extents shared
 * between the source subvolume and the new snapshot. A race condition occurs
 * if an extent is deleted concurrently with the snapshot creation. The bug
 * is that the snapshot thread reads the extent size AFTER the deletion has
 * already updated the qgroup, causing the snapshot to add a stale non-zero
 * value to its qgroup even though the extent is already gone.
 *
 * Specifically, the buggy sequence is:
 * 1. Snapshot thread reads extent size: snap_read_size = 100.
 * 2. Concurrent deletion: extent_size = 0, qgroup_src -= 100.
 * 3. Snapshot thread adds snap_read_size to qgroup_snap: qgroup_snap += 100.
 * 4. Final: qgroup_src=0, qgroup_snap=100, extent_size=0
 *    -> snapshot "owns" 100 bytes of a non-existent extent (ghost accounting).
 *
 * Fix: Snapshot reads extent size atomically under a lock that also blocks deletion.
 *      This ensures the read and the qgroup update are atomic w.r.t. deletion.
 *
 * Ghost variable: delete_before_read tracks whether deletion ran before snap read.
 *
 * Invariant: NoGhostAccounting
 *   If deletion ran before snap's read, snap_read_size must be 0.
 *)

EXTENDS Integers, TLC

VARIABLES
    extent_size,
    snap_read_size,
    qgroup_src,
    qgroup_snap,
    snap_pc,
    mod_pc,
    extent_lock,
    delete_before_read  \* ghost: TRUE if deletion completed before snap read

vars == <<extent_size, snap_read_size, qgroup_src, qgroup_snap, snap_pc, mod_pc, extent_lock, delete_before_read>>

Init ==
    /\ extent_size = 100
    /\ snap_read_size = 0
    /\ qgroup_src = 100
    /\ qgroup_snap = 0
    /\ snap_pc = "Init"
    /\ mod_pc = "Init"
    /\ extent_lock = "Free"
    /\ delete_before_read = FALSE

(* ===========================================================================
 * BUGGY VARIANT: Snapshot reads size without holding lock
 * =========================================================================== *)

BuggySnapReadSize ==
    /\ snap_pc = "Init"
    /\ snap_read_size' = extent_size   \* BUG: no lock, stale read possible
    /\ snap_pc' = "UpdateQgroup"
    /\ UNCHANGED <<extent_size, qgroup_src, qgroup_snap, mod_pc, extent_lock, delete_before_read>>

BuggySnapUpdateQgroup ==
    /\ snap_pc = "UpdateQgroup"
    /\ qgroup_snap' = qgroup_snap + snap_read_size
    /\ snap_pc' = "Done"
    /\ UNCHANGED <<extent_size, snap_read_size, qgroup_src, mod_pc, extent_lock, delete_before_read>>

BuggyModDelete ==
    /\ mod_pc = "Init"
    /\ extent_size' = 0
    /\ qgroup_src' = qgroup_src - 100
    \* ghost: TRUE if snap already read a stale value (snap_pc=UpdateQgroup means
    \* snap read 100 but hasn't updated qgroup yet, and now deletion runs)
    /\ delete_before_read' = (snap_pc = "UpdateQgroup")
    /\ mod_pc' = "Done"
    /\ UNCHANGED <<snap_read_size, qgroup_snap, snap_pc, extent_lock>>

BuggyDone ==
    /\ snap_pc = "Done"
    /\ mod_pc = "Done"
    /\ UNCHANGED vars

BuggyNext ==
    \/ BuggySnapReadSize
    \/ BuggySnapUpdateQgroup
    \/ BuggyModDelete
    \/ BuggyDone

BuggyFairness ==
    /\ WF_vars(BuggySnapReadSize)
    /\ WF_vars(BuggySnapUpdateQgroup)
    /\ WF_vars(BuggyModDelete)

BuggySpec == Init /\ [][BuggyNext]_vars /\ BuggyFairness

(* ===========================================================================
 * FIXED VARIANT: Snapshot holds lock while reading size; deletion waits for lock
 * =========================================================================== *)

FixedSnapLockAndRead ==
    /\ snap_pc = "Init"
    /\ extent_lock = "Free"
    /\ extent_lock' = "Snap"
    /\ snap_read_size' = extent_size   \* FIX: atomic read under lock
    /\ snap_pc' = "UpdateQgroup"
    /\ UNCHANGED <<extent_size, qgroup_src, qgroup_snap, mod_pc, delete_before_read>>

FixedSnapUpdateAndUnlock ==
    /\ snap_pc = "UpdateQgroup"
    /\ qgroup_snap' = qgroup_snap + snap_read_size
    /\ extent_lock' = "Free"
    /\ snap_pc' = "Done"
    /\ UNCHANGED <<extent_size, snap_read_size, qgroup_src, mod_pc, delete_before_read>>

FixedModDelete ==
    /\ mod_pc = "Init"
    /\ extent_lock = "Free"   \* FIX: waits for lock
    /\ extent_lock' = "Mod"
    /\ extent_size' = 0
    /\ qgroup_src' = qgroup_src - 100
    /\ delete_before_read' = (snap_pc = "UpdateQgroup")  \* ghost
    /\ mod_pc' = "Unlock"
    /\ UNCHANGED <<snap_read_size, qgroup_snap, snap_pc>>

FixedModUnlock ==
    /\ mod_pc = "Unlock"
    /\ extent_lock' = "Free"
    /\ mod_pc' = "Done"
    /\ UNCHANGED <<extent_size, snap_read_size, qgroup_src, qgroup_snap, snap_pc, delete_before_read>>

FixedDone ==
    /\ snap_pc = "Done"
    /\ mod_pc = "Done"
    /\ UNCHANGED vars

FixedNext ==
    \/ FixedSnapLockAndRead
    \/ FixedSnapUpdateAndUnlock
    \/ FixedModDelete
    \/ FixedModUnlock
    \/ FixedDone

FixedFairness ==
    /\ WF_vars(FixedSnapLockAndRead)
    /\ WF_vars(FixedSnapUpdateAndUnlock)
    /\ WF_vars(FixedModDelete)
    /\ WF_vars(FixedModUnlock)

FixedSpec == Init /\ [][FixedNext]_vars /\ FixedFairness

(* ===========================================================================
 * Invariant
 * =========================================================================== *)

\* If deletion ran AFTER snap read a stale value (snap_pc was UpdateQgroup),
\* then snap_read_size=100 but the extent was deleted before snap updated qgroup.
\* This is ghost accounting: snap owns 100 bytes of a non-existent extent.
NoGhostAccounting ==
    (snap_pc = "Done" /\ mod_pc = "Done") =>
        ~(delete_before_read = TRUE /\ snap_read_size = 100)

(* ===========================================================================
 * Liveness Properties (Track E)
 * =========================================================================== *)

EventualCompletion ==
    <>(snap_pc = "Done" /\ mod_pc = "Done")

==============================================================================
