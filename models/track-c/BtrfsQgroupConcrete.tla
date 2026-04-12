---- MODULE BtrfsQgroupConcrete ----
(*
 * Model: Concrete Btrfs Qgroup Accounting
 *
 * This model is a detailed representation of fs/btrfs/qgroup.c
 * btrfs_qgroup_account_extent and btrfs_qgroup_inherit.
 *)

EXTENDS Integers, TLC

VARIABLES
    \* Concrete variables
    extent_bytes,
    src_qgroup_bytes,
    snap_qgroup_bytes,
    
    \* Locks
    btrfs_qgroup_lock,  \* BOOLEAN (TRUE = locked, FALSE = unlocked)
    
    \* Thread states
    snap_state,
    mod_state,
    snap_bytes_read,
    delete_before_read

vars == <<extent_bytes, src_qgroup_bytes, snap_qgroup_bytes,
          btrfs_qgroup_lock, snap_state, mod_state, snap_bytes_read, delete_before_read>>

Init ==
    /\ extent_bytes = 100
    /\ src_qgroup_bytes = 100
    /\ snap_qgroup_bytes = 0
    /\ btrfs_qgroup_lock = FALSE
    /\ snap_state = "Init"
    /\ mod_state = "Init"
    /\ snap_bytes_read = 0
    /\ delete_before_read = FALSE

\* Snapshot thread: lock and read
SnapLockAndRead ==
    /\ snap_state = "Init"
    /\ btrfs_qgroup_lock = FALSE
    /\ btrfs_qgroup_lock' = TRUE
    /\ snap_bytes_read' = extent_bytes
    /\ snap_state' = "UpdateQgroup"
    /\ UNCHANGED <<extent_bytes, src_qgroup_bytes, snap_qgroup_bytes, mod_state, delete_before_read>>

\* Snapshot thread: update and unlock
SnapUpdateAndUnlock ==
    /\ snap_state = "UpdateQgroup"
    /\ snap_qgroup_bytes' = snap_qgroup_bytes + snap_bytes_read
    /\ btrfs_qgroup_lock' = FALSE
    /\ snap_state' = "Done"
    /\ UNCHANGED <<extent_bytes, src_qgroup_bytes, mod_state, snap_bytes_read, delete_before_read>>

\* Mod thread: wait for lock and delete
ModDelete ==
    /\ mod_state = "Init"
    /\ btrfs_qgroup_lock = FALSE
    /\ btrfs_qgroup_lock' = TRUE
    /\ extent_bytes' = 0
    /\ src_qgroup_bytes' = src_qgroup_bytes - 100
    /\ delete_before_read' = (snap_state = "UpdateQgroup")
    /\ mod_state' = "Unlock"
    /\ UNCHANGED <<snap_qgroup_bytes, snap_state, snap_bytes_read>>

\* Mod thread: unlock
ModUnlock ==
    /\ mod_state = "Unlock"
    /\ btrfs_qgroup_lock' = FALSE
    /\ mod_state' = "Done"
    /\ UNCHANGED <<extent_bytes, src_qgroup_bytes, snap_qgroup_bytes, snap_state, snap_bytes_read, delete_before_read>>

Done ==
    /\ snap_state = "Done"
    /\ mod_state = "Done"
    /\ UNCHANGED vars

Next ==
    \/ SnapLockAndRead
    \/ SnapUpdateAndUnlock
    \/ ModDelete
    \/ ModUnlock
    \/ Done

Fairness ==
    /\ WF_vars(SnapLockAndRead)
    /\ WF_vars(SnapUpdateAndUnlock)
    /\ WF_vars(ModDelete)
    /\ WF_vars(ModUnlock)

Spec == Init /\ [][Next]_vars /\ Fairness

=============================================================================
