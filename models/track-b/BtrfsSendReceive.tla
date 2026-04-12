---------------------------- MODULE BtrfsSendReceive ----------------------------
(*
 * Model: Btrfs send/receive path race with concurrent snapshot deletion
 *
 * Bug description:
 * The `btrfs send` operation iterates over the B-tree of a snapshot to generate
 * a stream of filesystem changes. A concurrent `btrfs subvolume delete` can
 * delete the snapshot while the send operation is still running. If the deletion
 * doesn't wait for send operations to finish, the send thread will encounter a
 * use-after-free when it tries to read the next node.
 *
 * Sequence (buggy):
 * 1. Send starts, gets snapshot root pointer (no send_in_progress increment).
 * 2. Delete starts, does NOT check send_in_progress.
 * 3. Delete deletes snapshot, frees all nodes.
 * 4. Send tries to read the next node -> UAF.
 *
 * Fix: The send operation increments send_in_progress on the root before
 * iterating. The snapshot deletion path checks send_in_progress and returns
 * -EPERM if > 0, preventing deletion while a send is active.
 *
 * Variables:
 *   snapshot_state: "Valid" | "Deleted"
 *   send_in_progress: integer (number of active send operations)
 *   send_pc: "Init" | "GetRoot" | "ReadNode" | "Done"
 *   delete_pc: "Init" | "TryDelete" | "Done"
 *   crash_uaf: TRUE | FALSE
 *)

EXTENDS Integers, TLC

VARIABLES
    snapshot_state,
    send_in_progress,
    send_pc,
    delete_pc,
    crash_uaf

vars == <<snapshot_state, send_in_progress, send_pc, delete_pc, crash_uaf>>

Init ==
    /\ snapshot_state = "Valid"
    /\ send_in_progress = 0
    /\ send_pc = "Init"
    /\ delete_pc = "Init"
    /\ crash_uaf = FALSE

(* ===========================================================================
 * BUGGY VARIANT: Send does not increment send_in_progress
 *                Delete does not check send_in_progress
 * =========================================================================== *)

\* Send gets root pointer (no protection)
BuggySendGetRoot ==
    /\ send_pc = "Init"
    /\ send_pc' = "ReadNode"
    /\ UNCHANGED <<snapshot_state, send_in_progress, delete_pc, crash_uaf>>

\* Send reads a node -- UAF if snapshot was deleted
BuggySendReadNode ==
    /\ send_pc = "ReadNode"
    /\ crash_uaf' = IF snapshot_state = "Deleted" THEN TRUE ELSE crash_uaf
    /\ send_pc' = "Done"
    /\ UNCHANGED <<snapshot_state, send_in_progress, delete_pc>>

\* Delete starts and immediately deletes (no check)
BuggyDeleteTryDelete ==
    /\ delete_pc = "Init"
    /\ snapshot_state' = "Deleted"
    /\ delete_pc' = "Done"
    /\ UNCHANGED <<send_in_progress, send_pc, crash_uaf>>

BuggyDone ==
    /\ send_pc = "Done"
    /\ delete_pc = "Done"
    /\ UNCHANGED vars

BuggyNext ==
    \/ BuggySendGetRoot
    \/ BuggySendReadNode
    \/ BuggyDeleteTryDelete
    \/ BuggyDone

BuggyFairness ==
    /\ WF_vars(BuggySendGetRoot)
    /\ WF_vars(BuggySendReadNode)
    /\ WF_vars(BuggyDeleteTryDelete)

BuggySpec == Init /\ [][BuggyNext]_vars /\ BuggyFairness

(* ===========================================================================
 * FIXED VARIANT: Send increments send_in_progress before iterating.
 *                Delete checks send_in_progress and returns -EPERM if > 0.
 * =========================================================================== *)

\* Send increments send_in_progress, then gets root pointer (only if snapshot still valid)
FixedSendGetRoot ==
    /\ send_pc = "Init"
    /\ snapshot_state = "Valid"
    /\ send_in_progress' = send_in_progress + 1
    /\ send_pc' = "ReadNode"
    /\ UNCHANGED <<snapshot_state, delete_pc, crash_uaf>>

\* Send aborts if snapshot was already deleted before it could start
FixedSendAbort ==
    /\ send_pc = "Init"
    /\ snapshot_state = "Deleted"
    /\ send_pc' = "Done"
    /\ UNCHANGED <<snapshot_state, send_in_progress, delete_pc, crash_uaf>>

\* Send reads a node, then decrements send_in_progress
FixedSendReadNode ==
    /\ send_pc = "ReadNode"
    /\ crash_uaf' = IF snapshot_state = "Deleted" THEN TRUE ELSE crash_uaf
    /\ send_in_progress' = send_in_progress - 1
    /\ send_pc' = "Done"
    /\ UNCHANGED <<snapshot_state, delete_pc>>

\* Delete checks send_in_progress first
FixedDeleteTryDelete ==
    /\ delete_pc = "Init"
    /\ IF send_in_progress > 0
       THEN /\ delete_pc' = "Done"       \* Returns -EPERM, snapshot not deleted
            /\ UNCHANGED snapshot_state
       ELSE /\ snapshot_state' = "Deleted"
            /\ delete_pc' = "Done"
    /\ UNCHANGED <<send_in_progress, send_pc, crash_uaf>>

FixedDone ==
    /\ send_pc = "Done"
    /\ delete_pc = "Done"
    /\ UNCHANGED vars

FixedNext ==
    \/ FixedSendGetRoot
    \/ FixedSendAbort
    \/ FixedSendReadNode
    \/ FixedDeleteTryDelete
    \/ FixedDone

FixedFairness ==
    /\ WF_vars(FixedSendGetRoot)
    /\ WF_vars(FixedSendAbort)   \* Send must eventually abort if snapshot is already deleted
    /\ WF_vars(FixedSendReadNode)
    /\ WF_vars(FixedDeleteTryDelete)

FixedSpec == Init /\ [][FixedNext]_vars /\ FixedFairness

(* ===========================================================================
 * Invariants
 * =========================================================================== *)

NoUAF ==
    crash_uaf = FALSE

SendInProgressNonNegative ==
    send_in_progress >= 0

(* ===========================================================================
 * Liveness Properties (Track E)
 * =========================================================================== *)

\* Both operations eventually complete.
\* This proves the fix does not introduce a deadlock (e.g., delete doesn't wait
\* infinitely, it simply returns an error and finishes).
EventualCompletion ==
    <>(send_pc = "Done" /\ delete_pc = "Done")

==============================================================================
