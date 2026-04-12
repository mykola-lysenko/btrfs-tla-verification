---- MODULE BtrfsFsyncLogTree ----
(*
 * Model: Btrfs Fsync Log Tree Race
 *
 * Bug description:
 * When an application calls fsync(), Btrfs writes the modified extents to a
 * separate log tree for fast commit. If multiple transactions are happening
 * concurrently, the log tree might be replayed incorrectly after a crash if
 * it contains mixed transactions without proper barriers.
 *
 * Fix: Btrfs uses log transaction IDs and synchronizes log commits with
 * main transaction commits to ensure ordering.
 *)

EXTENDS Integers, TLC

VARIABLES
    log_trans_id,
    main_trans_id,
    fsync_state,
    commit_state,
    crash_state

vars == <<log_trans_id, main_trans_id, fsync_state, commit_state, crash_state>>

Init ==
    /\ log_trans_id = 1
    /\ main_trans_id = 1
    /\ fsync_state = "Init"
    /\ commit_state = "Init"
    /\ crash_state = "None"

(* ===========================================================================
 * BUGGY VARIANT: Fsync doesn't wait for main transaction
 * =========================================================================== *)

BuggyFsync ==
    /\ fsync_state = "Init"
    /\ log_trans_id' = log_trans_id + 1
    /\ fsync_state' = "Done"
    /\ UNCHANGED <<main_trans_id, commit_state, crash_state>>

BuggyCommit ==
    /\ commit_state = "Init"
    /\ main_trans_id' = main_trans_id + 1
    /\ commit_state' = "Done"
    /\ UNCHANGED <<log_trans_id, fsync_state, crash_state>>

BuggyCrash ==
    /\ crash_state = "None"
    /\ fsync_state \in {"Done", "Init"}
    /\ commit_state \in {"Done", "Init"}
    /\ crash_state' = "Crashed"
    /\ UNCHANGED <<log_trans_id, main_trans_id, fsync_state, commit_state>>

BuggyDone ==
    /\ fsync_state = "Done"
    /\ commit_state = "Done"
    /\ UNCHANGED vars

BuggyNext ==
    \/ BuggyFsync
    \/ BuggyCommit
    \/ BuggyCrash
    \/ BuggyDone

BuggyFairness ==
    /\ WF_vars(BuggyFsync)
    /\ WF_vars(BuggyCommit)

BuggySpec == Init /\ [][BuggyNext]_vars /\ BuggyFairness

(* ===========================================================================
 * FIXED VARIANT: Fsync synchronizes with main transaction
 * =========================================================================== *)

FixedFsyncWait ==
    /\ fsync_state = "Init"
    /\ commit_state = "Done"  \* Must wait for main commit
    /\ log_trans_id' = log_trans_id + 1
    /\ fsync_state' = "Done"
    /\ UNCHANGED <<main_trans_id, commit_state, crash_state>>

FixedCommit ==
    /\ commit_state = "Init"
    /\ main_trans_id' = main_trans_id + 1
    /\ commit_state' = "Done"
    /\ UNCHANGED <<log_trans_id, fsync_state, crash_state>>

FixedCrash ==
    /\ crash_state = "None"
    /\ fsync_state \in {"Done", "Init"}
    /\ commit_state \in {"Done", "Init"}
    /\ crash_state' = "Crashed"
    /\ UNCHANGED <<log_trans_id, main_trans_id, fsync_state, commit_state>>

FixedDone ==
    /\ fsync_state = "Done"
    /\ commit_state = "Done"
    /\ UNCHANGED vars

FixedNext ==
    \/ FixedFsyncWait
    \/ FixedCommit
    \/ FixedCrash
    \/ FixedDone

FixedFairness ==
    /\ WF_vars(FixedFsyncWait)
    /\ WF_vars(FixedCommit)

FixedSpec == Init /\ [][FixedNext]_vars /\ FixedFairness

(* ===========================================================================
 * Invariants
 * =========================================================================== *)

\* If crashed, the log transaction ID shouldn't be ahead of the main transaction ID
\* unless it's properly synchronized. In the buggy variant, log_trans_id can be 2
\* while main_trans_id is 1.
ConsistentLog ==
    (crash_state = "Crashed") => (log_trans_id <= main_trans_id)

EventualCompletion ==
    <>( (fsync_state = "Done" /\ commit_state = "Done") \/ crash_state = "Crashed" )

=============================================================================
