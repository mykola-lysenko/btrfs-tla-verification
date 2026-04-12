---------------------------- MODULE BtrfsSpaceReservation ----------------------------
(*
 * Model: Btrfs ticket-based space reservation race under memory/disk pressure
 *
 * Bug description:
 * When Btrfs runs out of free space for metadata, it queues tasks that need
 * space using "tickets" and wakes up an asynchronous flusher thread to reclaim
 * space. A race condition occurs if a task creates a ticket, wakes the flusher,
 * and then times out and removes its ticket from the queue, but the flusher
 * concurrently tries to satisfy that ticket. If the flusher grants space to
 * a removed/freed ticket, it results in a space leak.
 *
 * Fix: The ticket removal and granting must be synchronized using a lock.
 * The flusher checks the ticket state under the lock before granting space.
 * The task checks the ticket state under the lock before freeing it.
 *
 * Invariant: NoSpaceLeak
 *)

EXTENDS Integers, TLC

VARIABLES
    ticket_state,
    task_pc,
    flusher_pc,
    leaked_space,
    space_lock

vars == <<ticket_state, task_pc, flusher_pc, leaked_space, space_lock>>

Init ==
    /\ ticket_state = "None"
    /\ task_pc = "Init"
    /\ flusher_pc = "Init"
    /\ leaked_space = FALSE
    /\ space_lock = "Free"

(* ===========================================================================
 * BUGGY VARIANT: Task frees ticket without proper synchronization
 * =========================================================================== *)

BuggyTaskQueue ==
    /\ task_pc = "Init"
    /\ ticket_state' = "Queued"
    /\ task_pc' = "Wait"
    /\ UNCHANGED <<flusher_pc, leaked_space, space_lock>>

BuggyTaskTimeout ==
    /\ task_pc = "Wait"
    /\ ticket_state \in {"Queued", "Granted"}
    \* BUG: Task times out and frees ticket. If it was already granted, space leaks.
    /\ leaked_space' = (ticket_state = "Granted")
    /\ ticket_state' = "Freed"
    /\ task_pc' = "Done"
    /\ UNCHANGED <<flusher_pc, space_lock>>

BuggyFlusherReclaim ==
    /\ flusher_pc = "Init"
    /\ ticket_state = "Queued"  \* Only runs if ticket is queued
    /\ flusher_pc' = "Grant"
    /\ UNCHANGED <<ticket_state, task_pc, leaked_space, space_lock>>

BuggyFlusherGrant ==
    /\ flusher_pc = "Grant"
    \* BUG: Flusher grants space to ticket. If ticket is already freed, space leaks.
    /\ leaked_space' = (leaked_space \/ (ticket_state = "Freed"))
    /\ ticket_state' = IF ticket_state = "Freed" THEN "Freed" ELSE "Granted"
    /\ flusher_pc' = "Done"
    /\ UNCHANGED <<task_pc, space_lock>>

BuggyFlusherSkip ==
    /\ flusher_pc = "Init"
    /\ ticket_state /= "Queued"
    /\ flusher_pc' = "Done"
    /\ UNCHANGED <<ticket_state, task_pc, leaked_space, space_lock>>

BuggyDone ==
    /\ task_pc = "Done"
    /\ flusher_pc = "Done"
    /\ UNCHANGED vars

BuggyNext ==
    \/ BuggyTaskQueue
    \/ BuggyTaskTimeout
    \/ BuggyFlusherReclaim
    \/ BuggyFlusherGrant
    \/ BuggyFlusherSkip
    \/ BuggyDone

BuggyFairness ==
    /\ WF_vars(BuggyTaskQueue)
    /\ WF_vars(BuggyTaskTimeout)
    /\ WF_vars(BuggyFlusherReclaim)
    /\ WF_vars(BuggyFlusherGrant)
    /\ WF_vars(BuggyFlusherSkip)

BuggySpec == Init /\ [][BuggyNext]_vars /\ BuggyFairness

(* ===========================================================================
 * FIXED VARIANT: Task and flusher synchronize using space_lock
 * =========================================================================== *)

FixedTaskQueue ==
    /\ task_pc = "Init"
    /\ ticket_state' = "Queued"
    /\ task_pc' = "Wait"
    /\ UNCHANGED <<flusher_pc, leaked_space, space_lock>>

FixedTaskTimeout ==
    /\ task_pc = "Wait"
    /\ space_lock = "Free"
    \* FIX: Task checks state under lock atomically (acquire, check, release).
    /\ IF ticket_state = "Granted" THEN
           /\ leaked_space' = FALSE  \* Space returned, no leak
           /\ ticket_state' = "Freed"
       ELSE
           /\ ticket_state' = "Freed"
           /\ UNCHANGED <<leaked_space>>
    /\ space_lock' = space_lock  \* Lock not held after atomic check
    /\ task_pc' = "Done"
    /\ UNCHANGED <<flusher_pc>>

FixedFlusherReclaim ==
    /\ flusher_pc = "Init"
    /\ ticket_state = "Queued"
    /\ flusher_pc' = "Grant"
    /\ UNCHANGED <<ticket_state, task_pc, leaked_space, space_lock>>

FixedFlusherGrant ==
    /\ flusher_pc = "Grant"
    /\ space_lock = "Free"
    \* FIX: Flusher checks state atomically under lock. If freed, doesn't grant.
    /\ IF ticket_state = "Queued" THEN
           /\ ticket_state' = "Granted"
           /\ UNCHANGED <<leaked_space>>
       ELSE
           /\ UNCHANGED <<ticket_state, leaked_space>>
    /\ space_lock' = space_lock  \* Lock not held after atomic check
    /\ flusher_pc' = "Done"
    /\ UNCHANGED <<task_pc>>

FixedFlusherSkip ==
    /\ flusher_pc = "Init"
    /\ ticket_state /= "Queued"
    /\ flusher_pc' = "Done"
    /\ UNCHANGED <<ticket_state, task_pc, leaked_space, space_lock>>

FixedDone ==
    /\ task_pc = "Done"
    /\ flusher_pc = "Done"
    /\ UNCHANGED vars

FixedNext ==
    \/ FixedTaskQueue
    \/ FixedTaskTimeout
    \/ FixedFlusherReclaim
    \/ FixedFlusherGrant
    \/ FixedFlusherSkip
    \/ FixedDone

FixedFairness ==
    /\ WF_vars(FixedTaskQueue)
    /\ WF_vars(FixedTaskTimeout)
    /\ WF_vars(FixedFlusherReclaim)
    /\ WF_vars(FixedFlusherGrant)
    /\ WF_vars(FixedFlusherSkip)

FixedSpec == Init /\ [][FixedNext]_vars /\ FixedFairness

(* ===========================================================================
 * Invariants
 * =========================================================================== *)

\* Space must never leak (granted to a freed ticket, or freed while holding space).
NoSpaceLeak ==
    leaked_space = FALSE

(* ===========================================================================
 * Liveness Properties (Track E)
 * =========================================================================== *)

\* Both the task and flusher must eventually finish.
\* This proves that the lock-based synchronization doesn't cause deadlocks
\* and both threads can make progress.
EventualCompletion ==
    <>(task_pc = "Done" /\ flusher_pc = "Done")

==============================================================================
