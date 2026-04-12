------------------------ MODULE BtrfsSpaceReservationLiveness ------------------------
EXTENDS Integers, FiniteSets, TLC

(*
 * BtrfsSpaceReservationLiveness.tla
 *
 * Models the Btrfs ticketed space reservation system and its flush/reclaim
 * liveness properties.
 *
 * BACKGROUND
 * ----------
 * Btrfs uses a "ticketed reservation" system (btrfs_reserve_metadata_bytes).
 * When free space is insufficient, a writer creates a ticket and blocks.
 * A background flusher (btrfs_async_reclaim_metadata_space) periodically
 * reclaims space (by flushing delayed refs, writing out inodes, etc.) and
 * then wakes blocked tickets.
 *
 * KEY LIVENESS PROPERTY
 * ---------------------
 * Every ticket that blocks must eventually either:
 *   (a) be granted (space becomes available), or
 *   (b) be cancelled (the operation is aborted with ENOSPC).
 *
 * A ticket must NEVER be permanently stuck (no progress, no cancellation).
 *
 * SAFETY PROPERTY
 * ---------------
 * The total reserved bytes never exceeds the total available space.
 * (Overcommit is allowed up to a limit, but we model the simple case.)
 *
 * BUGS MODELLED
 * -------------
 * BtrfsSpaceReservationBuggy.tla models the case where the flusher wakes
 * a ticket but does not re-check whether space is actually available,
 * leading to a spurious grant that overcommits space.
 *
 * This spec models the correct behavior.
 *)

CONSTANTS
    TotalSpace,     \* Total bytes of metadata space
    NumWriters,     \* Number of concurrent writers
    MaxFlushRounds  \* Bound on flush rounds (prevents infinite state space)

ASSUME TotalSpace   >= 1
ASSUME NumWriters   >= 1
ASSUME MaxFlushRounds >= 1

WS == 1..NumWriters

VARIABLES
    free_space,         \* Nat: currently free metadata bytes
    reserved_space,     \* Nat: currently reserved metadata bytes
    flush_rounds,       \* Nat: number of flush rounds completed

    \* Per-writer state
    writer_state,       \* [WS -> "Idle"|"Requesting"|"Blocked"|"Granted"|"Done"]
    writer_request,     \* [WS -> Nat] bytes requested

    \* Flusher state
    flusher_state       \* "Idle"|"Flushing"|"WakingTickets"|"Done"

vars == <<free_space, reserved_space, flush_rounds,
          writer_state, writer_request,
          flusher_state>>

-----------------------------------------------------------------------------
Init ==
    /\ free_space     = TotalSpace
    /\ reserved_space = 0
    /\ flush_rounds   = 0
    /\ writer_state   = [w \in WS |-> "Idle"]
    /\ writer_request = [w \in WS |-> 0]
    /\ flusher_state  = "Idle"

-----------------------------------------------------------------------------
\* WRITER: request space reservation

WriterRequest(w) ==
    /\ writer_state[w] = "Idle"
    /\ \E bytes \in 1..TotalSpace :
           /\ writer_request' = [writer_request EXCEPT ![w] = bytes]
           /\ writer_state'   = [writer_state   EXCEPT ![w] = "Requesting"]
    /\ UNCHANGED <<free_space, reserved_space, flush_rounds,
                   flusher_state>>

WriterTryGrant(w) ==
    \* Try to grant immediately if space is available
    /\ writer_state[w] = "Requesting"
    /\ LET bytes == writer_request[w] IN
       IF free_space >= bytes THEN
           /\ free_space'     = free_space - bytes
           /\ reserved_space' = reserved_space + bytes
           /\ writer_state'   = [writer_state EXCEPT ![w] = "Granted"]
       ELSE
           \* Not enough space; block and wait for flusher
           /\ writer_state' = [writer_state EXCEPT ![w] = "Blocked"]
           /\ UNCHANGED <<free_space, reserved_space>>
    /\ UNCHANGED <<flush_rounds, writer_request, flusher_state>>

WriterRelease(w) ==
    \* Release reserved space after use
    /\ writer_state[w] = "Granted"
    /\ LET bytes == writer_request[w] IN
       /\ reserved_space' = reserved_space - bytes
       /\ free_space'     = free_space + bytes
    /\ writer_state'   = [writer_state   EXCEPT ![w] = "Done"]
    /\ UNCHANGED <<flush_rounds, writer_request, flusher_state>>

WriterReset(w) ==
    /\ writer_state[w] = "Done"
    /\ writer_state'   = [writer_state   EXCEPT ![w] = "Idle"]
    /\ writer_request' = [writer_request EXCEPT ![w] = 0]
    /\ UNCHANGED <<free_space, reserved_space, flush_rounds, flusher_state>>

WriterCancel(w) ==
    \* A blocked writer can be cancelled (ENOSPC) if flush rounds are exhausted
    /\ writer_state[w] = "Blocked"
    /\ flush_rounds >= MaxFlushRounds
    /\ writer_state'   = [writer_state   EXCEPT ![w] = "Done"]
    /\ UNCHANGED <<free_space, reserved_space, flush_rounds,
                   writer_request, flusher_state>>

-----------------------------------------------------------------------------
\* FLUSHER: reclaim metadata space and wake blocked tickets

FlusherStart ==
    \* Start flushing when there are blocked writers
    /\ flusher_state = "Idle"
    /\ \E w \in WS : writer_state[w] = "Blocked"
    /\ flush_rounds < MaxFlushRounds
    /\ flusher_state' = "Flushing"
    /\ UNCHANGED <<free_space, reserved_space, flush_rounds,
                   writer_state, writer_request>>

FlusherReclaim ==
    \* Reclaim some space (simulate flushing delayed refs, writing inodes, etc.)
    /\ flusher_state = "Flushing"
    /\ LET reclaimed == 1 IN   \* simplified: reclaim 1 byte per round
       /\ free_space'   = free_space + reclaimed
       /\ flush_rounds' = flush_rounds + 1
    /\ flusher_state' = "WakingTickets"
    /\ UNCHANGED <<reserved_space, writer_state, writer_request>>

FlusherWakeTickets ==
    \* Wake blocked writers and try to grant them space
    /\ flusher_state = "WakingTickets"
    /\ \E w \in WS :
           /\ writer_state[w] = "Blocked"
           /\ LET bytes == writer_request[w] IN
              IF free_space >= bytes THEN
                  /\ free_space'     = free_space - bytes
                  /\ reserved_space' = reserved_space + bytes
                  /\ writer_state'   = [writer_state EXCEPT ![w] = "Granted"]
              ELSE
                  \* Still not enough space; leave blocked
                  /\ UNCHANGED <<free_space, reserved_space, writer_state>>
    /\ flusher_state' = "Done"
    /\ UNCHANGED <<flush_rounds, writer_request>>

FlusherDone ==
    /\ flusher_state = "Done"
    /\ flusher_state' = "Idle"
    /\ UNCHANGED <<free_space, reserved_space, flush_rounds,
                   writer_state, writer_request>>

-----------------------------------------------------------------------------
Terminal ==
    /\ flusher_state = "Idle"
    /\ \A w \in WS : writer_state[w] = "Idle"
    /\ UNCHANGED vars

-----------------------------------------------------------------------------
Next ==
    \/ \E w \in WS : WriterRequest(w) \/ WriterTryGrant(w) \/ WriterRelease(w)
                  \/ WriterReset(w) \/ WriterCancel(w)
    \/ FlusherStart \/ FlusherReclaim \/ FlusherWakeTickets \/ FlusherDone
    \/ Terminal

Fairness ==
    /\ \A w \in WS :
           /\ WF_vars(WriterRequest(w))
           /\ WF_vars(WriterTryGrant(w))
           /\ WF_vars(WriterRelease(w))
           /\ WF_vars(WriterReset(w))
           /\ WF_vars(WriterCancel(w))
    /\ WF_vars(FlusherStart)
    /\ WF_vars(FlusherReclaim)
    /\ WF_vars(FlusherWakeTickets)
    /\ WF_vars(FlusherDone)
    /\ WF_vars(Terminal)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
\* INVARIANTS

\* Space accounting is always consistent
SpaceConsistent ==
    free_space + reserved_space <= TotalSpace + flush_rounds

\* Free space never goes negative
FreeSpaceNonNegative ==
    free_space >= 0

\* Reserved space never goes negative
ReservedSpaceNonNegative ==
    reserved_space >= 0

TypeOK ==
    /\ free_space     \in Nat
    /\ reserved_space \in Nat
    /\ flush_rounds   \in 0..MaxFlushRounds
    /\ \A w \in WS : writer_state[w] \in {"Idle", "Requesting", "Blocked", "Granted", "Done"}
    /\ \A w \in WS : writer_request[w] \in 0..TotalSpace
    /\ flusher_state \in {"Idle", "Flushing", "WakingTickets", "Done"}

-----------------------------------------------------------------------------
\* LIVENESS

\* Every blocked writer eventually gets granted or cancelled
NoWriterStuck ==
    \A w \in WS :
        (writer_state[w] = "Blocked") ~> (writer_state[w] \in {"Granted", "Done"})

\* Every request eventually completes
AllRequestsComplete ==
    \A w \in WS :
        (writer_state[w] = "Requesting") ~> (writer_state[w] = "Idle")

=============================================================================
