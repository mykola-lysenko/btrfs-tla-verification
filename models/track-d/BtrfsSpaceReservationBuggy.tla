------------------------ MODULE BtrfsSpaceReservationBuggy ------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

(*
 * BtrfsSpaceReservation.tla
 * 
 * This model captures the core ticket-based space reservation system in btrfs,
 * specifically focusing on the interaction between:
 * 1. Normal priority tickets (e.g., data writes)
 * 2. High priority tickets (e.g., evict, limit, chunk allocation)
 * 3. The async flusher thread state machine
 * 4. The `try_granting_tickets` loop
 *
 * The goal is to find priority inversion, starvation, or deadlock scenarios
 * under ENOSPC conditions, as documented in fs/btrfs/space-info.c.
 *)

CONSTANTS
    TotalSpace,        \* Total metadata space available
    MaxTickets,        \* Maximum number of tickets to model
    Processes          \* Set of process IDs making reservations

VARIABLES
    space_used,        \* Currently used metadata space
    tickets,           \* Sequence of normal priority tickets (FIFO)
    priority_tickets,  \* Sequence of high priority tickets (FIFO)
    flusher_state,     \* State of the async flusher thread
    commit_cycles,     \* Number of full cycles the flusher has completed
    proc_state,        \* State of each process
    proc_ticket        \* The ticket (bytes) each process is waiting for

vars == <<space_used, tickets, priority_tickets, flusher_state, commit_cycles, proc_state, proc_ticket>>

\* Ticket types
Normal == "Normal"
Priority == "Priority"

\* Process states
Idle == "Idle"
Waiting == "Waiting"
Granted == "Granted"
Failed == "Failed"

\* Flusher states
FlusherIdle == "Idle"
FlushDelayedItems == "FlushDelayedItems"
FlushDelalloc == "FlushDelalloc"
FlushDelayedRefs == "FlushDelayedRefs"
AllocChunk == "AllocChunk"
CommitTrans == "CommitTrans"
FailTickets == "FailTickets"

-----------------------------------------------------------------------------

Init ==
    /\ space_used = 0
    /\ tickets = <<>>
    /\ priority_tickets = <<>>
    /\ flusher_state = FlusherIdle
    /\ commit_cycles = 0
    /\ proc_state = [p \in Processes |-> Idle]
    /\ proc_ticket = [p \in Processes |-> 0]

-----------------------------------------------------------------------------
\* HELPER MACROS
-----------------------------------------------------------------------------

\* In reality, btrfs_try_granting_tickets loops through priority_tickets first, then tickets.
\* For TLA+, we model this as a single atomic step that grants as many tickets as possible
\* from the front of the queues.

RECURSIVE GrantTickets(_, _, _)
GrantTickets(used, prio_q, norm_q) ==
    IF prio_q /= <<>> /\ used + Head(prio_q).bytes <= TotalSpace THEN
        \* Grant from priority queue
        GrantTickets(used + Head(prio_q).bytes, Tail(prio_q), norm_q)
    ELSE IF prio_q = <<>> /\ norm_q /= <<>> /\ used + Head(norm_q).bytes <= TotalSpace THEN
        \* Grant from normal queue only if priority queue is empty
        GrantTickets(used + Head(norm_q).bytes, prio_q, Tail(norm_q))
    ELSE
        \* Cannot grant any more tickets
        <<used, prio_q, norm_q>>

TryGrantingTickets ==
    LET result == GrantTickets(space_used, priority_tickets, tickets) IN
    /\ space_used' = result[1]
    /\ priority_tickets' = result[2]
    /\ tickets' = result[3]
    \* Update process states for granted tickets
    /\ proc_state' = [p \in Processes |-> 
        IF proc_state[p] = Waiting THEN
            IF \E i \in 1..Len(priority_tickets'): priority_tickets'[i].proc = p THEN Waiting
            ELSE IF \E i \in 1..Len(tickets'): tickets'[i].proc = p THEN Waiting
            ELSE Granted
        ELSE proc_state[p]]

-----------------------------------------------------------------------------
\* PROCESS ACTIONS
-----------------------------------------------------------------------------

ReserveNormal(p, bytes) ==
    /\ proc_state[p] = Idle
    /\ Len(tickets) + Len(priority_tickets) < MaxTickets
    /\ proc_ticket' = [proc_ticket EXCEPT ![p] = bytes]
    /\ IF space_used + bytes <= TotalSpace THEN
           \* Fast path success
           /\ space_used' = space_used + bytes
           /\ proc_state' = [proc_state EXCEPT ![p] = Granted]
           /\ UNCHANGED <<tickets, priority_tickets, flusher_state, commit_cycles>>
       ELSE
           \* ENOSPC, add to normal tickets queue
           /\ tickets' = Append(tickets, [proc |-> p, bytes |-> bytes, type |-> Normal])
           /\ proc_state' = [proc_state EXCEPT ![p] = Waiting]
           \* Wake up flusher if idle
           /\ flusher_state' = IF flusher_state = FlusherIdle THEN FlushDelayedItems ELSE flusher_state
           /\ UNCHANGED <<space_used, priority_tickets, commit_cycles>>

ReservePriority(p, bytes) ==
    /\ proc_state[p] = Idle
    /\ Len(tickets) + Len(priority_tickets) < MaxTickets
    /\ proc_ticket' = [proc_ticket EXCEPT ![p] = bytes]
    /\ IF space_used + bytes <= TotalSpace THEN
           \* Fast path success
           /\ space_used' = space_used + bytes
           /\ proc_state' = [proc_state EXCEPT ![p] = Granted]
           /\ UNCHANGED <<tickets, priority_tickets, flusher_state, commit_cycles>>
       ELSE
           \* ENOSPC, add to priority tickets queue
           /\ priority_tickets' = Append(priority_tickets, [proc |-> p, bytes |-> bytes, type |-> Priority])
           /\ proc_state' = [proc_state EXCEPT ![p] = Waiting]
           \* BUG: Doesn't wake up flusher if idle
           /\ flusher_state' = flusher_state \* Bug: No wake up
           /\ UNCHANGED <<space_used, tickets, commit_cycles>>

\* A process finishes its work and frees the space
FreeSpace(p) ==
    /\ proc_state[p] = Granted
    /\ space_used' = space_used - proc_ticket[p]
    /\ proc_state' = [proc_state EXCEPT ![p] = Idle]
    /\ proc_ticket' = [proc_ticket EXCEPT ![p] = 0]
    /\ UNCHANGED <<flusher_state, commit_cycles>>
    \* After freeing space, try granting tickets
    /\ TryGrantingTickets

FailSpace(p) ==
    /\ proc_state[p] = Failed
    /\ proc_state' = [proc_state EXCEPT ![p] = Idle]
    /\ proc_ticket' = [proc_ticket EXCEPT ![p] = 0]
    /\ UNCHANGED <<space_used, tickets, priority_tickets, flusher_state, commit_cycles>>

-----------------------------------------------------------------------------
\* FLUSHER ACTIONS
-----------------------------------------------------------------------------

\* The flusher progresses through states, freeing up space.
\* For modeling, we assume each state *might* free some space.

FlusherProgress(next_state, space_freed) ==
    /\ space_used' = space_used - space_freed
    /\ flusher_state' = next_state
    /\ UNCHANGED <<commit_cycles, proc_ticket>>
    /\ TryGrantingTickets

\* Flusher_Stuck is a workaround for the correct model. In the buggy model, we omit it.

Flusher_IdleWakeup ==
    /\ flusher_state = FlusherIdle
    /\ tickets /= <<>> \* BUG: Flusher doesn't wake up for priority tickets
    /\ flusher_state' = FlushDelayedItems
    /\ UNCHANGED <<space_used, tickets, priority_tickets, commit_cycles, proc_state, proc_ticket>>

Flusher_FlushDelayedItems ==
    /\ flusher_state = FlushDelayedItems
    \* Assume it frees 1 unit of space if possible
    /\ FlusherProgress(FlushDelalloc, IF space_used > 0 THEN 1 ELSE 0)

Flusher_FlushDelalloc ==
    /\ flusher_state = FlushDelalloc
    /\ FlusherProgress(FlushDelayedRefs, IF space_used > 0 THEN 1 ELSE 0)

Flusher_FlushDelayedRefs ==
    /\ flusher_state = FlushDelayedRefs
    /\ FlusherProgress(AllocChunk, IF space_used > 0 THEN 1 ELSE 0)

Flusher_AllocChunk ==
    /\ flusher_state = AllocChunk
    \* Allocating a chunk increases TotalSpace, but for a bounded model we just free space
    /\ FlusherProgress(CommitTrans, IF space_used > 0 THEN 1 ELSE 0)

Flusher_CommitTrans ==
    /\ flusher_state = CommitTrans
    /\ IF tickets = <<>> /\ priority_tickets = <<>> THEN
           \* All tickets satisfied, go idle
           /\ flusher_state' = FlusherIdle
           /\ commit_cycles' = 0
           /\ UNCHANGED <<space_used, tickets, priority_tickets, proc_state, proc_ticket>>
       ELSE
           \* Still have tickets, increment commit cycles
           /\ commit_cycles' = commit_cycles + 1
           /\ IF commit_cycles >= 2 THEN
                  \* Exhausted flushing, fail tickets
                  /\ flusher_state' = FailTickets
                  /\ UNCHANGED <<space_used, tickets, priority_tickets, proc_state, proc_ticket>>
              ELSE
                  \* Loop back
                  /\ flusher_state' = FlushDelayedItems
                  /\ UNCHANGED <<space_used, tickets, priority_tickets, proc_state, proc_ticket>>

Flusher_FailTickets ==
    /\ flusher_state = FailTickets
    \* maybe_fail_all_tickets fails the first normal ticket to make progress
    /\ IF tickets /= <<>> THEN
           LET failed_ticket == Head(tickets) IN
           /\ tickets' = Tail(tickets)
           /\ proc_state' = [proc_state EXCEPT ![failed_ticket.proc] = Failed]
           /\ flusher_state' = FlushDelayedItems
           /\ commit_cycles' = commit_cycles - 1
           /\ UNCHANGED <<space_used, priority_tickets, proc_ticket>>
       ELSE IF priority_tickets /= <<>> THEN
           \* BUGGY VERSION: The flusher goes idle when only priority tickets remain,
           \* failing to make progress on them or fail them, leading to a deadlock.
           /\ flusher_state' = FlusherIdle
           /\ commit_cycles' = 0
           /\ UNCHANGED <<space_used, tickets, priority_tickets, proc_state, proc_ticket>>
       ELSE
           /\ flusher_state' = FlusherIdle
           /\ commit_cycles' = 0
           /\ UNCHANGED <<space_used, tickets, priority_tickets, proc_state, proc_ticket>>

-----------------------------------------------------------------------------

Terminal ==
    /\ \A p \in Processes: proc_state[p] \in {Idle, Granted, Failed}
    /\ flusher_state \in {FlusherIdle, FlushDelayedItems}
    /\ tickets = <<>>
    /\ priority_tickets = <<>>
    /\ UNCHANGED vars

Next ==
    \/ \E p \in Processes:
        \/ ReserveNormal(p, 2)
        \/ ReservePriority(p, 1)
        \/ FreeSpace(p)
        \/ FailSpace(p)
    \/ Flusher_FlushDelayedItems
    \/ Flusher_FlushDelalloc
    \/ Flusher_FlushDelayedRefs
    \/ Flusher_AllocChunk
    \/ Flusher_CommitTrans
    \/ Flusher_FailTickets
    \/ Flusher_IdleWakeup
    \/ Terminal

Fairness == 
    /\ \A p \in Processes: WF_vars(ReserveNormal(p, 2))
    /\ \A p \in Processes: WF_vars(ReservePriority(p, 1))
    /\ \A p \in Processes: SF_vars(FreeSpace(p))
    /\ \A p \in Processes: WF_vars(FailSpace(p))
    /\ WF_vars(Flusher_FlushDelayedItems)
    /\ WF_vars(Flusher_FlushDelalloc)
    /\ WF_vars(Flusher_FlushDelayedRefs)
    /\ WF_vars(Flusher_AllocChunk)
    /\ WF_vars(Flusher_CommitTrans)
    /\ WF_vars(Flusher_FailTickets)
    /\ WF_vars(Flusher_IdleWakeup)
    /\ WF_vars(Terminal)

Spec == Init /\ [][Next]_vars /\ Fairness /\ WF_vars(Next)

-----------------------------------------------------------------------------
\* PROPERTIES
-----------------------------------------------------------------------------

\* Safety: Space used never exceeds total space
SpaceAccountingCorrect == space_used <= TotalSpace

\* Liveness: If a process is waiting, it eventually gets granted or failed
\* This is the starvation/deadlock check.
\* We want to check for deadlocks and starvation under weak fairness.
\* If processes and the flusher are continually given a chance to run, does waiting eventually end?
\* The stuttering happens because the processes with granted tickets never free them,
\* so the waiting process starves. We must enforce that processes eventually free their space!
FairFreeSpace == \A p \in Processes: WF_vars(FreeSpace(p))

\* To find the bug, we write a safety invariant that asserts we never reach the deadlock state
NoPriorityDeadlock == ~(flusher_state = FlusherIdle /\ priority_tickets /= <<>> /\ tickets = <<>>)

=============================================================================
