---- MODULE BtrfsExtentBufferLockConcrete ----
(*
 * Model: Concrete Btrfs Extent Buffer Lock
 *
 * This model is a more detailed, code-level representation of fs/btrfs/locking.c
 * It models the actual rw_semaphore operations and wait queues that implement
 * the abstract lock.
 *)

EXTENDS Integers, FiniteSets, Sequences, TLC

CONSTANTS NumLevels, NumThreads

ASSUME NumLevels \in 2..4 /\ NumThreads \in 2..3

Levels  == 1..NumLevels
Threads == 1..NumThreads

VARIABLES
    \* Concrete lock state for each level: 0 = free, t \in Threads = writer
    eb_lock_state,
    \* Wait queues for each lock: sequence of waiting threads
    eb_wait_queue,
    
    \* Thread local state
    thread_pc,
    thread_held,
    thread_target

vars == <<eb_lock_state, eb_wait_queue, thread_pc, thread_held, thread_target>>

Init ==
    /\ eb_lock_state = [l \in Levels |-> 0]
    /\ eb_wait_queue = [l \in Levels |-> <<>>]
    /\ thread_pc     = [t \in Threads |-> "Idle"]
    /\ thread_held   = [t \in Threads |-> {}]
    /\ thread_target = [t \in Threads |-> 0]

\* Btrfs btrfs_tree_lock() concrete implementation
\* Fast path: acquire if free
AcquireFast(t) ==
    /\ thread_pc[t] = "AcquireWrite"
    /\ LET l == thread_target[t] IN
       /\ \A held \in thread_held[t] : l < held
       /\ eb_lock_state[l] = 0
       /\ eb_wait_queue[l] = <<>>
       /\ eb_lock_state' = [eb_lock_state EXCEPT ![l] = t]
       /\ thread_held' = [thread_held EXCEPT ![t] = thread_held[t] \union {l}]
       /\ thread_pc' = [thread_pc EXCEPT ![t] = "HoldingLock"]
    /\ UNCHANGED <<eb_wait_queue, thread_target>>

\* Slow path: add to wait queue
AcquireSlowQueue(t) ==
    /\ thread_pc[t] = "AcquireWrite"
    /\ LET l == thread_target[t] IN
       /\ \A held \in thread_held[t] : l < held
       /\ \/ eb_lock_state[l] /= 0
          \/ eb_wait_queue[l] /= <<>>
       /\ eb_wait_queue' = [eb_wait_queue EXCEPT ![l] = Append(eb_wait_queue[l], t)]
       /\ thread_pc' = [thread_pc EXCEPT ![t] = "Waiting"]
    /\ UNCHANGED <<eb_lock_state, thread_held, thread_target>>

\* Slow path: wake up and acquire when it's our turn
AcquireSlowWake(t) ==
    /\ thread_pc[t] = "Waiting"
    /\ LET l == thread_target[t] IN
       /\ eb_lock_state[l] = 0
       /\ eb_wait_queue[l] /= <<>>
       /\ Head(eb_wait_queue[l]) = t
       /\ eb_lock_state' = [eb_lock_state EXCEPT ![l] = t]
       /\ eb_wait_queue' = [eb_wait_queue EXCEPT ![l] = Tail(eb_wait_queue[l])]
       /\ thread_held' = [thread_held EXCEPT ![t] = thread_held[t] \union {l}]
       /\ thread_pc' = [thread_pc EXCEPT ![t] = "HoldingLock"]
    /\ UNCHANGED thread_target

\* Start tree traversal at root
Start(t) ==
    /\ thread_pc[t] = "Idle"
    /\ thread_held[t] = {}
    /\ thread_target' = [thread_target EXCEPT ![t] = NumLevels]
    /\ thread_pc'     = [thread_pc EXCEPT ![t] = "AcquireWrite"]
    /\ UNCHANGED <<eb_lock_state, eb_wait_queue, thread_held>>

\* Descend to child level
Descend(t) ==
    /\ thread_pc[t] = "HoldingLock"
    /\ thread_target[t] > 1
    /\ thread_target' = [thread_target EXCEPT ![t] = thread_target[t] - 1]
    /\ thread_pc'     = [thread_pc EXCEPT ![t] = "AcquireWrite"]
    /\ UNCHANGED <<eb_lock_state, eb_wait_queue, thread_held>>

\* Release lock
Release(t) ==
    /\ thread_pc[t] = "HoldingLock"
    /\ LET l == thread_target[t] IN
       /\ l /= 0
       /\ eb_lock_state[l] = t
       /\ eb_lock_state' = [eb_lock_state EXCEPT ![l] = 0]
       /\ thread_held' = [thread_held EXCEPT ![t] = thread_held[t] \ {l}]
       /\ LET remaining == thread_held[t] \ {l} IN
          IF remaining = {}
          THEN /\ thread_pc'     = [thread_pc EXCEPT ![t] = "Idle"]
               /\ thread_target' = [thread_target EXCEPT ![t] = 0]
          ELSE /\ thread_pc'     = [thread_pc EXCEPT ![t] = "HoldingLock"]
               /\ thread_target' = [thread_target EXCEPT ![t] =
                                        CHOOSE m \in remaining :
                                            \A k \in remaining : m <= k]
    /\ UNCHANGED eb_wait_queue

Next ==
    \E t \in Threads :
        \/ Start(t)
        \/ AcquireFast(t)
        \/ AcquireSlowQueue(t)
        \/ AcquireSlowWake(t)
        \/ Descend(t)
        \/ Release(t)

Fairness ==
    /\ \A t \in Threads : SF_vars(Start(t))
    /\ \A t \in Threads : SF_vars(AcquireFast(t))
    /\ \A t \in Threads : SF_vars(AcquireSlowQueue(t))
    /\ \A t \in Threads : SF_vars(AcquireSlowWake(t))
    /\ \A t \in Threads : SF_vars(Descend(t))
    /\ \A t \in Threads : SF_vars(Release(t))

Spec == Init /\ [][Next]_vars /\ Fairness

=============================================================================
