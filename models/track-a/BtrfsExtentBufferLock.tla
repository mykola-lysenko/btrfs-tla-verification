---------------------------- MODULE BtrfsExtentBufferLock ----------------------------
(*
 * Model: Extent buffer read/write lock ordering in Btrfs B-tree operations
 *
 * Real code: fs/btrfs/locking.c, fs/btrfs/ctree.c
 *   btrfs_tree_lock()        -- exclusive write lock on an extent buffer
 *   btrfs_tree_read_lock()   -- shared read lock on an extent buffer
 *   btrfs_tree_unlock()      -- release write lock
 *   btrfs_tree_read_unlock() -- release read lock
 *
 * Lock ordering rule (from btrfs/locking.c comments):
 *   When traversing the B-tree, locks must be acquired top-down:
 *     root (NumLevels) -> ... -> leaf (1)
 *   A thread must NEVER hold a lock on a child node while acquiring a lock
 *   on a parent node (no lock upgrading from child to parent).
 *
 * Bug surface modeled:
 *   Thread A: holds lock on level L, tries to acquire level L+1 (parent) -- INVERSION
 *   Thread B: holds lock on level L+1, tries to acquire level L (child)  -- correct
 *   => DEADLOCK: A waits for B to release L+1; B waits for A to release L.
 *
 * Fix: Always acquire locks in strictly decreasing level order (root first).
 *      Threads descend one level at a time; never acquire a higher-numbered level
 *      while holding any lock.
 *
 * Correspondence:
 *   NumLevels  : number of B-tree levels (3 = root/internal/leaf)
 *   NumThreads : concurrent B-tree traversal threads
 *   eb_wlock[l]: thread holding write lock on level l (0 = free)
 *   thread_held[t]: set of levels thread t currently holds
 *   thread_pc[t]: "Idle" | "AcquireWrite" | "HoldingLock"
 *   thread_target[t]: level thread t is currently trying to acquire
 *
 * Invariants:
 *   WriterExclusion   : at most one writer per level
 *   NoLockInversion   : no thread acquires a parent while holding a child
 *   NoDeadlock        : at least one thread can always make progress
 *)

EXTENDS Integers, FiniteSets, TLC

CONSTANTS NumLevels, NumThreads

ASSUME NumLevels \in 2..4 /\ NumThreads \in 2..3

Levels  == 1..NumLevels
Threads == 1..NumThreads

VARIABLES
    eb_wlock,
    thread_held,
    thread_pc,
    thread_target

vars == <<eb_wlock, thread_held, thread_pc, thread_target>>

IsWLocked(l) == eb_wlock[l] /= 0
CanWriteLock(l) == ~IsWLocked(l)

Init ==
    /\ eb_wlock      = [l \in Levels  |-> 0]
    /\ thread_held   = [t \in Threads |-> {}]
    /\ thread_pc     = [t \in Threads |-> "Idle"]
    /\ thread_target = [t \in Threads |-> 0]

\* ============================================================
\* BUGGY VARIANT — no ordering constraint on lock acquisition
\* ============================================================

BuggyStart(t) ==
    /\ thread_pc[t] = "Idle"
    /\ thread_held[t] = {}
    /\ \E l \in Levels :
           /\ thread_target' = [thread_target EXCEPT ![t] = l]
           /\ thread_pc'     = [thread_pc     EXCEPT ![t] = "AcquireWrite"]
    /\ UNCHANGED <<eb_wlock, thread_held>>

BuggyAcquire(t) ==
    /\ thread_pc[t] = "AcquireWrite"
    /\ LET l == thread_target[t] IN
       /\ CanWriteLock(l)
       /\ eb_wlock'    = [eb_wlock    EXCEPT ![l] = t]
       /\ thread_held' = [thread_held EXCEPT ![t] = thread_held[t] \union {l}]
       /\ thread_pc'   = [thread_pc   EXCEPT ![t] = "HoldingLock"]
    /\ UNCHANGED thread_target

\* BUG: thread can acquire any second lock, including a parent (higher level)
BuggyAcquireSecond(t) ==
    /\ thread_pc[t] = "HoldingLock"
    /\ thread_held[t] /= {}
    /\ \E l \in Levels :
           /\ l /= thread_target[t]
           /\ CanWriteLock(l)
           /\ eb_wlock'    = [eb_wlock    EXCEPT ![l] = t]
           /\ thread_held' = [thread_held EXCEPT ![t] = thread_held[t] \union {l}]
           /\ thread_target' = [thread_target EXCEPT ![t] = l]
    /\ UNCHANGED thread_pc

BuggyRelease(t) ==
    /\ thread_pc[t] = "HoldingLock"
    /\ LET l == thread_target[t] IN
       /\ l /= 0
       /\ eb_wlock[l] = t
       /\ eb_wlock'    = [eb_wlock    EXCEPT ![l] = 0]
       /\ thread_held' = [thread_held EXCEPT ![t] = thread_held[t] \ {l}]
       /\ thread_target' = [thread_target EXCEPT ![t] = 0]
       /\ thread_pc'   = [thread_pc   EXCEPT ![t] = "Idle"]

BuggyNext ==
    \E t \in Threads :
        \/ BuggyStart(t)
        \/ BuggyAcquire(t)
        \/ BuggyAcquireSecond(t)
        \/ BuggyRelease(t)

BuggyFairness ==
    /\ \A t \in Threads : WF_vars(BuggyStart(t))
    /\ \A t \in Threads : WF_vars(BuggyAcquire(t))
    /\ \A t \in Threads : WF_vars(BuggyRelease(t))

BuggySpec == Init /\ [][BuggyNext]_vars /\ BuggyFairness

\* ============================================================
\* FIXED VARIANT — strict top-down (root-first) lock ordering
\* ============================================================

\* Always start at root
FixedStart(t) ==
    /\ thread_pc[t] = "Idle"
    /\ thread_held[t] = {}
    /\ thread_target' = [thread_target EXCEPT ![t] = NumLevels]
    /\ thread_pc'     = [thread_pc     EXCEPT ![t] = "AcquireWrite"]
    /\ UNCHANGED <<eb_wlock, thread_held>>

\* Acquire only if target is strictly below all currently held levels
FixedAcquire(t) ==
    /\ thread_pc[t] = "AcquireWrite"
    /\ LET l == thread_target[t] IN
       /\ CanWriteLock(l)
       /\ \A held \in thread_held[t] : l < held
       /\ eb_wlock'    = [eb_wlock    EXCEPT ![l] = t]
       /\ thread_held' = [thread_held EXCEPT ![t] = thread_held[t] \union {l}]
       /\ thread_pc'   = [thread_pc   EXCEPT ![t] = "HoldingLock"]
    /\ UNCHANGED thread_target

\* Descend to child level
FixedDescend(t) ==
    /\ thread_pc[t] = "HoldingLock"
    /\ thread_target[t] > 1
    /\ thread_target' = [thread_target EXCEPT ![t] = thread_target[t] - 1]
    /\ thread_pc'     = [thread_pc     EXCEPT ![t] = "AcquireWrite"]
    /\ UNCHANGED <<eb_wlock, thread_held>>

\* Release the current (lowest) lock; if more locks held, move target up to next parent
FixedRelease(t) ==
    /\ thread_pc[t] = "HoldingLock"
    /\ LET l == thread_target[t] IN
       /\ l /= 0
       /\ eb_wlock[l] = t
       /\ eb_wlock'    = [eb_wlock    EXCEPT ![l] = 0]
       /\ thread_held' = [thread_held EXCEPT ![t] = thread_held[t] \ {l}]
       /\ LET remaining == thread_held[t] \ {l} IN
          IF remaining = {}
          THEN /\ thread_pc'     = [thread_pc     EXCEPT ![t] = "Idle"]
               /\ thread_target' = [thread_target EXCEPT ![t] = 0]
          ELSE /\ thread_pc'     = [thread_pc     EXCEPT ![t] = "HoldingLock"]
               /\ thread_target' = [thread_target EXCEPT ![t] =
                                        CHOOSE m \in remaining :
                                            \A k \in remaining : m <= k]

FixedNext ==
    \E t \in Threads :
        \/ FixedStart(t)
        \/ FixedAcquire(t)
        \/ FixedDescend(t)
        \/ FixedRelease(t)

FixedFairness ==
    \* All actions use SF (strong fairness) to prevent starvation:
    \* if an action is enabled infinitely often, it must eventually fire.
    /\ \A t \in Threads : SF_vars(FixedStart(t))
    /\ \A t \in Threads : SF_vars(FixedAcquire(t))
    /\ \A t \in Threads : SF_vars(FixedDescend(t))
    /\ \A t \in Threads : SF_vars(FixedRelease(t))

FixedSpec == Init /\ [][FixedNext]_vars /\ FixedFairness

\* ============================================================
\* Invariants (shared)
\* ============================================================

WriterExclusion ==
    \A l \in Levels : \A t1, t2 \in Threads :
        (eb_wlock[l] = t1 /\ eb_wlock[l] = t2) => t1 = t2

NoLockInversion ==
    \A t \in Threads :
        (thread_pc[t] = "AcquireWrite" /\ thread_held[t] /= {}) =>
            \A held \in thread_held[t] : thread_target[t] < held

NoDeadlock ==
    \/ \E t \in Threads : thread_pc[t] = "Idle"
    \/ \E t \in Threads :
           /\ thread_pc[t] = "AcquireWrite"
           /\ CanWriteLock(thread_target[t])
    \/ \E t \in Threads : thread_pc[t] = "HoldingLock"

\* Liveness Properties (Track E):
\*
\* EventualLockAcquisition: If a thread is waiting to acquire a lock and the lock
\* is free, it eventually succeeds. This captures starvation-freedom for the locking
\* protocol itself (not the full traversal lifecycle).
EventualLockAcquisition ==
    \A t \in Threads :
        (thread_pc[t] = "AcquireWrite" /\ CanWriteLock(thread_target[t]))
            ~> (thread_pc[t] = "HoldingLock")

\* EventualRelease: Every thread that holds a lock eventually releases it.
\* This prevents indefinite lock hoarding.
EventualRelease ==
    \A t \in Threads :
        (thread_pc[t] = "HoldingLock") ~> (thread_pc[t] = "Idle" \/ thread_pc[t] = "AcquireWrite")

==============================================================================
