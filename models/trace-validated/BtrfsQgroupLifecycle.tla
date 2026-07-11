------------------------- MODULE BtrfsQgroupLifecycle -------------------------
(***************************************************************************)
(* Faithful model of the btrfs qgroup enable / disable / rescan lifecycle, *)
(* extracted from fs/btrfs/qgroup.c + ioctl.c of btrfs-devel for-next      *)
(* ("7.1.0-rc7", which contains the CVE-2025-39759 fix).                   *)
(*                                                                         *)
(* Unlike the earlier models in models/track-c (which encode the UAF as a  *)
(* state flag by construction), this model encodes the kernel's actual     *)
(* lock discipline and control flow; the UAF *emerges* from the            *)
(* interleaving when the fix is absent.                                    *)
(*                                                                         *)
(* Kernel facts modeled (with source locations, 7.1-rc7):                  *)
(*   - quota enable/disable run under down_write(&subvol_sem)              *)
(*     (btrfs_ioctl_quota_ctl, ioctl.c:3563-3600) -> mutually exclusive.   *)
(*   - the rescan ioctl (btrfs_ioctl_quota_rescan -> btrfs_qgroup_rescan)  *)
(*     does NOT take subvol_sem -> races with enable/disable.              *)
(*   - btrfs_quota_enable (qgroup.c:1050-1300): creates quota root, sets   *)
(*     quota_root + QUOTA_ENABLED under qgroup_lock, then                  *)
(*     qgroup_rescan_init (sets FLAG_RESCAN, resets completion, under      *)
(*     qgroup_rescan_lock), qgroup_rescan_zero_tracking (iterates          *)
(*     qgroup_tree under qgroup_lock), sets rescan_running, queues worker. *)
(*   - btrfs_qgroup_rescan (qgroup.c:4047): rescan_init -> commit          *)
(*     transaction (a WIDE window with FLAG_RESCAN set but                 *)
(*     rescan_running still false!) -> zero_tracking -> under rescan_lock  *)
(*     sets rescan_running and queues the worker.                          *)
(*   - btrfs_quota_disable (qgroup.c:1332): clears QUOTA_ENABLED, then     *)
(*     btrfs_qgroup_wait_for_completion (returns immediately if            *)
(*     rescan_running is false!), then clears quota_root + FLAG_ON under   *)
(*     qgroup_lock, then btrfs_free_qgroup_config frees every qgroup       *)
(*     record. The CVE-2025-39759 fix makes the free loop hold             *)
(*     qgroup_lock (qgroup.c:677); before the fix it iterated bare.        *)
(*   - btrfs_qgroup_rescan_worker (qgroup.c:3852): scans while             *)
(*     rescan_should_stop() is false (it stops when QUOTA_ENABLED is       *)
(*     cleared OR the fs is closing), then under rescan_lock clears        *)
(*     FLAG_RESCAN (only if not stopped), clears rescan_running,           *)
(*     complete_all(completion).                                           *)
(*   - close_ctree (unmount, disk-io.c): sets BTRFS_FS_CLOSING, calls      *)
(*     btrfs_qgroup_wait_for_completion, later btrfs_free_qgroup_config —  *)
(*     unconditionally, even if quota was never enabled. The freed fs_info *)
(*     means a subsequent mount starts from fresh in-memory state. VFS     *)
(*     guarantees no quota ioctl is in flight once umount proceeds (open   *)
(*     fds make umount fail with EBUSY before close_ctree runs).           *)
(*   - the standalone btrfs_qgroup_wait_for_completion callers (the        *)
(*     rescan-wait ioctl and close_ctree) are out-of-TU, so their kprobe   *)
(*     fires: WaitRescanCompletion_* is observable there; the copy inlined *)
(*     into btrfs_quota_disable emits nothing and stays internal.          *)
(*                                                                         *)
(* The CVE-2025-39759 race this model reproduces when                      *)
(* FixFreeHoldsQgroupLock = FALSE:                                         *)
(*   rescan ioctl: rescan_init sets FLAG_RESCAN, parks in the              *)
(*     transaction-commit window (rescan_running still FALSE);             *)
(*   disable: wait_for_completion sees rescan_running == FALSE and sails   *)
(*     through; frees the qgroup records WITHOUT qgroup_lock;              *)
(*   rescan ioctl: zero_tracking iterates the tree (under qgroup_lock)     *)
(*     while/after the records are freed under it -> use-after-free.       *)
(*                                                                         *)
(* Observable actions carry the exact names emitted by                     *)
(* tracing/bpftrace/btrfs_qgroup.bt so real traces can be validated        *)
(* against this spec (see BtrfsQgroupTrace.tla).                           *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    UserTasks,              \* user threads issuing quota ioctls
    FixFreeHoldsQgroupLock  \* TRUE: kernel with the CVE-2025-39759 fix

Worker == "worker"          \* the single qgroup_rescan_work item
Tasks  == UserTasks \cup {Worker}
NoTask == "none"

VARIABLES
    quotaRoot,      \* fs_info->quota_root != NULL
    quotaEnabled,   \* BTRFS_FS_QUOTA_ENABLED bit
    flagOn,         \* BTRFS_QGROUP_STATUS_FLAG_ON
    flagRescan,     \* BTRFS_QGROUP_STATUS_FLAG_RESCAN
    rescanRunning,  \* fs_info->qgroup_rescan_running
    completionDone, \* qgroup_rescan_completion (complete_all sticky, reset by init_completion)
    workerQueued,   \* qgroup_rescan_work queued but not yet executing
    workerStopped,  \* the worker's local `stopped` (rescan_should_stop() at loop exit)
    qgroupLock,     \* fs_info->qgroup_lock  (spinlock)  : NoTask or holder
    rescanLock,     \* fs_info->qgroup_rescan_lock (mutex): NoTask or holder
    subvolSem,      \* fs_info->subvol_sem (write)       : NoTask or holder
    iterating,      \* tasks holding a live pointer into qgroup_tree (zero_tracking loop)
    uafOccurred,    \* set when records are freed under an active iterator
    pc              \* program counter per task

vars == <<quotaRoot, quotaEnabled, flagOn, flagRescan, rescanRunning,
          completionDone, workerQueued, workerStopped, qgroupLock, rescanLock,
          subvolSem, iterating, uafOccurred, pc>>

UserPCs == {"idle",
            \* btrfs_quota_enable
            "e_check", "e_create", "e_setroot", "e_rescaninit",
            "e_zt_enter", "e_zt_iter", "e_zt_done", "e_queue", "e_done",
            \* btrfs_quota_disable
            "d_check", "d_clear_enabled", "d_wait_enter", "d_wait_read",
            "d_wait_block", "d_wait_done", "d_trans", "d_clear_root",
            "d_free_enter", "d_free_lock", "d_free_do", "d_free_done",
            "d_clean", "d_done",
            \* btrfs_qgroup_rescan (rescan ioctl)
            "r_init", "r_commit", "r_zt_enter", "r_zt_iter", "r_zt_done",
            "r_queue", "r_done",
            \* standalone btrfs_qgroup_wait_for_completion (rescan -w etc.)
            "u_wait_read", "u_wait_block", "u_wait_done",
            \* close_ctree (unmount): wait, free config, teardown
            "m_wait_read", "m_wait_block", "m_wait_done",
            "m_free_enter", "m_free_lock", "m_free_do", "m_free_done"}
WorkerPCs == {"w_idle", "w_run", "w_finish", "w_exit"}

\* A task inside the unmount path = BTRFS_FS_CLOSING is set (close_ctree
\* sets it before the qgroup teardown steps modeled here).
MStates  == {"m_wait_read", "m_wait_block", "m_wait_done",
             "m_free_enter", "m_free_lock", "m_free_do", "m_free_done"}
Closing  == \E t \in Tasks : pc[t] \in MStates

TypeOK ==
    /\ quotaRoot \in BOOLEAN /\ quotaEnabled \in BOOLEAN
    /\ flagOn \in BOOLEAN /\ flagRescan \in BOOLEAN
    /\ rescanRunning \in BOOLEAN /\ completionDone \in BOOLEAN
    /\ workerQueued \in BOOLEAN /\ workerStopped \in BOOLEAN
    /\ qgroupLock \in Tasks \cup {NoTask}
    /\ rescanLock \in Tasks \cup {NoTask}
    /\ subvolSem \in Tasks \cup {NoTask}
    /\ iterating \subseteq Tasks
    /\ uafOccurred \in BOOLEAN
    /\ pc \in [Tasks -> UserPCs \cup WorkerPCs]

Init ==
    /\ quotaRoot = FALSE /\ quotaEnabled = FALSE
    /\ flagOn = FALSE /\ flagRescan = FALSE
    /\ rescanRunning = FALSE /\ completionDone = FALSE
    /\ workerQueued = FALSE /\ workerStopped = FALSE
    /\ qgroupLock = NoTask /\ rescanLock = NoTask /\ subvolSem = NoTask
    /\ iterating = {} /\ uafOccurred = FALSE
    /\ pc = [t \in Tasks |-> IF t = Worker THEN "w_idle" ELSE "idle"]

(***************************************************************************)
(* btrfs_quota_enable — under subvol_sem (taken in the ioctl wrapper       *)
(* before the function is entered, so the Enter event follows the sem).   *)
(***************************************************************************)

QuotaEnableEnter(t) ==      \* observable: QuotaEnable_Enter
    /\ t \in UserTasks /\ pc[t] = "idle" /\ subvolSem = NoTask
    /\ ~Closing              \* an in-flight ioctl fd would have failed umount
    /\ subvolSem' = t
    /\ pc' = [pc EXCEPT ![t] = "e_check"]
    /\ UNCHANGED <<quotaRoot, quotaEnabled, flagOn, flagRescan, rescanRunning,
                   completionDone, workerQueued, workerStopped, qgroupLock,
                   rescanLock, iterating, uafOccurred>>

E_Check(t) ==               \* internal: if (fs_info->quota_root) goto out
    /\ pc[t] = "e_check"
    /\ pc' = [pc EXCEPT ![t] = IF quotaRoot THEN "e_done" ELSE "e_create"]
    /\ UNCHANGED <<quotaRoot, quotaEnabled, flagOn, flagRescan, rescanRunning,
                   completionDone, workerQueued, workerStopped, qgroupLock,
                   rescanLock, subvolSem, iterating, uafOccurred>>

E_Create(t) ==              \* internal: create quota tree inside the enable
                            \* transaction. qgroup.c:1104 OVERWRITES
                            \* qgroup_flags = FLAG_ON, clearing a stale
                            \* FLAG_RESCAN left by a scan paused mid-disable.
                            \* Note the real window this opens: flagOn is set
                            \* here but quota_root only after the commit.
    /\ pc[t] = "e_create"
    /\ flagOn' = TRUE /\ flagRescan' = FALSE
    /\ pc' = [pc EXCEPT ![t] = "e_setroot"]
    /\ UNCHANGED <<quotaRoot, quotaEnabled, rescanRunning,
                   completionDone, workerQueued, workerStopped, qgroupLock,
                   rescanLock, subvolSem, iterating, uafOccurred>>

E_SetRoot(t) ==             \* internal: qgroup.c:1254-1259, under qgroup_lock
    /\ pc[t] = "e_setroot" /\ qgroupLock = NoTask
    /\ quotaRoot' = TRUE /\ quotaEnabled' = TRUE
    /\ pc' = [pc EXCEPT ![t] = "e_rescaninit"]
    /\ UNCHANGED <<flagOn, flagRescan, rescanRunning, completionDone,
                   workerQueued, workerStopped, qgroupLock, rescanLock,
                   subvolSem, iterating, uafOccurred>>

E_SimpleSkip(t) ==          \* internal: simple-quotas enable (squota,
                            \* BTRFS_QUOTA_CTL_ENABLE_SIMPLE_QUOTA) skips the
                            \* rescan machinery entirely — no rescan_init, no
                            \* zero_tracking, no worker. The full/simple
                            \* choice is the ioctl argument, modeled as a
                            \* nondeterministic branch here. (Deliberate
                            \* over-approximation: the model does not track
                            \* SIMPLE_MODE, so it permits a later rescan that
                            \* the kernel would reject with -EINVAL; that
                            \* only ADDS interleavings, all fix-protected.)
    /\ pc[t] = "e_rescaninit"
    /\ pc' = [pc EXCEPT ![t] = "e_done"]
    /\ UNCHANGED <<quotaRoot, quotaEnabled, flagOn, flagRescan, rescanRunning,
                   completionDone, workerQueued, workerStopped, qgroupLock,
                   rescanLock, subvolSem, iterating, uafOccurred>>

E_RescanInit(t) ==          \* internal: qgroup_rescan_init(fs_info, 0, 1)
    /\ pc[t] = "e_rescaninit" /\ rescanLock = NoTask
    /\ IF flagRescan
       THEN \* -EINPROGRESS: someone already started a rescan; enable
            \* tolerates this (ASSERT ret == -EINPROGRESS; ret = 0)
            /\ pc' = [pc EXCEPT ![t] = "e_done"]
            /\ UNCHANGED <<flagRescan, completionDone>>
       ELSE /\ flagRescan' = TRUE
            /\ completionDone' = FALSE      \* init_completion, qgroup.c:4019
            /\ pc' = [pc EXCEPT ![t] = "e_zt_enter"]
    /\ UNCHANGED <<quotaRoot, quotaEnabled, flagOn, rescanRunning,
                   workerQueued, workerStopped, qgroupLock, rescanLock,
                   subvolSem, iterating, uafOccurred>>

E_ZTEnter(t) ==             \* observable: RescanZeroTracking_Enter
    /\ pc[t] = "e_zt_enter"
    /\ pc' = [pc EXCEPT ![t] = "e_zt_iter"]
    /\ UNCHANGED <<quotaRoot, quotaEnabled, flagOn, flagRescan, rescanRunning,
                   completionDone, workerQueued, workerStopped, qgroupLock,
                   rescanLock, subvolSem, iterating, uafOccurred>>

E_ZTLock(t) ==              \* internal: spin_lock(qgroup_lock); start iterating
    /\ pc[t] = "e_zt_iter" /\ qgroupLock = NoTask /\ t \notin iterating
    /\ qgroupLock' = t
    /\ iterating' = iterating \cup {t}
    /\ UNCHANGED <<quotaRoot, quotaEnabled, flagOn, flagRescan, rescanRunning,
                   completionDone, workerQueued, workerStopped, rescanLock,
                   subvolSem, uafOccurred, pc>>

E_ZTUnlock(t) ==            \* internal: iteration finished; spin_unlock
    /\ pc[t] = "e_zt_iter" /\ qgroupLock = t /\ t \in iterating
    /\ qgroupLock' = NoTask
    /\ iterating' = iterating \ {t}
    /\ pc' = [pc EXCEPT ![t] = "e_zt_done"]
    /\ UNCHANGED <<quotaRoot, quotaEnabled, flagOn, flagRescan, rescanRunning,
                   completionDone, workerQueued, workerStopped, rescanLock,
                   subvolSem, uafOccurred>>

E_ZTDone(t) ==              \* observable: RescanZeroTracking_Done
    /\ pc[t] = "e_zt_done"
    /\ pc' = [pc EXCEPT ![t] = "e_queue"]
    /\ UNCHANGED <<quotaRoot, quotaEnabled, flagOn, flagRescan, rescanRunning,
                   completionDone, workerQueued, workerStopped, qgroupLock,
                   rescanLock, subvolSem, iterating, uafOccurred>>

E_Queue(t) ==               \* internal: qgroup.c:1268-1270 (no rescan_lock here;
                            \* safe because enable holds subvol_sem)
    /\ pc[t] = "e_queue"
    /\ rescanRunning' = TRUE /\ workerQueued' = TRUE
    /\ pc' = [pc EXCEPT ![t] = "e_done"]
    /\ UNCHANGED <<quotaRoot, quotaEnabled, flagOn, flagRescan, completionDone,
                   workerStopped, qgroupLock, rescanLock, subvolSem,
                   iterating, uafOccurred>>

QuotaEnableDone(t) ==       \* observable: QuotaEnable_Done
    /\ pc[t] = "e_done" /\ subvolSem = t
    /\ subvolSem' = NoTask
    /\ pc' = [pc EXCEPT ![t] = "idle"]
    /\ UNCHANGED <<quotaRoot, quotaEnabled, flagOn, flagRescan, rescanRunning,
                   completionDone, workerQueued, workerStopped, qgroupLock,
                   rescanLock, iterating, uafOccurred>>

(***************************************************************************)
(* btrfs_quota_disable — under subvol_sem.                                 *)
(***************************************************************************)

QuotaDisableEnter(t) ==     \* observable: QuotaDisable_Enter
    /\ t \in UserTasks /\ pc[t] = "idle" /\ subvolSem = NoTask
    /\ ~Closing
    /\ subvolSem' = t
    /\ pc' = [pc EXCEPT ![t] = "d_check"]
    /\ UNCHANGED <<quotaRoot, quotaEnabled, flagOn, flagRescan, rescanRunning,
                   completionDone, workerQueued, workerStopped, qgroupLock,
                   rescanLock, iterating, uafOccurred>>

D_Check(t) ==               \* internal: if (!fs_info->quota_root) goto out
    /\ pc[t] = "d_check"
    /\ pc' = [pc EXCEPT ![t] = IF quotaRoot THEN "d_clear_enabled" ELSE "d_done"]
    /\ UNCHANGED <<quotaRoot, quotaEnabled, flagOn, flagRescan, rescanRunning,
                   completionDone, workerQueued, workerStopped, qgroupLock,
                   rescanLock, subvolSem, iterating, uafOccurred>>

D_ClearEnabled(t) ==        \* internal: clear_bit(BTRFS_FS_QUOTA_ENABLED)
    /\ pc[t] = "d_clear_enabled"
    /\ quotaEnabled' = FALSE
    /\ pc' = [pc EXCEPT ![t] = "d_wait_enter"]
    /\ UNCHANGED <<quotaRoot, flagOn, flagRescan, rescanRunning, completionDone,
                   workerQueued, workerStopped, qgroupLock, rescanLock,
                   subvolSem, iterating, uafOccurred>>

D_WaitEnter(t) ==           \* internal: btrfs_qgroup_wait_for_completion is
                            \* inlined into btrfs_quota_disable (same TU), so
                            \* its kprobe never fires — not observable
    /\ pc[t] = "d_wait_enter"
    /\ pc' = [pc EXCEPT ![t] = "d_wait_read"]
    /\ UNCHANGED <<quotaRoot, quotaEnabled, flagOn, flagRescan, rescanRunning,
                   completionDone, workerQueued, workerStopped, qgroupLock,
                   rescanLock, subvolSem, iterating, uafOccurred>>

D_WaitRead(t) ==            \* internal: read rescan_running under rescan_lock;
                            \* THE HOLE: returns immediately if it is false,
                            \* even though FLAG_RESCAN may already be set.
    /\ pc[t] = "d_wait_read" /\ rescanLock = NoTask
    /\ pc' = [pc EXCEPT ![t] = IF rescanRunning THEN "d_wait_block" ELSE "d_wait_done"]
    /\ UNCHANGED <<quotaRoot, quotaEnabled, flagOn, flagRescan, rescanRunning,
                   completionDone, workerQueued, workerStopped, qgroupLock,
                   rescanLock, subvolSem, iterating, uafOccurred>>

D_WaitBlocked(t) ==         \* internal: wait_for_completion(...)
    /\ pc[t] = "d_wait_block" /\ completionDone
    /\ pc' = [pc EXCEPT ![t] = "d_wait_done"]
    /\ UNCHANGED <<quotaRoot, quotaEnabled, flagOn, flagRescan, rescanRunning,
                   completionDone, workerQueued, workerStopped, qgroupLock,
                   rescanLock, subvolSem, iterating, uafOccurred>>

D_WaitDone(t) ==            \* internal (see D_WaitEnter)
    /\ pc[t] = "d_wait_done"
    /\ pc' = [pc EXCEPT ![t] = "d_trans"]
    /\ UNCHANGED <<quotaRoot, quotaEnabled, flagOn, flagRescan, rescanRunning,
                   completionDone, workerQueued, workerStopped, qgroupLock,
                   rescanLock, subvolSem, iterating, uafOccurred>>

D_Trans(t) ==               \* internal: flush_reservations + start_transaction
    /\ pc[t] = "d_trans"
    /\ pc' = [pc EXCEPT ![t] = "d_clear_root"]
    /\ UNCHANGED <<quotaRoot, quotaEnabled, flagOn, flagRescan, rescanRunning,
                   completionDone, workerQueued, workerStopped, qgroupLock,
                   rescanLock, subvolSem, iterating, uafOccurred>>

D_ClearRoot(t) ==           \* internal: qgroup.c:1403-1409, under qgroup_lock
    /\ pc[t] = "d_clear_root" /\ qgroupLock = NoTask
    /\ quotaRoot' = FALSE /\ flagOn' = FALSE
    /\ pc' = [pc EXCEPT ![t] = "d_free_enter"]
    /\ UNCHANGED <<quotaEnabled, flagRescan, rescanRunning, completionDone,
                   workerQueued, workerStopped, qgroupLock, rescanLock,
                   subvolSem, iterating, uafOccurred>>

D_FreeEnter(t) ==           \* observable: FreeQgroupConfig_Enter
    /\ pc[t] = "d_free_enter"
    /\ pc' = [pc EXCEPT ![t] = IF FixFreeHoldsQgroupLock THEN "d_free_lock" ELSE "d_free_do"]
    /\ UNCHANGED <<quotaRoot, quotaEnabled, flagOn, flagRescan, rescanRunning,
                   completionDone, workerQueued, workerStopped, qgroupLock,
                   rescanLock, subvolSem, iterating, uafOccurred>>

D_FreeLock(t) ==            \* internal (fixed kernel): spin_lock(qgroup_lock)
    /\ pc[t] = "d_free_lock" /\ qgroupLock = NoTask
    /\ qgroupLock' = t
    /\ pc' = [pc EXCEPT ![t] = "d_free_do"]
    /\ UNCHANGED <<quotaRoot, quotaEnabled, flagOn, flagRescan, rescanRunning,
                   completionDone, workerQueued, workerStopped, rescanLock,
                   subvolSem, iterating, uafOccurred>>

D_FreeDo(t) ==              \* internal: rb_erase + kfree of every qgroup record.
                            \* UAF iff another task holds a live iterator now.
    /\ pc[t] = "d_free_do"
    /\ IF FixFreeHoldsQgroupLock THEN qgroupLock = t ELSE TRUE
    /\ uafOccurred' = (uafOccurred \/ \E t2 \in iterating : t2 # t)
    /\ qgroupLock' = IF FixFreeHoldsQgroupLock THEN NoTask ELSE qgroupLock
    /\ pc' = [pc EXCEPT ![t] = "d_free_done"]
    /\ UNCHANGED <<quotaRoot, quotaEnabled, flagOn, flagRescan, rescanRunning,
                   completionDone, workerQueued, workerStopped, rescanLock,
                   subvolSem, iterating>>

D_FreeDone(t) ==            \* observable: FreeQgroupConfig_Done
    /\ pc[t] = "d_free_done"
    /\ pc' = [pc EXCEPT ![t] = "d_clean"]
    /\ UNCHANGED <<quotaRoot, quotaEnabled, flagOn, flagRescan, rescanRunning,
                   completionDone, workerQueued, workerStopped, qgroupLock,
                   rescanLock, subvolSem, iterating, uafOccurred>>

D_Clean(t) ==               \* internal: clean quota tree, del root, commit
    /\ pc[t] = "d_clean"
    /\ pc' = [pc EXCEPT ![t] = "d_done"]
    /\ UNCHANGED <<quotaRoot, quotaEnabled, flagOn, flagRescan, rescanRunning,
                   completionDone, workerQueued, workerStopped, qgroupLock,
                   rescanLock, subvolSem, iterating, uafOccurred>>

QuotaDisableDone(t) ==      \* observable: QuotaDisable_Done
    /\ pc[t] = "d_done" /\ subvolSem = t
    /\ subvolSem' = NoTask
    /\ pc' = [pc EXCEPT ![t] = "idle"]
    /\ UNCHANGED <<quotaRoot, quotaEnabled, flagOn, flagRescan, rescanRunning,
                   completionDone, workerQueued, workerStopped, qgroupLock,
                   rescanLock, iterating, uafOccurred>>

(***************************************************************************)
(* btrfs_qgroup_rescan (the rescan ioctl) — NO subvol_sem.                 *)
(***************************************************************************)

QgroupRescanEnter(t) ==     \* observable: QgroupRescan_Enter
    /\ t \in UserTasks /\ pc[t] = "idle" /\ ~Closing
    /\ pc' = [pc EXCEPT ![t] = "r_init"]
    /\ UNCHANGED <<quotaRoot, quotaEnabled, flagOn, flagRescan, rescanRunning,
                   completionDone, workerQueued, workerStopped, qgroupLock,
                   rescanLock, subvolSem, iterating, uafOccurred>>

R_Init(t) ==                \* internal: qgroup_rescan_init(fs_info, 0, 1)
    /\ pc[t] = "r_init" /\ rescanLock = NoTask
    /\ IF flagRescan \/ ~flagOn
       THEN \* -EINPROGRESS or -ENOTCONN/-EBUSY
            /\ pc' = [pc EXCEPT ![t] = "r_done"]
            /\ UNCHANGED <<flagRescan, completionDone>>
       ELSE /\ flagRescan' = TRUE
            /\ completionDone' = FALSE      \* init_completion
            /\ pc' = [pc EXCEPT ![t] = "r_commit"]
    /\ UNCHANGED <<quotaRoot, quotaEnabled, flagOn, rescanRunning,
                   workerQueued, workerStopped, qgroupLock, rescanLock,
                   subvolSem, iterating, uafOccurred>>

R_Commit(t) ==              \* internal: btrfs_commit_current_transaction —
                            \* the wide window with FLAG_RESCAN set but
                            \* rescan_running still FALSE (qgroup.c:4066)
    /\ pc[t] = "r_commit"
    /\ pc' = [pc EXCEPT ![t] = "r_zt_enter"]
    /\ UNCHANGED <<quotaRoot, quotaEnabled, flagOn, flagRescan, rescanRunning,
                   completionDone, workerQueued, workerStopped, qgroupLock,
                   rescanLock, subvolSem, iterating, uafOccurred>>

R_ZTEnter(t) ==             \* observable: RescanZeroTracking_Enter
    /\ pc[t] = "r_zt_enter"
    /\ pc' = [pc EXCEPT ![t] = "r_zt_iter"]
    /\ UNCHANGED <<quotaRoot, quotaEnabled, flagOn, flagRescan, rescanRunning,
                   completionDone, workerQueued, workerStopped, qgroupLock,
                   rescanLock, subvolSem, iterating, uafOccurred>>

R_ZTLock(t) ==              \* internal: spin_lock(qgroup_lock); start iterating
    /\ pc[t] = "r_zt_iter" /\ qgroupLock = NoTask /\ t \notin iterating
    /\ qgroupLock' = t
    /\ iterating' = iterating \cup {t}
    /\ UNCHANGED <<quotaRoot, quotaEnabled, flagOn, flagRescan, rescanRunning,
                   completionDone, workerQueued, workerStopped, rescanLock,
                   subvolSem, uafOccurred, pc>>

R_ZTUnlock(t) ==            \* internal: iteration finished; spin_unlock
    /\ pc[t] = "r_zt_iter" /\ qgroupLock = t /\ t \in iterating
    /\ qgroupLock' = NoTask
    /\ iterating' = iterating \ {t}
    /\ pc' = [pc EXCEPT ![t] = "r_zt_done"]
    /\ UNCHANGED <<quotaRoot, quotaEnabled, flagOn, flagRescan, rescanRunning,
                   completionDone, workerQueued, workerStopped, rescanLock,
                   subvolSem, uafOccurred>>

R_ZTDone(t) ==              \* observable: RescanZeroTracking_Done
    /\ pc[t] = "r_zt_done"
    /\ pc' = [pc EXCEPT ![t] = "r_queue"]
    /\ UNCHANGED <<quotaRoot, quotaEnabled, flagOn, flagRescan, rescanRunning,
                   completionDone, workerQueued, workerStopped, qgroupLock,
                   rescanLock, subvolSem, iterating, uafOccurred>>

R_Queue(t) ==               \* internal: qgroup.c:4074-4087, under rescan_lock;
                            \* only queues if full accounting is still on
    /\ pc[t] = "r_queue" /\ rescanLock = NoTask
    /\ IF flagOn
       THEN rescanRunning' = TRUE /\ workerQueued' = TRUE
       ELSE UNCHANGED <<rescanRunning, workerQueued>>   \* -ENOTCONN
    /\ pc' = [pc EXCEPT ![t] = "r_done"]
    /\ UNCHANGED <<quotaRoot, quotaEnabled, flagOn, flagRescan, completionDone,
                   workerStopped, qgroupLock, rescanLock, subvolSem,
                   iterating, uafOccurred>>

QgroupRescanDone(t) ==      \* observable: QgroupRescan_Done
    /\ pc[t] = "r_done"
    /\ pc' = [pc EXCEPT ![t] = "idle"]
    /\ UNCHANGED <<quotaRoot, quotaEnabled, flagOn, flagRescan, rescanRunning,
                   completionDone, workerQueued, workerStopped, qgroupLock,
                   rescanLock, subvolSem, iterating, uafOccurred>>

(***************************************************************************)
(* Standalone btrfs_qgroup_wait_for_completion (the rescan-wait ioctl:     *)
(* quota rescan -w). Out-of-TU caller, so the kprobe fires: observable.    *)
(***************************************************************************)

UserWaitEnter(t) ==         \* observable: WaitRescanCompletion_Enter
    /\ t \in UserTasks /\ pc[t] = "idle" /\ ~Closing
    /\ pc' = [pc EXCEPT ![t] = "u_wait_read"]
    /\ UNCHANGED <<quotaRoot, quotaEnabled, flagOn, flagRescan, rescanRunning,
                   completionDone, workerQueued, workerStopped, qgroupLock,
                   rescanLock, subvolSem, iterating, uafOccurred>>

U_WaitRead(t) ==            \* internal
    /\ pc[t] = "u_wait_read" /\ rescanLock = NoTask
    /\ pc' = [pc EXCEPT ![t] = IF rescanRunning THEN "u_wait_block" ELSE "u_wait_done"]
    /\ UNCHANGED <<quotaRoot, quotaEnabled, flagOn, flagRescan, rescanRunning,
                   completionDone, workerQueued, workerStopped, qgroupLock,
                   rescanLock, subvolSem, iterating, uafOccurred>>

U_WaitBlocked(t) ==         \* internal
    /\ pc[t] = "u_wait_block" /\ completionDone
    /\ pc' = [pc EXCEPT ![t] = "u_wait_done"]
    /\ UNCHANGED <<quotaRoot, quotaEnabled, flagOn, flagRescan, rescanRunning,
                   completionDone, workerQueued, workerStopped, qgroupLock,
                   rescanLock, subvolSem, iterating, uafOccurred>>

UserWaitDone(t) ==          \* observable: WaitRescanCompletion_Done
    /\ pc[t] = "u_wait_done"
    /\ pc' = [pc EXCEPT ![t] = "idle"]
    /\ UNCHANGED <<quotaRoot, quotaEnabled, flagOn, flagRescan, rescanRunning,
                   completionDone, workerQueued, workerStopped, qgroupLock,
                   rescanLock, subvolSem, iterating, uafOccurred>>

(***************************************************************************)
(* close_ctree (unmount): wait_for_completion, then free_qgroup_config,    *)
(* then the fs_info is torn down — a later mount starts fresh. The wait    *)
(* and free are the same functions as in disable, so the fix constant and  *)
(* the UAF emergence rule apply here identically. Entered only when no     *)
(* other user task is mid-operation (VFS: busy fs fails umount).           *)
(***************************************************************************)

UmountBegin(t) ==           \* observable: WaitRescanCompletion_Enter
    /\ t \in UserTasks /\ pc[t] = "idle"
    /\ \A t2 \in UserTasks \ {t} : pc[t2] = "idle"
    /\ pc' = [pc EXCEPT ![t] = "m_wait_read"]
    /\ UNCHANGED <<quotaRoot, quotaEnabled, flagOn, flagRescan, rescanRunning,
                   completionDone, workerQueued, workerStopped, qgroupLock,
                   rescanLock, subvolSem, iterating, uafOccurred>>

M_WaitRead(t) ==            \* internal: read rescan_running under rescan_lock
    /\ pc[t] = "m_wait_read" /\ rescanLock = NoTask
    /\ pc' = [pc EXCEPT ![t] = IF rescanRunning THEN "m_wait_block" ELSE "m_wait_done"]
    /\ UNCHANGED <<quotaRoot, quotaEnabled, flagOn, flagRescan, rescanRunning,
                   completionDone, workerQueued, workerStopped, qgroupLock,
                   rescanLock, subvolSem, iterating, uafOccurred>>

M_WaitBlocked(t) ==         \* internal: wait_for_completion(...)
    /\ pc[t] = "m_wait_block" /\ completionDone
    /\ pc' = [pc EXCEPT ![t] = "m_wait_done"]
    /\ UNCHANGED <<quotaRoot, quotaEnabled, flagOn, flagRescan, rescanRunning,
                   completionDone, workerQueued, workerStopped, qgroupLock,
                   rescanLock, subvolSem, iterating, uafOccurred>>

M_WaitDone(t) ==            \* observable: WaitRescanCompletion_Done
    /\ pc[t] = "m_wait_done"
    /\ pc' = [pc EXCEPT ![t] = "m_free_enter"]
    /\ UNCHANGED <<quotaRoot, quotaEnabled, flagOn, flagRescan, rescanRunning,
                   completionDone, workerQueued, workerStopped, qgroupLock,
                   rescanLock, subvolSem, iterating, uafOccurred>>

M_FreeEnter(t) ==           \* observable: FreeQgroupConfig_Enter
    /\ pc[t] = "m_free_enter"
    /\ pc' = [pc EXCEPT ![t] = IF FixFreeHoldsQgroupLock THEN "m_free_lock" ELSE "m_free_do"]
    /\ UNCHANGED <<quotaRoot, quotaEnabled, flagOn, flagRescan, rescanRunning,
                   completionDone, workerQueued, workerStopped, qgroupLock,
                   rescanLock, subvolSem, iterating, uafOccurred>>

M_FreeLock(t) ==            \* internal (fixed kernel): spin_lock(qgroup_lock)
    /\ pc[t] = "m_free_lock" /\ qgroupLock = NoTask
    /\ qgroupLock' = t
    /\ pc' = [pc EXCEPT ![t] = "m_free_do"]
    /\ UNCHANGED <<quotaRoot, quotaEnabled, flagOn, flagRescan, rescanRunning,
                   completionDone, workerQueued, workerStopped, rescanLock,
                   subvolSem, iterating, uafOccurred>>

M_FreeDo(t) ==              \* internal: same UAF emergence rule as D_FreeDo
    /\ pc[t] = "m_free_do"
    /\ IF FixFreeHoldsQgroupLock THEN qgroupLock = t ELSE TRUE
    /\ uafOccurred' = (uafOccurred \/ \E t2 \in iterating : t2 # t)
    /\ qgroupLock' = IF FixFreeHoldsQgroupLock THEN NoTask ELSE qgroupLock
    /\ pc' = [pc EXCEPT ![t] = "m_free_done"]
    /\ UNCHANGED <<quotaRoot, quotaEnabled, flagOn, flagRescan, rescanRunning,
                   completionDone, workerQueued, workerStopped, rescanLock,
                   subvolSem, iterating>>

M_FreeDone(t) ==            \* observable: FreeQgroupConfig_Done. Also folds
                            \* in the teardown: the fs_info is destroyed and
                            \* a later mount (xfstests re-mkfs's between
                            \* subtests) starts from fresh in-memory state.
                            \* Sound to fold: the ~Closing gates keep every
                            \* other task out until this task is idle again,
                            \* so nothing can observe a gap between the free
                            \* returning and the teardown.
    /\ pc[t] = "m_free_done"
    /\ quotaRoot' = FALSE /\ quotaEnabled' = FALSE
    /\ flagOn' = FALSE /\ flagRescan' = FALSE
    /\ rescanRunning' = FALSE /\ completionDone' = FALSE
    /\ workerQueued' = FALSE
    /\ pc' = [pc EXCEPT ![t] = "idle"]
    /\ UNCHANGED <<workerStopped, qgroupLock, rescanLock, subvolSem,
                   iterating, uafOccurred>>

(***************************************************************************)
(* btrfs_qgroup_rescan_worker                                              *)
(***************************************************************************)

WorkerStart ==              \* observable: RescanWorker_Enter
    /\ pc[Worker] = "w_idle" /\ workerQueued
    /\ workerQueued' = FALSE
    /\ pc' = [pc EXCEPT ![Worker] = "w_run"]
    /\ UNCHANGED <<quotaRoot, quotaEnabled, flagOn, flagRescan, rescanRunning,
                   completionDone, workerStopped, qgroupLock, rescanLock,
                   subvolSem, iterating, uafOccurred>>

W_ExitLoop ==               \* internal: scan loop exits; `stopped` is
                            \* rescan_should_stop() = !quotaEnabled or the
                            \* fs is closing (unmount in progress)
    /\ pc[Worker] = "w_run"
    /\ workerStopped' = (~quotaEnabled \/ Closing)
    /\ pc' = [pc EXCEPT ![Worker] = "w_finish"]
    /\ UNCHANGED <<quotaRoot, quotaEnabled, flagOn, flagRescan, rescanRunning,
                   completionDone, workerQueued, qgroupLock, rescanLock,
                   subvolSem, iterating, uafOccurred>>

W_Finish ==                 \* internal: qgroup.c:3925-3940 under rescan_lock
    /\ pc[Worker] = "w_finish" /\ rescanLock = NoTask
    /\ flagRescan' = IF ~workerStopped THEN FALSE ELSE flagRescan
    /\ rescanRunning' = FALSE
    /\ completionDone' = TRUE               \* complete_all
    /\ pc' = [pc EXCEPT ![Worker] = "w_exit"]
    /\ UNCHANGED <<quotaRoot, quotaEnabled, flagOn, workerQueued,
                   workerStopped, qgroupLock, rescanLock, subvolSem,
                   iterating, uafOccurred>>

WorkerDone ==               \* observable: RescanWorker_Done
    /\ pc[Worker] = "w_exit"
    /\ pc' = [pc EXCEPT ![Worker] = "w_idle"]
    /\ UNCHANGED <<quotaRoot, quotaEnabled, flagOn, flagRescan, rescanRunning,
                   completionDone, workerQueued, workerStopped, qgroupLock,
                   rescanLock, subvolSem, iterating, uafOccurred>>

(***************************************************************************)
(* Observable / internal partition (names match the bpftrace events)       *)
(***************************************************************************)

Observable(t, a) ==
    CASE a = "QuotaEnable_Enter"          -> QuotaEnableEnter(t)
      [] a = "QuotaEnable_Done"           -> QuotaEnableDone(t)
      [] a = "QuotaDisable_Enter"         -> QuotaDisableEnter(t)
      [] a = "QuotaDisable_Done"          -> QuotaDisableDone(t)
      [] a = "QgroupRescan_Enter"         -> QgroupRescanEnter(t)
      [] a = "QgroupRescan_Done"          -> QgroupRescanDone(t)
      [] a = "RescanZeroTracking_Enter"   -> E_ZTEnter(t) \/ R_ZTEnter(t)
      [] a = "RescanZeroTracking_Done"    -> E_ZTDone(t) \/ R_ZTDone(t)
      [] a = "WaitRescanCompletion_Enter" -> UserWaitEnter(t) \/ UmountBegin(t)
      [] a = "WaitRescanCompletion_Done"  -> UserWaitDone(t) \/ M_WaitDone(t)
      [] a = "FreeQgroupConfig_Enter"     -> D_FreeEnter(t) \/ M_FreeEnter(t)
      [] a = "FreeQgroupConfig_Done"      -> D_FreeDone(t) \/ M_FreeDone(t)
      [] a = "RescanWorker_Enter"         -> WorkerStart
      [] a = "RescanWorker_Done"          -> WorkerDone
      [] OTHER                            -> FALSE

Internal ==
    \/ \E t \in UserTasks :
        \/ E_Check(t) \/ E_Create(t) \/ E_SetRoot(t) \/ E_RescanInit(t)
        \/ E_SimpleSkip(t) \/ E_ZTLock(t) \/ E_ZTUnlock(t) \/ E_Queue(t)
        \/ D_Check(t) \/ D_ClearEnabled(t) \/ D_WaitEnter(t) \/ D_WaitRead(t)
        \/ D_WaitBlocked(t) \/ D_WaitDone(t) \/ D_Trans(t) \/ D_ClearRoot(t)
        \/ D_FreeLock(t) \/ D_FreeDo(t) \/ D_Clean(t)
        \/ R_Init(t) \/ R_Commit(t) \/ R_ZTLock(t) \/ R_ZTUnlock(t) \/ R_Queue(t)
        \/ U_WaitRead(t) \/ U_WaitBlocked(t)
        \/ M_WaitRead(t) \/ M_WaitBlocked(t) \/ M_FreeLock(t) \/ M_FreeDo(t)
    \/ W_ExitLoop \/ W_Finish

ObservableNames == {"QuotaEnable_Enter", "QuotaEnable_Done",
                    "QuotaDisable_Enter", "QuotaDisable_Done",
                    "QgroupRescan_Enter", "QgroupRescan_Done",
                    "RescanZeroTracking_Enter", "RescanZeroTracking_Done",
                    "WaitRescanCompletion_Enter", "WaitRescanCompletion_Done",
                    "FreeQgroupConfig_Enter", "FreeQgroupConfig_Done",
                    "RescanWorker_Enter", "RescanWorker_Done"}

Next ==
    \/ Internal
    \/ \E t \in Tasks, a \in ObservableNames : Observable(t, a)

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* The safety property. Not encoded by construction: uafOccurred is set    *)
(* only by D_FreeDo when the free interleaves with a live iterator, which  *)
(* the modeled lock discipline makes reachable iff the fix is absent.      *)
(***************************************************************************)
NoUAF == ~uafOccurred

================================================================================
