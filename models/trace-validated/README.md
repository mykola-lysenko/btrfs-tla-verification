# Trace-Validated Models

A TLA+ model of the btrfs qgroup lifecycle that is **built from and checked
against the running kernel**, not hand-asserted. This is the answer to "how
do we make the formal models actually correspond to btrfs?"

The models under `models/track-*` encode their bugs *by construction*
(`crash_uaf' = IF node_state = "Freed" THEN TRUE ...`), so TLC "finding" the
bug is circular. This model is different: it encodes the kernel's real lock
discipline and control flow, and the use-after-free **emerges** from the
interleaving only when the fix is removed. The model's fidelity to the real
kernel is then checked by replaying an actual bpftrace trace against it.

## The three artifacts

| File | Role |
|---|---|
| `BtrfsQgroupLifecycle.tla` | The model: enable / disable / rescan / worker state machine, extracted from `fs/btrfs/qgroup.c` + `ioctl.c` (7.1-rc7). Actions named to match the bpftrace events. |
| `BtrfsQgroupLifecycle_{buggy,fixed}.cfg` | The same model with `FixFreeHoldsQgroupLock` FALSE/TRUE — the one line the CVE-2025-39759 fix changed. |
| `BtrfsQgroupLifecycle_workerrace.cfg` | Reachability witness: the rescan worker is a second UAF victim (see below). |
| `BtrfsQgroupTrace.tla` + `validate-trace.sh` | Trace validation: replays a real kernel trace and checks it is an accepted behavior of the model. |

## Part 1 — model checking (does the bug emerge?)

```bash
DIR=models/trace-validated
run() { docker run --rm -v ~/qemu-btrfs/tlc:/tlc:ro -v "$PWD/$DIR":/spec -w /spec \
    btrfs-trace:latest java -cp /tlc/tla2tools.jar tlc2.TLC \
    -workers 8 -config "$1" BtrfsQgroupLifecycle.tla; }

run BtrfsQgroupLifecycle_buggy.cfg   # => Invariant NoUAF is violated (22-step counterexample)
run BtrfsQgroupLifecycle_fixed.cfg   # => No error has been found
```

The buggy counterexample is exactly CVE-2025-39759:

```
u1: QuotaDisable ... clears QUOTA_ENABLED, wait_for_completion sees
    rescan_running == FALSE (the rescan ioctl set FLAG_RESCAN but is still
    in its transaction-commit window), sails through, clears quota_root,
    reaches btrfs_free_qgroup_config  (pc = d_free_do)
u2: btrfs_qgroup_rescan ... qgroup_rescan_zero_tracking is iterating the
    qgroup_tree under qgroup_lock                              (pc = r_zt_iter)
=> D_FreeDo frees the records while u2 holds a live iterator => uafOccurred
```

With `FixFreeHoldsQgroupLock = TRUE` the free loop takes `qgroup_lock`, which
excludes it against the iterator, and NoUAF holds across all 74k states.

### The worker is a second victim (`_workerrace.cfg`)

Modeling the rescan worker's own tree walk — `qgroup_rescan_leaf` takes
`qgroup_lock` and calls `find_qgroup_rb` on the same rb-tree the free loop
erases (`W_ScanLock`/`W_ScanUnlock`) — exposed a **second** use-after-free
victim, distinct from the rescan ioctl's `zero_tracking`:

```bash
run BtrfsQgroupLifecycle_workerrace.cfg   # => NoWorkerRaceWithFree violated (pre-fix)
```

Mechanism (from the counterexample): disable clears `QUOTA_ENABLED` and
passes `wait_for_completion` *in the CVE hole* — a concurrent rescan has set
`FLAG_RESCAN` but not yet `rescan_running`. The rescan then reaches
`R_Queue` and starts the worker, which begins scanning under `qgroup_lock`
while disable is still in its unlocked free loop → the free collides with
the **worker's** iterator, not the ioctl's. Same root cause (the early
`wait_for_completion` return), second blast site. Flip the constant to
`TRUE` and it holds: the fix guards the *tree*, so one lock covers both
victims — which is exactly why the real one-line fix is sufficient.

## Part 2 — trace validation (is the model faithful?)

```bash
# 1. capture a real trace (kprobe edition emits the action names the model uses)
bash qemu/run-vm-trace.sh qgroup 60 kprobe

# 2. replay it against the model
bash models/trace-validated/validate-trace.sh \
     workloads/results/qgroup_<TS>/trace.jsonl
# => RESULT: TRACE ACCEPTED — all 1422 events are a behavior of BtrfsQgroupLifecycle
```

`validate-trace.sh` runs `tracing/trace_to_tla.py` to turn the JSONL trace into
a TLA+ sequence, then TLC replays it: each step either matches the next trace
event or is an internal (unobserved) model transition. If TLC consumes the
whole trace, the run is an accepted behavior of the model (reported as the
`TraceNotDone` invariant being violated). If TLC gets stuck, the model diverges
from the kernel at that event — which is a finding to feed back into the model.

## Part 3 — how much does "ACCEPTED" actually mean?

Acceptance alone is one-sided: it proves the model is not too *restrictive*
(it can explain real kernel behavior), but a model that allows everything
would also accept every trace. Two additional checks bound the claim from
the other side, and a third measures how much of the model the trace vouches
for.

### Mutation testing (is the model too permissive?)

```bash
bash models/trace-validated/mutation-test.sh \
     workloads/results/qgroup_<TS>/trace.jsonl
```

`tracing/mutate_trace.py` generates trace mutants that are **illegal by
construction** — they violate per-task program order or queue→worker
causality, orderings the kernel cannot produce: same-task event swaps,
dropped `*_Enter`s (orphaning the later event), duplicated `*_Done`s, and
worker starts moved before any possible queue event. A faithful model must
reject all of them; unmutated truncated prefixes run as controls and must
still be accepted. Cross-task swaps of independent events are deliberately
NOT generated — those are usually legal alternative interleavings.

### Transition coverage (which parts of the model does the trace vouch for?)

```bash
COVERAGE=1 PROBES=1 bash models/trace-validated/validate-trace.sh <trace.jsonl>
```

`coverage_report.py` maps TLC's `-coverage` output back to the model's
actions and reports which were never taken during replay; flow arithmetic
between adjacent actions recovers branch coverage (e.g. how often disable's
`wait_for_completion` saw `rescan_running == FALSE` — the CVE hole
precondition). The `PROBES=1` runs check *cross-task state overlap* that
action counts cannot see, as negated-reachability witness invariants: did
the trace ever have a disable inside the wait while another task sat in the
rescan commit window (the CVE setup), or the free loop running while anyone
held a live iterator?

For the 1422-event reference trace: **38/43 actions exercised** and **all
24 mutants killed with both controls accepted**, but both witness probes
report *never entered* — every one of the 89 disables sailed through the
wait (`D_WaitBlocked` never fired), yet no rescan was concurrently in its
commit window. So the trace validates the lock/flag protocol and the happy
paths thoroughly, while the CVE-window interleaving itself rests on the
model-checking part (Part 1) plus code reading — an adversarial workload
(concurrent `quota enable/disable/rescan` loops from separate threads) is
the natural way to close that gap.

## What the validation loop actually taught the model

Each divergence during bring-up was a real correction, exactly the point of the
method (the model started from a careful reading, but the trace still caught
things):

1. **Divergence at event 42** — the rescan worker starts (`RescanWorker_Enter`)
   *before* the queueing `btrfs_qgroup_rescan` ioctl returns
   (`QgroupRescan_Done` comes later). The enqueue is an anticipatory cross-task
   handoff; the trace spec models it explicitly (`Enqueue`).
2. **Divergence at event 582** — a task at `idle` must be free to begin the
   operation the trace shows next; the speculative standalone
   `wait_for_completion` path (unused by this workload — no `quota rescan -w`)
   was letting it wander off. Excluded from replay.
3. **`btrfs_qgroup_wait_for_completion` emits no event inside disable** — it is
   inlined into `btrfs_quota_disable` (same TU), so its kprobe never fires
   there. Modeled as internal, not observable.
4. **`qgroup_flags` is overwritten, not OR'd, in enable** (`qgroup.c:1104`,
   `fs_info->qgroup_flags = FLAG_ON`) — clears a stale `FLAG_RESCAN` from a
   scan paused mid-disable. Without this the replay diverged on the
   enable-after-paused-rescan sequence.

The first xfstests trace (btrfs/022, via `qemu/run-vm-xfstests.sh`) taught
three more, none of which the hand-rolled workload could reach:

5. **The unmount path**: `close_ctree` calls
   `btrfs_qgroup_wait_for_completion` and then `btrfs_free_qgroup_config`
   unconditionally — even on filesystems that never enabled quota. The free
   is the same function as in disable, so the CVE fix (and the UAF
   emergence rule) applies at this second call site too; modeled as the
   `UmountBegin`/`M_*` actions, with `~Closing` gates on ioctl entry (VFS:
   a busy fs fails umount before `close_ctree` runs).
6. **The completion is a second anticipatory handoff**: `complete_all` runs
   *inside* the worker, so a waiter's `WaitRescanCompletion_Done` can
   precede the worker's own `RescanWorker_Done` (kretprobe at function
   exit). The replay spec allows `W_ExitLoop`/`W_Finish` as free steps,
   exactly like `Enqueue`.
7. **Ambiguous observables need deadlock-tolerant replay**:
   `WaitRescanCompletion_Enter` is both the rescan-wait ioctl and unmount,
   so replay forks and the wrong branch dies in a sink state. TLC now runs
   with `-deadlock`; the verdict rests solely on `TraceNotDone` (violated
   = accepted; clean finish = divergence).

And the full `-g qgroup` group run (36 tests) taught one more:

8. **Simple quotas are a separate enable path**: squota
   (`BTRFS_QUOTA_CTL_ENABLE_SIMPLE_QUOTA`, the btrfs/301+ tests) skips the
   entire rescan machinery — enable returns with no zero-tracking and no
   worker. 15 of 51 per-fs groups diverged with exactly this signature
   until `E_SimpleSkip` modeled the branch. (The model does not track
   SIMPLE_MODE; see the comment on that action for the deliberate
   over-approximation.)

Traces also carry an `"fs"` field now (the fs_info pointer): xfstests
mounts several btrfs filesystems at once (TEST_DEV + scratch, and each
re-mkfs is a fresh fs_info — one 36-test group run produced 51 quota-active
incarnations); `trace_to_tla.py` splits on it and validates the
quota-active group (`--fs` overrides, `TRACE_FS` env in validate-trace.sh).

The result is a model that (a) reproduces the historical CVE as an emergent
counterexample and (b) accepts every real 7.1-rc7 trace thrown at it so
far: 1422 events of the hand-rolled workload, the xfstests btrfs/022 run,
and all 51 quota-active filesystem incarnations of the full xfstests
`-g qgroup` group run (unmount cycles, standalone waits, squota and all).

## Requirements

- `btrfs-trace:latest` docker image (has Java; see `qemu/README.md`)
- `~/qemu-btrfs/tlc/tla2tools.jar` (TLC 2.19+):
  `curl -L -o ~/qemu-btrfs/tlc/tla2tools.jar https://github.com/tlaplus/tlaplus/releases/latest/download/tla2tools.jar`

## Notes / limits

- Trace replay pins internal steps to the task owning the next observable
  event (plus the enqueue handoff). This is a hand-applied partial-order
  reduction — without it, interleaving 260+ trace tasks explodes to 100M+
  states. It is sound as long as the only anticipatory cross-task dependency
  is the work-queue enqueue; any other hidden dependency shows up as a
  divergence rather than being silently accepted.
- The model abstracts each lock-protected critical section to one atomic
  action. Finer bugs (within a critical section) are out of scope by design —
  that is the standard TLA+ altitude choice, and it is what keeps the state
  space checkable.
- Unmount is modeled as a full in-memory reset, which is correct for
  xfstests-style cycles (each subtest re-mkfs's the scratch device). A
  remount that PRESERVES on-disk quota state (`btrfs_read_qgroup_config`,
  rescan resume at mount) is not modeled yet — a trace doing that will
  diverge at the quota activity that has no preceding enable, which is the
  signal to add the mount-path transitions.
- To validate against a different kernel, re-capture the trace; if a genuinely
  new interleaving appears, the model will diverge and needs a new transition.
