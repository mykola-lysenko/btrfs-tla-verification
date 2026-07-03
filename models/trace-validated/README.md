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
excludes it against the iterator, and NoUAF holds across all 44k states.

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

The result is a model that (a) reproduces the historical CVE as an emergent
counterexample and (b) accepts 1422 events of real 7.1-rc7 kernel execution.

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
- To validate against a different kernel, re-capture the trace; if a genuinely
  new interleaving appears, the model will diverge and needs a new transition.
