# QEMU Runtime-Verification Harness

Runs the bpftrace tracing kit against an **upstream btrfs kernel** booted under
QEMU/KVM, turning the TLA+ models' invariants into a runtime oracle for real
kernel executions.

Everything runs rootless on the host: Docker provides root + `/dev/kvm` access,
[virtme-ng](https://github.com/arighi/virtme-ng) boots the freshly built kernel
with the container's rootfs shared over 9p (so `bpftrace`, `btrfs-progs`, and
`python3` inside the container are the guest userspace), and the repo is
bind-mounted at `/repo` so traces land in `workloads/results/` on the host.

```
host (no root) ── docker (--device /dev/kvm) ── qemu/KVM guest
                    │                              │
                    │  container rootfs ── 9p ──── /  (bpftrace, btrfs-progs)
                    │  this repo        ── 9p ──── /repo
                    │  sparse raw files ─ virtio ─ /dev/vd[a-d]  (scratch btrfs)
                    └────────────────────────────  guest runs:
                                                   workloads/run_trace_check.sh
```

## Quick Start

```bash
# 1. Build the docker image (kernel toolchain + qemu + virtme-ng + bpftrace)
docker build -t btrfs-trace:latest qemu/

# 2. Get a kernel tree (any upstream tree; btrfs-devel for-next recommended)
#    e.g. tar xzf linux-btrfs-for-next.tar.gz -C ~/qemu-btrfs/

# 3. Build the kernel (defconfig + kvm_guest.config + qemu/kernel.config)
bash qemu/build-kernel.sh ~/qemu-btrfs/btrfs-devel-for-next

# 4. Run a subsystem check: boots the VM, mkfs+mounts scratch btrfs, runs
#    workload + bpftrace + checker, writes results to workloads/results/
bash qemu/run-vm-trace.sh qgroup 60
bash qemu/run-vm-trace.sh fsync-log-tree 120
bash qemu/run-vm-trace.sh raid56 120        # uses 3 scratch disks, -d raid5

# Third arg picks the script edition:
#   tp     (default) — tracepoint scripts (tracing/bpftrace-tp/)
#   kprobe           — function-entry scripts (tracing/bpftrace/); these
#                      emit the action names the Python checkers expect,
#                      so use kprobe for checker-verified runs
bash qemu/run-vm-trace.sh extent-buffer-lock 60 kprobe
```

## Known-good state (2026-07-02, kernel 7.1.0-rc7, bpftrace 0.25)

- All 17 tracepoint scripts parse, attach, and emit events (after joining
  adjacent string literals and renaming tracepoints/fields to the 7.1 ABI —
  see `tracing/join_bt_strings.py` and `tracing/audit_tp_fields.py`).
- kprobe editions verified attaching: qgroup (14 probes), fsync-log-tree
  (12), transaction-chain (9), extent-buffer-lock (after renaming
  `btrfs_tree_lock` → `btrfs_tree_lock_nested`, same for read lock; the
  free-space-cache script still probes a function that became static).
- bpftrace takes ~10 s to attach on this debug kernel (lockdep + BTF); the
  harness waits for the BEGIN banner before starting the workload.
- Verified end-to-end runs: `qgroup` (tp edition, 72k events, checker
  processed all) and `extent-buffer-lock` (kprobe edition, 9.9M events,
  ZERO lost, CONFORMS after calibrating the checker — see below).

## Trace-fidelity lessons (hard-won, do not regress)

1. **Never put a slow consumer in bpftrace's output path.** Python parses
   ~50k JSON lines/s; lock probes emit >100k events/s. Inline FIFO checking
   or writing to 9p (~12 MB/s) backpressures bpftrace and silently drops
   millions of events. The harness writes to /dev/shm and checks post-hoc.
2. **Sort by `ts` before checking.** bpftrace merges per-CPU perf buffers
   in poll order; cross-CPU events arrive out of order.
3. **Watch `bpftrace.log` for "Lost N events".** Any loss invalidates
   stateful checking (unbalanced acquire/release corrupts the lock state).
4. **Reading the btrfs_header at lock-entry races with buffer init** —
   freshly allocated buffers are locked before their header is written
   (observed impossible "level 122"). The checker discards level >= 8.
5. **Lock ordering is per-tree** (`owner`), and the fsync log tree
   (owner -6/-7) is exempt: serialized by log_mutex, legitimately built
   bottom-up. Without these scopings the checker reported tens of
   thousands of false inversions; with them, a complete 9.9M-event trace
   CONFORMS while the buggy simulator scenario still VIOLATES.

## Files

| File | Purpose |
|---|---|
| `Dockerfile` | Toolchain + QEMU + virtme-ng + guest userspace image |
| `kernel.config` | Config fragment: btrfs debug, BPF/BTF, lockdep, virtio/9p |
| `build-kernel.sh` | Builds bzImage inside the container (rootless) |
| `run-vm-trace.sh` | Boots the VM and runs one subsystem end-to-end |
| `guest-run.sh` | Runs inside the guest: scratch mkfs/mount + harness |

## Kernel config highlights

Beyond what the tracing kit needs (`KPROBES`, `BPF_SYSCALL`, `DEBUG_INFO_BTF`,
tracepoints), the fragment enables the in-kernel concurrency detectors that
give independent signal on the same bug classes the TLA+ models target:

- `CONFIG_PROVE_LOCKING` (lockdep) — catches the ABBA/lock-inversion classes
  (extent buffer lock models) at first occurrence, not just on actual deadlock
- `CONFIG_BTRFS_DEBUG`, `BTRFS_ASSERT`, `BTRFS_FS_REF_VERIFY` — btrfs's own
  runtime self-checks (ref-verify directly covers the delayed-refs models)
- `CONFIG_DETECT_HUNG_TASK` — the transaction-chain deadlock model's invariant,
  enforced by the kernel with a 60s timeout
- `CONFIG_DM_FLAKEY`, `DM_LOG_WRITES` — for future crash-consistency runs

KASAN is intentionally off by default (it distorts timing and slows the race
windows); add `CONFIG_KASAN=y` to `kernel.config` for a UAF-hunting build.

## Env knobs for run-vm-trace.sh

| Var | Default | Meaning |
|---|---|---|
| `KSRC` | `~/qemu-btrfs/btrfs-devel-for-next` | kernel source dir |
| `CPUS` | 8 | guest vCPUs (races need real SMP) |
| `MEM` | 4G | guest RAM |
| `NDISKS` | 4 | scratch virtio disks (4G sparse each) |
| `BPFTRACE_DIR` | `tracing/bpftrace-tp` | tracing script edition (guest-run.sh) |

## Interpreting results

Same as `workloads/README.md`: `CONFORMS` means no invariant violation was
observed (kernel correct *or* race window not hit); `VIOLATES` means the checker
found an event sequence breaking the invariant — plus, in this setup, watch the
guest console for lockdep splats, btrfs ASSERT failures, ref-verify errors, and
hung-task reports, which are independent kernel-side confirmation.
