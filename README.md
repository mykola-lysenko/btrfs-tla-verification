# Btrfs Formal Verification

Formal verification of the Linux Btrfs filesystem using TLA+ and TLC, paired with a bpftrace runtime tracing kit for checking real kernel execution traces against the formal models.

## Overview

This repository contains the complete output of a seven-track formal verification project covering 26 TLA+ models across the core Btrfs subsystems. Each model captures a known concurrency bug (or class of bugs) in the Btrfs kernel source, verifies the bug using TLC model checking, and provides a fixed variant that satisfies the safety and liveness invariants.

The tracing kit extends the formal work into runtime verification: bpftrace scripts collect normalized JSON traces from a live Btrfs kernel, and Python checkers verify those traces against the invariants extracted from the TLA+ models.

## Repository Structure

```
models/
  track-a/    Transaction lifecycle, Delayed Refs, Extent Buffer Lock
  track-b/    Free Space Cache, COW Path (CVE-2023-1611), Send/Receive
  track-c/    Delayed Inode, Qgroup, Async Discard, Device Replace
  track-d/    Compression, RAID56, Scrub, Space Reservation
  track-e/    Liveness properties (extended from Tracks A–D)
  track-f/    Refinement mappings (abstract → concrete)
  track-g/    Balance/Relocation, Snapshot Creation, Autodefrag, Fsync Log Tree

tracing/
  bpftrace/   One .bt script per subsystem (normalized JSON output)
  checkers/   Python invariant checkers (read JSON from stdin)
  simulators/ Synthetic trace generators for local testing

reports/
  btrfs_track_a_improvements_report.md
  btrfs_track_b_improvements_report.md
  btrfs_track_c_improvements_report.md
  btrfs_track_d_improvements_report.md
  btrfs_track_e_liveness_report.md
  btrfs_extended_track_e_liveness_report.md
  btrfs_track_f_refinement_report.md
  btrfs_track_g_report.md
```

## Model Corpus

| Track | Subsystem | Models | Key Bug Class | CVE |
|---|---|---|---|---|
| A | Transaction lifecycle | 9 | UAF, deadlock, abort race | — |
| A | Delayed References | 2 | Double-free, abort race | — |
| A | Extent Buffer Lock | 3 | ABBA deadlock, lock inversion | — |
| B | Free Space Cache | 3 | Double-add race | — |
| B | COW Path | 3 | Use-after-free | CVE-2023-1611 |
| B | Send/Receive | 1 | UAF (snapshot deleted during send) | — |
| C | Qgroup | 2 | UAF (rescan vs. disable) | CVE-2025-39759 |
| C | Async Discard | 2 | Discard-after-realloc | — |
| C | Device Replace | 1 | Lost write | — |
| D | RAID56 | 4 | Write hole | — |
| D | Scrub | 2 | Missed repair | — |
| D | Space Reservation | 3 | Over-commit, ENOSPC deadlock | — |
| D | Compression | 2 | UAF (page freed before I/O) | — |
| G | Balance/Relocation | 1 | Lost write | — |
| G | Snapshot Creation | 1 | Inconsistent snapshot | — |
| G | Autodefrag | 1 | Stale inode | — |
| G | Fsync Log Tree | 1 | Duplicate key crash | CVE-2024-37354 |

## Tracing Kit

### Requirements

- Linux kernel with `CONFIG_KPROBES=y`, `CONFIG_BPF_SYSCALL=y`, `CONFIG_DEBUG_INFO_BTF=y`
- Btrfs mounted (`CONFIG_BTRFS_FS=y` or `CONFIG_BTRFS_FS=m`)
- bpftrace ≥ 0.14
- Python ≥ 3.10
- Root privileges (`CAP_SYS_ADMIN`)

### Quick Start

**Collect a live trace and check it:**

```bash
# Terminal 1: collect trace
sudo bpftrace tracing/bpftrace/btrfs_extent_buffer_lock.bt | tee trace.jsonl

# Terminal 2: check in real time
tail -f trace.jsonl | python3 tracing/checkers/btrfs_extent_buffer_lock_checker.py
```

**Test the pipeline locally (no kernel required):**

```bash
# Buggy scenario — should report VIOLATES
python3 tracing/simulators/btrfs_extent_buffer_lock_simulate.py --scenario buggy | \
    python3 tracing/checkers/btrfs_extent_buffer_lock_checker.py

# Fixed scenario — should report CONFORMS
python3 tracing/simulators/btrfs_extent_buffer_lock_simulate.py --scenario fixed | \
    python3 tracing/checkers/btrfs_extent_buffer_lock_checker.py
```

### Available Scripts

| Subsystem | bpftrace script | Checker | Simulator | Invariant |
|---|---|---|---|---|
| Transaction Chain | `btrfs_transaction_chain.bt` | `btrfs_transaction_chain_checker.py` | — | NoDeadlock |
| Delayed Refs | `btrfs_delayed_refs.bt` | — | — | NoDoubleFree |
| Extent Buffer Lock | `btrfs_extent_buffer_lock.bt` | `btrfs_extent_buffer_lock_checker.py` | `btrfs_extent_buffer_lock_simulate.py` | NoDeadlock |
| Free Space Cache | `btrfs_free_space_cache.bt` | `btrfs_free_space_cache_checker.py` | `btrfs_free_space_cache_simulate.py` | NoDoubleAdd |
| COW Path | `btrfs_cow_path.bt` | — | — | NoUAF |
| Send/Receive | `btrfs_send_receive.bt` | — | — | NoUAF |
| Qgroup | `btrfs_qgroup.bt` | `btrfs_qgroup_checker.py` | `btrfs_qgroup_simulate.py` | NoUAF |
| Async Discard | `btrfs_async_discard.bt` | — | — | NoDiscardAfterRealloc |
| Device Replace | `btrfs_dev_replace.bt` | — | — | NoLostWrite |
| RAID56 | `btrfs_raid56.bt` | — | — | NoWriteHole |
| Scrub | `btrfs_scrub.bt` | — | — | NoMissedRepair |
| Space Reservation | `btrfs_space_reservation.bt` | — | — | NoOverCommit |
| Compression | `btrfs_compression.bt` | — | — | NoUAF |
| Balance/Relocation | `btrfs_balance_relocation.bt` | — | — | NoLostWrite |
| Snapshot Creation | `btrfs_snapshot_creation.bt` | — | — | SnapshotConsistency |
| Autodefrag | `btrfs_autodefrag.bt` | — | — | NoStaleDefrag |
| Fsync Log Tree | `btrfs_fsync_log_tree.bt` | `btrfs_fsync_log_tree_checker.py` | `btrfs_fsync_log_tree_simulate.py` | NoLogTreeDuplicate |

### Output Format

Every bpftrace script emits one JSON object per event on stdout:

```json
{"ts":1712345678901234567,"tid":1842,"comm":"kworker/1:2","action":"AcquireWrite","level":2,"bytenr":131072}
```

Fields common to all events:

| Field | Type | Description |
|---|---|---|
| `ts` | uint64 | Timestamp in nanoseconds (monotonic) |
| `tid` | int | Kernel thread ID |
| `comm` | string | Thread name (comm) |
| `action` | string | TLA+ action name (matches model variable) |

Subsystem-specific fields follow the action. Actions prefixed with `VIOLATION_` are emitted inline by the bpftrace script when a fast-path check fires in the kernel context.

### Design Principles

**Action names match TLA+ model actions.** The `action` field in every JSON event uses the exact same name as the corresponding TLA+ action in the model. This eliminates any mapping layer between the trace and the checker.

**Checkers are direct translations of TLA+ invariants.** Each checker re-implements the safety invariant from the TLA+ spec in Python, operating on the same abstract state variables. The checker is not a heuristic — it is a faithful translation of the formal specification.

**Simulators enable local testing.** Each simulator generates both a buggy and a fixed trace that exercises the exact race condition the model captures. This lets you validate the full pipeline without a live kernel.

## Running TLC

The TLA+ models require the [TLA+ Toolbox](https://github.com/tlaplus/tlaplus) or the standalone `tla2tools.jar`.

```bash
# Example: check BtrfsExtentBufferLock.tla with the buggy config
java -jar tla2tools.jar -config models/track-a/BtrfsExtentBufferLockBuggy.cfg \
    models/track-a/BtrfsExtentBufferLock.tla
```

Each `.cfg` file specifies the model constants, initial state, and invariants to check. Buggy configs are expected to produce counterexamples; fixed configs are expected to pass.

## Reports

Track-by-track verification reports are in `reports/`. Each report documents the models built, the bugs found, the fixes verified, and the TLC statistics (states explored, counterexample depth).

## Environment Notes

bpftrace requires a kernel with:
- `CONFIG_KPROBES=y` — for function entry/exit probes
- `CONFIG_BPF_SYSCALL=y` — for eBPF program loading
- `CONFIG_DEBUG_INFO_BTF=y` — for typed struct access in bpftrace scripts
- `CONFIG_BTRFS_FS=y` or `=m` — for Btrfs kernel symbols to exist

UML (User Mode Linux) is **not** supported: it does not expose eBPF/kprobe infrastructure to the guest, and its Btrfs support is incomplete. Use a QEMU/KVM VM, a Docker container on a Btrfs-capable host, or bare metal.

## License

The TLA+ models and tracing scripts in this repository are released under the MIT License.
The Linux kernel source referenced in comments is GPL-2.0.
