# Btrfs Trace Workloads

Stress workloads designed to generate kernel execution traces that exercise the exact race windows captured by the TLA+ models. Each workload is paired with a bpftrace script (in `tracing/bpftrace/`) and, where available, a Python invariant checker (in `tracing/checkers/`).

## Design Philosophy

Each workload targets a specific **race window** — the precise interleaving of kernel operations that the corresponding TLA+ model flags as a safety violation. The workloads are not general stress tests; they are surgical: they set up the exact preconditions the model requires, then hammer the race window from multiple threads simultaneously.

The key design decisions for each workload are documented in the script header under "What makes this tricky."

## Quick Start

```bash
# Run a single subsystem: workload + bpftrace + checker together
sudo bash run_trace_check.sh <subsystem> /mnt/btrfs [duration_secs]

# Example: check qgroup UAF (CVE-2025-39759)
sudo bash run_trace_check.sh qgroup /mnt/btrfs 60

# Example: check fsync log tree duplicate key (CVE-2024-37354)
sudo bash run_trace_check.sh fsync-log-tree /mnt/btrfs 120
```

Results are saved to `workloads/results/<subsystem>_<timestamp>/`:
- `trace.jsonl` — full normalized JSON trace from bpftrace
- `report.txt` — invariant checker output

## Workload Inventory

| Subsystem | Script | Race Window | CVE | Checker |
|---|---|---|---|---|
| `extent-buffer-lock` | `workload.py` | Lock inversion: bottom-up B-tree lock acquisition | — | Yes |
| `free-space-cache` | `workload.sh` | Double-add: two threads cache the same extent | — | Yes |
| `qgroup` | `workload.sh` | UAF: quota disable frees records while rescan iterates | CVE-2025-39759 | Yes |
| `fsync-log-tree` | `workload.py` | Duplicate key: fsync + prealloc write race | CVE-2024-37354 | Yes |
| `transaction-chain` | `workload.py` | Deadlock: TRANS_JOIN waits for committing transaction | CVE-2025-71194 | Yes |
| `send-receive` | `workload.sh` | UAF: snapshot deleted while send traverses it | — | Inline |
| `snapshot-creation` | `workload.py` | Inconsistency: partial write visible in snapshot | — | Built-in |
| `balance-relocation` | `workload.sh` | Lost write: write to old location after reloc commits | — | Inline |
| `cow-path` | `workload.sh` | UAF: tree block freed while COW path traverses it | CVE-2023-1611 | Inline |
| `raid56` | `workload.sh` | Write hole: partial stripe write + crash | — | Inline |
| `scrub` | `workload.sh` | Missed repair: write after scrub reads but before verify | — | Inline |
| `space-reservation` | `workload.py` | Over-commit: reserved > available metadata | — | Inline |
| `autodefrag` | `workload.sh` | Stale inode: defrag runs after inode deleted | — | Inline |

## Subsystem Details

### `extent-buffer-lock` — Lock Inversion

**Precondition:** A deep B-tree (root → internal → leaf nodes at all three levels).

**Race:** Thread A holds a leaf lock (level 1) and tries to acquire an internal lock (level 2). Thread B holds the internal lock and tries to acquire the leaf lock. Classic ABBA deadlock via lock inversion.

**How the workload creates it:** 16 threads — half writing small files (forces leaf-level splits), half reading directory listings (forces top-down traversal). Rename operations force two-directory locking, which can involve nodes at different levels simultaneously.

```bash
sudo bash run_trace_check.sh extent-buffer-lock /mnt/btrfs 60
```

---

### `qgroup` — Rescan UAF (CVE-2025-39759)

**Precondition:** Quotas enabled, rescan worker running asynchronously.

**Race:** Task B calls `btrfs_quota_disable()` → `btrfs_free_qgroup_config()` while Task A's rescan worker is iterating `qgroup_tree`. The free happens without holding `qgroup_lock`.

**How the workload creates it:** Tight enable/disable loop (20ms between enable and disable). Concurrent file creation and snapshot operations keep the rescan worker busy longer, widening the window. The workload runs ~3,000 enable/disable cycles per minute.

```bash
sudo bash run_trace_check.sh qgroup /mnt/btrfs 60
```

---

### `fsync-log-tree` — Duplicate Key (CVE-2024-37354)

**Precondition:** File with `FALLOC_FL_KEEP_SIZE` preallocated extents beyond `i_size`.

**Race:** Fsync thread reads extent map (sees prealloc extent at offset X). Writer thread extends `i_size` to cover offset X. Fsync logs the prealloc extent AND the new regular extent for the same offset — duplicate key in log tree.

**How the workload creates it:** 32 files, each with 4KB of data and 64KB of prealloc. 8 fsync threads + 8 writer threads + 2 resetter threads (truncate + re-preallocate to keep the precondition alive).

```bash
sudo bash run_trace_check.sh fsync-log-tree /mnt/btrfs 120
```

---

### `transaction-chain` — TRANS_JOIN Deadlock (CVE-2025-71194)

**Precondition:** A transaction in `TRANS_STATE_COMMIT_START` with ordered extents in-flight.

**Race:** Ordered extent worker calls `btrfs_start_transaction(TRANS_JOIN)`. TRANS_JOIN should return `-EBUSY` when commit is starting, but the buggy code calls `wait_current_trans()` unconditionally. The commit is waiting for the ordered extent to complete. Circular wait.

**How the workload creates it:** 8 large writers (1–8MB files, no fsync) keep ordered extents in-flight. 8 xattr writers use `TRANS_JOIN` internally. 2 commit triggers call `sync()` every 100ms to keep commits frequent.

```bash
sudo bash run_trace_check.sh transaction-chain /mnt/btrfs 120
```

---

### `snapshot-creation` — Consistency Check

This workload includes a **built-in consistency checker** that does not require bpftrace. After each snapshot, it verifies that every file contains exactly `PATTERN_A` (all zeros) or `PATTERN_B` (all ones) — never a mix. A partial write visible in the snapshot would appear as a file with mixed content.

```bash
sudo bash run_trace_check.sh snapshot-creation /mnt/btrfs 120
```

---

### `space-reservation` — Over-commit

**Precondition:** Filesystem at ~85% capacity.

**Race:** 64 threads simultaneously reserve metadata space via create/rename/xattr/link operations without flushing. The total reserved bytes approaches the metadata limit, triggering `btrfs_async_reclaim_metadata_space`.

**Observable in trace:** `ReserveMetadata_ENOSPC` events (expected under pressure), `AsyncReclaim_Triggered` events, and `PeriodicStats` showing total reserved bytes.

```bash
sudo bash run_trace_check.sh space-reservation /mnt/btrfs 120
```

---

## Requirements

All workloads require:
- Linux kernel with `CONFIG_BTRFS_FS=y` or `=m`
- `CONFIG_KPROBES=y`, `CONFIG_BPF_SYSCALL=y`, `CONFIG_DEBUG_INFO_BTF=y`
- bpftrace ≥ 0.14
- Python ≥ 3.10
- Root privileges (`CAP_SYS_ADMIN`)

RAID workloads additionally require:
- `raid56`: 3+ block devices, Btrfs formatted with `-d raid5`
- `scrub`: 2+ block devices, Btrfs formatted with `-d raid1`

The `autodefrag` workload requires mounting with `-o autodefrag`.

## Interpreting Results

**CONFORMS** — The trace contains no invariant violations. This means either the kernel is correct, or the race window was not hit during the run. Increase `duration_secs` or thread count to increase coverage.

**VIOLATES** — At least one invariant violation was detected. The checker output and `trace.jsonl` contain the exact event sequence that triggered the violation, including timestamps and thread IDs.

**Inline VIOLATION_ events** — For subsystems without a Python checker, the bpftrace script itself emits `VIOLATION_*` events when it detects a violation in kernel context. These appear in `trace.jsonl` and are counted in the harness report.

## Extending

To add a new workload:
1. Create `workloads/<subsystem>/workload.{sh,py}`
2. Add the subsystem to `BT_SCRIPT`, `CHECKER`, and `WORKLOAD_CMD` in `run_trace_check.sh`
3. Document the race window and preconditions in the script header
