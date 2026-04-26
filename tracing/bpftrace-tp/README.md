# bpftrace-tp — Tracepoint-Based Scripts

This directory contains **tracepoint-based** bpftrace scripts for all 13 modeled
Btrfs subsystems. These replace the kprobe-based scripts in `../bpftrace/` and are
the recommended approach for any system where kprobes fail to load.

## Why Tracepoints Instead of Kprobes

| Feature | kprobes | tracepoints |
|---|---|---|
| Stability | Function names change per kernel release | Stable ABI — names never change |
| BTF requirement | Required for struct field access | Not required |
| Overhead | Slightly higher (dynamic) | Lower (static, compiled in) |
| Field access | Full struct layout via BTF | Fixed fields declared in `TRACE_EVENT` |
| Availability | Only if function is not inlined | Always present if `CONFIG_TRACEPOINTS=y` |

## Verified Environment

These scripts were verified against the Linux 6.9 tracepoint ABI
(`include/trace/events/btrfs.h`). They are compatible with:

- Linux 6.1 LTS through 6.14+
- bpftrace 0.14+
- No `CONFIG_DEBUG_INFO_BTF` required (though BTF helps with error messages)

## Quick Start

```bash
# 1. Verify your system is ready
sudo bpftrace -l 'tracepoint:btrfs:*' | wc -l
# Should print ~100. If 0, Btrfs module is not loaded.

# 2. Load Btrfs if needed
sudo modprobe btrfs
# Or mount a Btrfs filesystem: sudo mount /dev/loop0 /mnt/btrfs

# 3. Run a script
sudo bpftrace btrfs_qgroup.bt

# 4. Pipe to a checker
sudo bpftrace btrfs_qgroup.bt | python3 ../checkers/btrfs_qgroup_checker.py

# 5. Use the harness (runs workload + bpftrace + checker together)
sudo bash ../../workloads/run_trace_check.sh qgroup /mnt/btrfs 60
```

## Scripts

| Script | Subsystem | TLA+ Model | Key Tracepoints |
|---|---|---|---|
| `btrfs_extent_buffer_lock.bt` | B-tree lock ordering | `BtrfsExtentBufferLock.tla` | `btrfs_tree_lock`, `btrfs_tree_unlock`, `btrfs_cow_block` |
| `btrfs_transaction_chain.bt` | Transaction deadlock | `BtrfsTransactionChain.tla` | `btrfs_transaction_commit`, `btrfs_ordered_extent_*`, `btrfs_space_reservation` |
| `btrfs_delayed_refs.bt` | Delayed ref consistency | `BtrfsDelayedRefs.tla` | `add_delayed_tree_ref`, `run_delayed_tree_ref`, `btrfs_reserved_extent_*` |
| `btrfs_free_space_cache.bt` | Free space double-add | `BtrfsFreeSpaceCache.tla` | `btrfs_reserved_extent_*`, `find_free_extent`, `btrfs_reserve_extent` |
| `btrfs_cow_path.bt` | COW path UAF | `BtrfsCOWPath.tla` | `btrfs_cow_block`, `add_delayed_tree_ref`, `run_delayed_tree_ref` |
| `btrfs_qgroup.bt` | Qgroup rescan UAF | `BtrfsQgroupRescan.tla` | `qgroup_meta_reserve`, `btrfs_qgroup_account_extent`, `qgroup_update_counters` |
| `btrfs_space_reservation.bt` | Space over-commit | `BtrfsSpaceReservation.tla` | `btrfs_space_reservation`, `btrfs_trigger_flush`, `btrfs_reserve_ticket` |
| `btrfs_fsync_log_tree.bt` | Fsync duplicate key | `BtrfsFsyncLogTree.tla` | `btrfs_sync_file`, `btrfs_ordered_extent_*` |
| `btrfs_raid56.bt` | RAID56 write hole | `BtrfsRAID56.tla` | `raid56_write`, `raid56_read` |
| `btrfs_balance_relocation.bt` | Balance lost write | `BtrfsBalanceRelocation.tla` | `btrfs_add_block_group`, `btrfs_remove_block_group`, `btrfs_cow_block` |
| `btrfs_snapshot_creation.bt` | Snapshot consistency | `BtrfsSnapshotCreation.tla` | `btrfs_transaction_commit`, `btrfs_ordered_extent_*` |
| `btrfs_send_receive.bt` | Send/receive UAF | `BtrfsSendReceive.tla` | `btrfs_cow_block`, `btrfs_reserved_extent_free` |
| `btrfs_scrub.bt` | Scrub missed repair | `BtrfsScrub.tla` | `btrfs_reserved_extent_*`, `btrfs_cow_block` |
| `btrfs_autodefrag.bt` | Autodefrag stale inode | `BtrfsAutodefrag.tla` | `btrfs_inode_new`, `btrfs_inode_evict`, `btrfs_ordered_extent_add` |
| `btrfs_dev_replace.bt` | Device replace lost write | `BtrfsDevReplace.tla` | `btrfs_chunk_alloc`, `btrfs_chunk_free` |
| `btrfs_compression.bt` | Compression consistency | `BtrfsCompression.tla` | `btrfs_ordered_extent_*` (compress_type > 0) |
| `btrfs_async_discard.bt` | Async discard safety | `BtrfsAsyncDiscard.tla` | `btrfs_reserved_extent_*`, `btrfs_add_unused_block_group` |

## Output Format

All scripts emit one JSON object per event on stdout:

```json
{"tid":1842,"comm":"btrfs-worker","action":"AcquireWrite","block":4194304,"owner":1,"is_log":0,"wait_ns":0,"ts":1712345678901}
{"tid":1901,"comm":"kworker/u8:2","action":"QgroupAccountExtent","bytenr":8388608,"num_bytes":4096,"nr_old_roots":1,"nr_new_roots":0,"ts":1712345679010}
{"tid":1842,"action":"VIOLATION_RescanStalled","gap_ns":2100000000,"ts":1712345681011}
```

`VIOLATION_*` events are emitted inline when the script detects an anomaly.
The Python checkers in `../checkers/` perform the full cross-thread invariant check.

## Tracepoint Field Reference

Key fields available across scripts:

| Tracepoint | Key Fields |
|---|---|
| `btrfs_tree_lock` / `btrfs_tree_read_lock` | `block` (bytenr), `owner` (root id), `is_log_tree`, `diff_ns` (wait time) |
| `btrfs_tree_unlock` / `btrfs_tree_read_unlock` | `block`, `owner`, `is_log_tree` |
| `btrfs_cow_block` | `root_objectid`, `buf_start`, `buf_level`, `cow_start`, `cow_level`, `refs` |
| `btrfs_transaction_commit` | `generation` |
| `btrfs_ordered_extent_*` | `ino`, `file_offset`, `len`, `disk_len`, `flags`, `compress_type` |
| `btrfs_space_reservation` | `type` (string), `val`, `bytes`, `reserve` (1=reserve, 0=release) |
| `btrfs_reserve_ticket` | `flags`, `bytes`, `start_ns`, `flush`, `error` |
| `add_delayed_tree_ref` / `run_delayed_tree_ref` | `bytenr`, `num_bytes`, `action`, `level`, `ref_root` |
| `raid56_write` / `raid56_read` | `full_stripe`, `physical`, `devid`, `offset`, `len`, `stripe_nr`, `nr_data` |
| `qgroup_meta_reserve` | `refroot`, `diff`, `type` |
| `btrfs_qgroup_account_extent` | `bytenr`, `num_bytes`, `nr_old_roots`, `nr_new_roots` |

## Troubleshooting

**"No probes found"** — Btrfs module not loaded. Run `sudo modprobe btrfs` or mount a Btrfs filesystem.

**"ERROR: Could not resolve symbol"** — The tracepoint name changed. Run `sudo bpftrace -l 'tracepoint:btrfs:*'` to see available names.

**Script exits immediately** — No Btrfs activity. Start a workload first, then run the script. Or use the harness which starts both simultaneously.

**"map overflow"** — Reduce the workload duration or add `clear(@map)` calls more frequently.
