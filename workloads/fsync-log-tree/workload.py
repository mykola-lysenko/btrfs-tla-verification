#!/usr/bin/env python3
"""
workloads/fsync-log-tree/workload.py
--------------------------------------
Stress workload for BtrfsFsyncLogTree.tla (CVE-2024-37354)

Race window targeted:
    A file has preallocated extents beyond i_size.
    Thread A: fsync() — reads the extent map, starts logging extents to log tree
    Thread B: write() — extends i_size into the preallocated region
    If Thread B's write completes between Thread A's extent map read and
    Thread A's log_one_extent() call, Thread A logs the prealloc extent
    AND the new regular extent for the same file offset range.
    This creates a duplicate key in the log tree, triggering a BUG().

What makes this tricky:
    1. Preallocation is essential: the race only occurs on files with
       FALLOC_FL_KEEP_SIZE prealloc extents beyond i_size.
    2. The write must extend i_size (not just overwrite existing data).
    3. The fsync must be concurrent with the write — not before or after.
    4. The file must not have been fsynced recently (log tree must be
       in a state where it needs to log the prealloc extents).
    5. We use multiple files and threads to maximize concurrency.

Kernel versions affected: Linux < 6.3 (fixed in commit 1e2f5f...),
    and some backport-affected stable kernels.

Expected trace events:
    FsyncFile_Enter, LogInode_Enter, LogOneExtent, DropExtents_Enter,
    DropExtents_Done (ret != 0 on buggy kernel -> VIOLATION)

Invariant checked: NoLogTreeDuplicate

Usage:
    mount -t btrfs /dev/sdb /mnt/btrfs
    python3 workload.py --mount /mnt/btrfs --files 32 --threads 8 --duration 120
"""

import argparse
import ctypes
import os
import random
import threading
import time

# fallocate(2) constants
FALLOC_FL_KEEP_SIZE = 0x01

# Load libc for fallocate
libc = ctypes.CDLL("libc.so.6", use_errno=True)


def fallocate_prealloc(fd: int, offset: int, length: int) -> int:
    """Preallocate extents beyond i_size (FALLOC_FL_KEEP_SIZE)."""
    return libc.fallocate(fd, FALLOC_FL_KEEP_SIZE, offset, length)


def setup_file(path: str, file_size: int, prealloc_size: int) -> None:
    """
    Create a file with:
      - file_size bytes of actual data (sets i_size)
      - prealloc_size bytes of preallocated extents beyond i_size
    This is the precondition for the CVE-2024-37354 race.
    """
    with open(path, "wb") as f:
        # Write initial data to set i_size
        f.write(os.urandom(file_size))
        f.flush()
        # Preallocate beyond i_size
        fallocate_prealloc(f.fileno(), file_size, prealloc_size)
        os.fsync(f.fileno())


def fsync_thread(paths: list, stop_event: threading.Event, stats: dict):
    """
    Continuously fsyncs files from the shared list.
    This is Thread A in the race: reads extent map, logs extents.
    The race window is between the extent map read and log_one_extent().
    """
    while not stop_event.is_set():
        if not paths:
            time.sleep(0.001)
            continue
        path = random.choice(paths)
        try:
            with open(path, "r+b") as f:
                os.fsync(f.fileno())
            stats["fsyncs"] += 1
        except (FileNotFoundError, OSError):
            pass


def writer_thread(paths: list, file_size: int, prealloc_size: int,
                  stop_event: threading.Event, stats: dict):
    """
    Continuously writes into the preallocated region, extending i_size.
    This is Thread B in the race: extends i_size into prealloc.

    The write must land in the preallocated region (offset >= file_size)
    to trigger the race. We write exactly at file_size to maximize the
    chance of hitting the window where fsync is mid-log.
    """
    while not stop_event.is_set():
        if not paths:
            time.sleep(0.001)
            continue
        path = random.choice(paths)
        try:
            with open(path, "r+b") as f:
                # Write at the boundary: file_size..file_size+4096
                # This extends i_size into the preallocated region
                f.seek(file_size)
                f.write(os.urandom(min(4096, prealloc_size)))
                f.flush()
                # Do NOT fsync here — we want the write to be in pagecache
                # when the fsync thread reads the extent map
            stats["writes"] += 1
        except (FileNotFoundError, OSError):
            pass


def resetter_thread(paths: list, file_size: int, prealloc_size: int,
                    stop_event: threading.Event, stats: dict):
    """
    Periodically resets files back to the prealloc state.
    This ensures the race condition can repeat: after a write extends
    i_size, we truncate back and re-preallocate.
    """
    while not stop_event.is_set():
        if not paths:
            time.sleep(0.1)
            continue
        path = random.choice(paths)
        try:
            with open(path, "r+b") as f:
                # Truncate back to file_size
                f.truncate(file_size)
                f.flush()
                # Re-preallocate beyond i_size
                fallocate_prealloc(f.fileno(), file_size, prealloc_size)
                os.fsync(f.fileno())
            stats["resets"] += 1
        except (FileNotFoundError, OSError):
            pass
        time.sleep(0.05)


def main():
    parser = argparse.ArgumentParser(description="Fsync log tree stress workload (CVE-2024-37354)")
    parser.add_argument("--mount",        required=True,       help="Btrfs mount point")
    parser.add_argument("--files",        type=int, default=32, help="Number of test files")
    parser.add_argument("--threads",      type=int, default=8,  help="Threads per role")
    parser.add_argument("--duration",     type=int, default=120, help="Run duration (seconds)")
    parser.add_argument("--file-size",    type=int, default=4096,
                        help="Initial file size in bytes (default: 4096 = one leaf extent)")
    parser.add_argument("--prealloc-size", type=int, default=65536,
                        help="Prealloc size beyond i_size (default: 64KB = 16 extents)")
    args = parser.parse_args()

    workdir = os.path.join(args.mount, "fsync_log_tree_stress")
    os.makedirs(workdir, exist_ok=True)

    print(f"[fsync-log-tree] Setting up {args.files} files "
          f"(size={args.file_size}B, prealloc={args.prealloc_size}B)...")
    paths = []
    for i in range(args.files):
        p = os.path.join(workdir, f"testfile_{i:04d}")
        setup_file(p, args.file_size, args.prealloc_size)
        paths.append(p)
    print(f"[fsync-log-tree] Files ready. Starting {args.threads * 3} threads for {args.duration}s.")
    print(f"[fsync-log-tree] Run bpftrace btrfs_fsync_log_tree.bt in another terminal.")

    stop = threading.Event()
    stats = {"fsyncs": 0, "writes": 0, "resets": 0}
    threads = []

    for _ in range(args.threads):
        threads.append(threading.Thread(
            target=fsync_thread, args=(paths, stop, stats), daemon=True))
    for _ in range(args.threads):
        threads.append(threading.Thread(
            target=writer_thread, args=(paths, args.file_size, args.prealloc_size, stop, stats),
            daemon=True))
    for _ in range(max(1, args.threads // 4)):
        threads.append(threading.Thread(
            target=resetter_thread, args=(paths, args.file_size, args.prealloc_size, stop, stats),
            daemon=True))

    for t in threads:
        t.start()

    start = time.time()
    while time.time() - start < args.duration:
        time.sleep(5)
        elapsed = time.time() - start
        print(f"[fsync-log-tree] {elapsed:.0f}s: "
              f"fsyncs={stats['fsyncs']} writes={stats['writes']} resets={stats['resets']}")

    stop.set()
    for t in threads:
        t.join(timeout=5)

    print(f"[fsync-log-tree] Done. Total: fsyncs={stats['fsyncs']} "
          f"writes={stats['writes']} resets={stats['resets']}")
    print(f"[fsync-log-tree] Check bpftrace output for LogOneExtent/DropExtents events.")


if __name__ == "__main__":
    main()
