#!/usr/bin/env python3
"""
workloads/extent-buffer-lock/workload.py
-----------------------------------------
Stress workload for BtrfsExtentBufferLock.tla

Race window targeted:
    The kernel enforces top-down lock ordering (root > internal > leaf).
    This workload creates a deep B-tree by inserting many small files,
    then hammers concurrent tree reads and writes across multiple threads.
    Each thread traverses the tree from different levels, maximising the
    chance that the kernel's lock ordering code is exercised under contention.

What makes this tricky:
    - Small files (4–64 bytes) force many B-tree splits, creating nodes at
      all three levels (root=3, internal=2, leaf=1).
    - Concurrent stat() + write() pairs on the same inodes force the kernel
      to acquire read locks (stat) and write locks (write) on the same path
      simultaneously from different threads.
    - The rename() calls force the kernel to lock two directory entries,
      which can involve nodes at different levels.
    - The find_first_extent_bit() calls during writeback traverse the extent
      tree top-down, which is the exact path the lock ordering invariant
      protects.

Expected trace events:
    AcquireWrite, AcquireWrite_Done, Release, AcquireRead, ReleaseRead
    (from btrfs_extent_buffer_lock.bt)

Invariant checked: NoDeadlock (top-down lock ordering)

Usage:
    mount -t btrfs /dev/sdb /mnt/btrfs
    python3 workload.py --mount /mnt/btrfs --threads 16 --duration 60
"""

import argparse
import os
import random
import string
import threading
import time


def random_name(length=8):
    return "".join(random.choices(string.ascii_lowercase, k=length))


def writer_thread(mount: str, tid: int, stop_event: threading.Event):
    """
    Continuously creates, writes, renames, and deletes small files.
    Forces B-tree modifications at leaf level while concurrent readers
    are traversing internal/root nodes.
    """
    base = os.path.join(mount, f"ebl_writer_{tid}")
    os.makedirs(base, exist_ok=True)
    files = []
    while not stop_event.is_set():
        try:
            # Create a new file with a small random payload
            name = os.path.join(base, random_name())
            with open(name, "wb") as f:
                # Vary size: 4B to 64B forces leaf-level splits
                f.write(os.urandom(random.randint(4, 64)))
                f.flush()
                os.fsync(f.fileno())
            files.append(name)

            # Rename to force directory entry locking across nodes
            if len(files) > 1:
                src = random.choice(files[:-1])
                dst = os.path.join(base, random_name())
                try:
                    os.rename(src, dst)
                    files.remove(src)
                    files.append(dst)
                except FileNotFoundError:
                    pass

            # Delete old files to trigger extent tree modifications
            if len(files) > 50:
                victim = files.pop(0)
                try:
                    os.unlink(victim)
                except FileNotFoundError:
                    pass
        except OSError:
            pass


def reader_thread(mount: str, tid: int, stop_event: threading.Event):
    """
    Continuously stats files and reads directory listings.
    Forces shared read locks on B-tree nodes while writers hold write locks.
    The interleaving of read and write lock acquisitions at different levels
    is the exact scenario the NoDeadlock invariant guards against.
    """
    while not stop_event.is_set():
        try:
            # Walk all writer directories — forces top-down tree traversal
            for entry in os.scandir(mount):
                if stop_event.is_set():
                    break
                if entry.name.startswith("ebl_writer_"):
                    try:
                        for f in os.scandir(entry.path):
                            # stat() acquires read lock on leaf node
                            f.stat()
                    except (FileNotFoundError, PermissionError):
                        pass
        except OSError:
            pass
        time.sleep(0.001)


def truncate_thread(mount: str, tid: int, stop_event: threading.Event):
    """
    Truncates files to random sizes.
    Truncation modifies the extent tree at leaf level while potentially
    holding a lock on an internal node — a known source of lock ordering
    complexity in Btrfs.
    """
    base = os.path.join(mount, f"ebl_writer_{tid % 4}")
    while not stop_event.is_set():
        try:
            entries = os.listdir(base)
            if entries:
                target = os.path.join(base, random.choice(entries))
                try:
                    with open(target, "r+b") as f:
                        f.truncate(random.randint(0, 32))
                        os.fsync(f.fileno())
                except (FileNotFoundError, IsADirectoryError):
                    pass
        except (FileNotFoundError, OSError):
            pass
        time.sleep(0.005)


def main():
    parser = argparse.ArgumentParser(description="Extent Buffer Lock stress workload")
    parser.add_argument("--mount",    required=True, help="Btrfs mount point")
    parser.add_argument("--threads",  type=int, default=16, help="Total threads")
    parser.add_argument("--duration", type=int, default=60, help="Run duration (seconds)")
    args = parser.parse_args()

    stop = threading.Event()
    threads = []

    n_writers   = args.threads // 2
    n_readers   = args.threads // 4
    n_truncators = args.threads - n_writers - n_readers

    print(f"[ebl] Starting: {n_writers} writers, {n_readers} readers, "
          f"{n_truncators} truncators for {args.duration}s on {args.mount}")

    for i in range(n_writers):
        t = threading.Thread(target=writer_thread,   args=(args.mount, i, stop), daemon=True)
        threads.append(t)
    for i in range(n_readers):
        t = threading.Thread(target=reader_thread,   args=(args.mount, i, stop), daemon=True)
        threads.append(t)
    for i in range(n_truncators):
        t = threading.Thread(target=truncate_thread, args=(args.mount, i, stop), daemon=True)
        threads.append(t)

    for t in threads:
        t.start()

    time.sleep(args.duration)
    stop.set()
    for t in threads:
        t.join(timeout=5)

    print(f"[ebl] Done. Check bpftrace output for AcquireWrite/Release events.")


if __name__ == "__main__":
    main()
