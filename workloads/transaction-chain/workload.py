#!/usr/bin/env python3
"""
workloads/transaction-chain/workload.py
-----------------------------------------
Stress workload for BtrfsTransactionChain.tla (NoDeadlock, CVE-2025-71194)

Race window targeted:
    An ordered extent worker calls btrfs_start_transaction(TRANS_JOIN).
    If the current transaction is in TRANS_STATE_COMMIT_START, TRANS_JOIN
    should return -EBUSY and the worker should retry — but the buggy code
    calls wait_current_trans() unconditionally, which waits for the
    transaction to commit. Meanwhile, the commit is waiting for the
    ordered extent to complete. Circular wait = deadlock.

What makes this tricky:
    1. The race requires an ordered extent to be in-flight during a
       transaction commit. We achieve this by:
       - Writing large files (forces ordered extents)
       - Calling sync() to trigger transaction commit
       - Having concurrent writers that keep ordered extents alive
    2. The TRANS_JOIN path is taken by internal Btrfs operations
       (not user-visible), so we trigger it indirectly via:
       - btrfs_setxattr (uses TRANS_JOIN for small metadata updates)
       - btrfs_update_inode (uses TRANS_JOIN)
       - fallocate (uses TRANS_JOIN for extent reservation)
    3. We use many threads to maximize the chance that a TRANS_JOIN
       call lands exactly when a commit is in TRANS_STATE_COMMIT_START.

Expected trace events:
    StartTransaction_Done, CommitTransaction_Enter/Done,
    WaitCurrentTrans_Enter/Done (long wait -> potential deadlock)

Invariant checked: NoDeadlock

Usage:
    mount -t btrfs /dev/sdb /mnt/btrfs
    python3 workload.py --mount /mnt/btrfs --threads 32 --duration 120
"""

import argparse
import os
import random
import string
import subprocess
import threading
import time


def random_name(n=8):
    return "".join(random.choices(string.ascii_lowercase, k=n))


def large_writer(mount: str, tid: int, stop: threading.Event, stats: dict):
    """
    Writes large files to generate ordered extents.
    Ordered extents are the key ingredient: they must be in-flight
    when the transaction commit starts.
    """
    base = os.path.join(mount, f"txchain_large_{tid}")
    os.makedirs(base, exist_ok=True)
    while not stop.is_set():
        try:
            name = os.path.join(base, random_name())
            # 1MB–8MB: large enough to generate multiple ordered extents
            size = random.randint(1, 8) * 1024 * 1024
            with open(name, "wb") as f:
                f.write(os.urandom(size))
                # Do NOT fsync — we want ordered extents pending in memory
                # when the commit starts
            stats["large_writes"] += 1
            # Occasionally delete to keep space available
            if random.random() < 0.3:
                try:
                    os.unlink(name)
                except FileNotFoundError:
                    pass
        except OSError:
            pass


def xattr_writer(mount: str, tid: int, stop: threading.Event, stats: dict):
    """
    Sets xattrs on files — this uses TRANS_JOIN internally.
    TRANS_JOIN is the transaction type that triggers the CVE-2025-71194
    deadlock when it encounters TRANS_STATE_COMMIT_START.
    """
    base = os.path.join(mount, f"txchain_xattr_{tid}")
    os.makedirs(base, exist_ok=True)
    # Pre-create some files
    files = []
    for i in range(20):
        p = os.path.join(base, f"f_{i}")
        with open(p, "wb") as f:
            f.write(b"x" * 4096)
        files.append(p)

    while not stop.is_set():
        try:
            path = random.choice(files)
            # setxattr uses TRANS_JOIN — the exact path for CVE-2025-71194
            os.setxattr(path, b"user.stress", os.urandom(64))
            stats["xattrs"] += 1
        except (FileNotFoundError, OSError):
            pass


def commit_trigger(mount: str, stop: threading.Event, stats: dict):
    """
    Periodically triggers transaction commits via sync().
    The commit must happen while ordered extents are in-flight
    (from large_writer threads) to create the deadlock window.
    """
    while not stop.is_set():
        try:
            # sync() triggers btrfs_commit_transaction
            os.sync()
            stats["commits"] += 1
        except OSError:
            pass
        # Short sleep: we want commits to happen frequently
        time.sleep(0.1)


def fallocate_worker(mount: str, tid: int, stop: threading.Event, stats: dict):
    """
    Calls fallocate() in a loop — uses TRANS_JOIN for extent reservation.
    This is another path to CVE-2025-71194.
    """
    import ctypes
    libc = ctypes.CDLL("libc.so.6", use_errno=True)
    FALLOC_FL_KEEP_SIZE = 0x01

    base = os.path.join(mount, f"txchain_falloc_{tid}")
    os.makedirs(base, exist_ok=True)
    name = os.path.join(base, "falloc_file")
    with open(name, "wb") as f:
        f.write(b"\x00" * 4096)

    while not stop.is_set():
        try:
            with open(name, "r+b") as f:
                # Preallocate then punch hole — both use TRANS_JOIN
                offset = random.randint(0, 64) * 4096
                libc.fallocate(f.fileno(), FALLOC_FL_KEEP_SIZE, offset, 4096)
                stats["fallocates"] += 1
        except OSError:
            pass
        time.sleep(0.001)


def main():
    parser = argparse.ArgumentParser(description="Transaction chain deadlock stress workload")
    parser.add_argument("--mount",    required=True,        help="Btrfs mount point")
    parser.add_argument("--threads",  type=int, default=32, help="Total threads")
    parser.add_argument("--duration", type=int, default=120, help="Run duration (seconds)")
    args = parser.parse_args()

    stop  = threading.Event()
    stats = {"large_writes": 0, "xattrs": 0, "commits": 0, "fallocates": 0}
    threads = []

    n_large    = args.threads // 4
    n_xattr    = args.threads // 4
    n_falloc   = args.threads // 4
    n_commit   = 2

    print(f"[txchain] Starting: {n_large} large writers, {n_xattr} xattr writers, "
          f"{n_falloc} fallocate workers, {n_commit} commit triggers")
    print(f"[txchain] Duration: {args.duration}s on {args.mount}")
    print(f"[txchain] Run bpftrace btrfs_transaction_chain.bt in another terminal.")

    for i in range(n_large):
        threads.append(threading.Thread(
            target=large_writer, args=(args.mount, i, stop, stats), daemon=True))
    for i in range(n_xattr):
        threads.append(threading.Thread(
            target=xattr_writer, args=(args.mount, i, stop, stats), daemon=True))
    for i in range(n_falloc):
        threads.append(threading.Thread(
            target=fallocate_worker, args=(args.mount, i, stop, stats), daemon=True))
    for _ in range(n_commit):
        threads.append(threading.Thread(
            target=commit_trigger, args=(args.mount, stop, stats), daemon=True))

    for t in threads:
        t.start()

    start = time.time()
    while time.time() - start < args.duration:
        time.sleep(10)
        elapsed = time.time() - start
        print(f"[txchain] {elapsed:.0f}s: large_writes={stats['large_writes']} "
              f"xattrs={stats['xattrs']} commits={stats['commits']} "
              f"fallocates={stats['fallocates']}")

    stop.set()
    for t in threads:
        t.join(timeout=5)

    print(f"[txchain] Done. Check bpftrace output for WaitCurrentTrans events.")


if __name__ == "__main__":
    main()
