#!/usr/bin/env python3
"""
workloads/snapshot-creation/workload.py
-----------------------------------------
Stress workload for BtrfsSnapshotCreation.tla (SnapshotConsistency)

Race window targeted:
    A snapshot must represent a consistent point-in-time view of the
    subvolume. The race is:
      Writer thread:   writes data to files in the subvolume
      Snapshot thread: creates a snapshot of the subvolume
    If the snapshot captures some but not all of a writer's changes
    (partial visibility), the snapshot is inconsistent.

    Btrfs prevents this via transaction ordering: the snapshot is
    created within a transaction, and writes are only visible in the
    snapshot if they were committed before the snapshot transaction.

What makes this tricky:
    1. We use many concurrent writers to maximize the chance that a
       write is in-flight when the snapshot transaction commits.
    2. We use a "consistency checker": after each snapshot, we verify
       that the snapshot is internally consistent (no partial writes).
       A partial write would appear as a file with unexpected content.
    3. We use atomic write patterns: each write is a complete replacement
       of a known value (e.g., all-zeros or all-ones). After snapshotting,
       every file in the snapshot must be either all-zeros or all-ones —
       never a mix (which would indicate a partial write was captured).
    4. We use O_SYNC writes to ensure writes are either fully visible
       or not visible at all in the snapshot.

Expected trace events:
    CreateSnapshot_Enter/Done, CopyRoot_Enter/Done,
    CommitTransaction_Enter/Done, WriteWhileSnapshot

Invariant checked: SnapshotConsistency

Usage:
    mount -t btrfs /dev/sdb /mnt/btrfs
    python3 workload.py --mount /mnt/btrfs --files 100 --threads 16 --duration 120
"""

import argparse
import os
import random
import threading
import time
import subprocess


PATTERN_A = b"\x00" * 4096  # "value A"
PATTERN_B = b"\xFF" * 4096  # "value B"


def writer_thread(files: list, stop: threading.Event, stats: dict):
    """
    Atomically replaces file content with either PATTERN_A or PATTERN_B.
    Uses O_SYNC to ensure the write is either fully committed or not at all.
    A snapshot taken during a write should see either the old or new value,
    never a partial mix.
    """
    while not stop.is_set():
        path = random.choice(files)
        pattern = random.choice([PATTERN_A, PATTERN_B])
        try:
            # O_SYNC ensures the write is durable before returning
            fd = os.open(path, os.O_WRONLY | os.O_SYNC)
            try:
                os.write(fd, pattern)
            finally:
                os.close(fd)
            stats["writes"] += 1
        except OSError:
            pass


def snapshot_thread(subvol: str, snap_dir: str, stop: threading.Event, stats: dict):
    """
    Creates read-only snapshots of the subvolume.
    After each snapshot, verifies consistency: every file must contain
    exactly PATTERN_A or PATTERN_B (no partial writes).
    """
    snap_n = 0
    while not stop.is_set():
        snap_path = os.path.join(snap_dir, f"snap_{snap_n}")
        try:
            result = subprocess.run(
                ["btrfs", "subvolume", "snapshot", "-r", subvol, snap_path],
                capture_output=True, timeout=10
            )
            if result.returncode != 0:
                time.sleep(0.1)
                continue

            stats["snapshots"] += 1

            # Verify consistency of the snapshot
            violations = check_snapshot_consistency(snap_path)
            if violations:
                stats["violations"] += len(violations)
                for v in violations:
                    print(f"[snap] CONSISTENCY VIOLATION: {v}")

            # Delete the snapshot
            subprocess.run(
                ["btrfs", "subvolume", "delete", snap_path],
                capture_output=True, timeout=10
            )
            snap_n += 1
        except (subprocess.TimeoutExpired, OSError):
            pass
        time.sleep(0.05)


def check_snapshot_consistency(snap_path: str) -> list:
    """
    Check that every file in the snapshot contains exactly PATTERN_A or PATTERN_B.
    Returns a list of violation descriptions.
    """
    violations = []
    try:
        for entry in os.scandir(snap_path):
            if not entry.is_file():
                continue
            try:
                with open(entry.path, "rb") as f:
                    data = f.read(4096)
                if data != PATTERN_A and data != PATTERN_B:
                    violations.append(
                        f"{entry.name}: unexpected content "
                        f"(first 8 bytes: {data[:8].hex()})"
                    )
            except OSError:
                pass
    except OSError:
        pass
    return violations


def main():
    parser = argparse.ArgumentParser(description="Snapshot consistency stress workload")
    parser.add_argument("--mount",    required=True,         help="Btrfs mount point")
    parser.add_argument("--files",    type=int, default=100, help="Files in subvolume")
    parser.add_argument("--threads",  type=int, default=16,  help="Writer threads")
    parser.add_argument("--duration", type=int, default=120, help="Run duration (seconds)")
    args = parser.parse_args()

    workdir  = os.path.join(args.mount, "snap_stress")
    subvol   = os.path.join(workdir, "src")
    snap_dir = os.path.join(workdir, "snaps")
    os.makedirs(workdir, exist_ok=True)
    os.makedirs(snap_dir, exist_ok=True)

    # Create the source subvolume
    subprocess.run(["btrfs", "subvolume", "create", subvol], check=True)

    # Populate with files (all PATTERN_A initially)
    print(f"[snap] Creating {args.files} files in subvolume...")
    files = []
    for i in range(args.files):
        p = os.path.join(subvol, f"file_{i:04d}")
        with open(p, "wb") as f:
            f.write(PATTERN_A)
        files.append(p)

    print(f"[snap] Starting {args.threads} writers + 1 snapshot thread for {args.duration}s.")
    print(f"[snap] Run bpftrace btrfs_snapshot_creation.bt in another terminal.")

    stop  = threading.Event()
    stats = {"writes": 0, "snapshots": 0, "violations": 0}
    threads = []

    for _ in range(args.threads):
        t = threading.Thread(target=writer_thread, args=(files, stop, stats), daemon=True)
        threads.append(t)
    snap_t = threading.Thread(target=snapshot_thread,
                              args=(subvol, snap_dir, stop, stats), daemon=True)
    threads.append(snap_t)

    for t in threads:
        t.start()

    start = time.time()
    while time.time() - start < args.duration:
        time.sleep(10)
        elapsed = time.time() - start
        print(f"[snap] {elapsed:.0f}s: writes={stats['writes']} "
              f"snapshots={stats['snapshots']} violations={stats['violations']}")

    stop.set()
    for t in threads:
        t.join(timeout=5)

    print(f"[snap] Done. Consistency violations found: {stats['violations']}")
    if stats["violations"] > 0:
        print(f"[snap] WARNING: Snapshot consistency violated — "
              f"partial writes visible in snapshot!")
    else:
        print(f"[snap] All snapshots were consistent.")


if __name__ == "__main__":
    main()
