#!/usr/bin/env python3
"""
workloads/space-reservation/workload.py
-----------------------------------------
Stress workload for BtrfsSpaceReservation.tla (NoOverCommit, NoStarvation)

Race window targeted:
    Btrfs uses a "space reservation" model: operations reserve metadata
    space before modifying the tree. If too many operations reserve space
    concurrently without committing, the total reserved bytes can exceed
    the available metadata space (over-commit), leading to ENOSPC even
    when space is available.

    The NoStarvation property: every reservation request must eventually
    either succeed or return ENOSPC — it must not block forever.

What makes this tricky:
    1. We fill the filesystem to ~90% capacity to minimize headroom.
    2. We run many concurrent metadata-heavy operations (create/delete
       files, setxattr, rename) that each reserve metadata space.
    3. We avoid flushing (no sync/fsync) to keep reservations outstanding.
    4. We use a mix of operations that reserve different amounts:
       - File creation: 1 metadata reservation
       - xattr set: 1 metadata reservation
       - rename: 2 metadata reservations (src + dst directory)
       - hardlink: 1 metadata reservation
    5. The async reclaim path (btrfs_async_reclaim_metadata_space) is
       triggered when reservations approach the limit — we want to see
       this in the trace.

Expected trace events:
    ReserveMetadata_Enter/OK/ENOSPC, UnreserveMetadata,
    AsyncReclaim_Triggered, UpdateBytesMAyUse, PeriodicStats

Invariant checked: NoOverCommit, NoStarvation

Usage:
    mount -t btrfs /dev/sdb /mnt/btrfs
    python3 workload.py --mount /mnt/btrfs --fill 0.85 --threads 64 --duration 120
"""

import argparse
import os
import random
import shutil
import string
import threading
import time


def random_name(n=12):
    return "".join(random.choices(string.ascii_lowercase + string.digits, k=n))


def fill_filesystem(mount: str, target_fraction: float):
    """Fill the filesystem to target_fraction of total capacity."""
    total, used, free = shutil.disk_usage(mount)
    target_used = int(total * target_fraction)
    to_write = target_used - used
    if to_write <= 0:
        print(f"[space-rsv] Filesystem already at {used/total:.1%}, skipping fill")
        return

    fill_dir = os.path.join(mount, "space_fill")
    os.makedirs(fill_dir, exist_ok=True)
    written = 0
    chunk = 64 * 1024 * 1024  # 64MB chunks
    n = 0
    print(f"[space-rsv] Filling filesystem to {target_fraction:.0%} "
          f"({to_write // (1024**2)}MB to write)...")
    while written < to_write:
        size = min(chunk, to_write - written)
        try:
            with open(os.path.join(fill_dir, f"fill_{n}"), "wb") as f:
                f.write(b"\x00" * size)
            written += size
            n += 1
        except OSError:
            break
    print(f"[space-rsv] Fill done: {written // (1024**2)}MB written")


def metadata_hammer(mount: str, tid: int, stop: threading.Event, stats: dict):
    """
    Creates, renames, sets xattrs on, and deletes files rapidly.
    Each operation reserves metadata space. The goal is to have many
    outstanding reservations simultaneously.
    """
    base = os.path.join(mount, f"space_rsv_{tid}")
    os.makedirs(base, exist_ok=True)
    files = []

    while not stop.is_set():
        try:
            op = random.randint(0, 4)

            if op == 0 or not files:
                # Create file — 1 metadata reservation
                name = os.path.join(base, random_name())
                with open(name, "wb") as f:
                    f.write(os.urandom(random.randint(1, 4096)))
                    # NO fsync — keep reservation outstanding
                files.append(name)
                stats["creates"] += 1

            elif op == 1 and files:
                # Set xattr — 1 metadata reservation
                path = random.choice(files)
                os.setxattr(path, b"user.stress", os.urandom(64))
                stats["xattrs"] += 1

            elif op == 2 and len(files) >= 2:
                # Rename — 2 metadata reservations (src dir + dst dir)
                src = random.choice(files)
                dst = os.path.join(base, random_name())
                os.rename(src, dst)
                files.remove(src)
                files.append(dst)
                stats["renames"] += 1

            elif op == 3 and files:
                # Hardlink — 1 metadata reservation
                src = random.choice(files)
                dst = os.path.join(base, random_name())
                try:
                    os.link(src, dst)
                    files.append(dst)
                    stats["links"] += 1
                except OSError:
                    pass

            elif op == 4 and files:
                # Delete — releases reservation
                victim = files.pop(random.randint(0, len(files) - 1))
                try:
                    os.unlink(victim)
                    stats["deletes"] += 1
                except FileNotFoundError:
                    pass

        except OSError as e:
            if e.errno == 28:  # ENOSPC
                stats["enospc"] += 1
                # Back off briefly to let reclaim run
                time.sleep(0.01)
            else:
                pass


def main():
    parser = argparse.ArgumentParser(description="Space reservation stress workload")
    parser.add_argument("--mount",    required=True,         help="Btrfs mount point")
    parser.add_argument("--fill",     type=float, default=0.85, help="Fill fraction (0.0–0.95)")
    parser.add_argument("--threads",  type=int,   default=64, help="Worker threads")
    parser.add_argument("--duration", type=int,   default=120, help="Run duration (seconds)")
    args = parser.parse_args()

    # Fill filesystem to near capacity
    fill_filesystem(args.mount, args.fill)

    stop  = threading.Event()
    stats = {"creates": 0, "xattrs": 0, "renames": 0, "links": 0,
             "deletes": 0, "enospc": 0}
    threads = []

    print(f"[space-rsv] Starting {args.threads} metadata hammer threads for {args.duration}s.")
    print(f"[space-rsv] Run bpftrace btrfs_space_reservation.bt in another terminal.")

    for i in range(args.threads):
        t = threading.Thread(target=metadata_hammer,
                             args=(args.mount, i, stop, stats), daemon=True)
        threads.append(t)
        t.start()

    start = time.time()
    while time.time() - start < args.duration:
        time.sleep(10)
        elapsed = time.time() - start
        total, used, free = shutil.disk_usage(args.mount)
        print(f"[space-rsv] {elapsed:.0f}s: creates={stats['creates']} "
              f"renames={stats['renames']} enospc={stats['enospc']} "
              f"disk={used/total:.1%}")

    stop.set()
    for t in threads:
        t.join(timeout=5)

    print(f"[space-rsv] Done. ENOSPC count: {stats['enospc']}. "
          f"Check bpftrace output for ReserveMetadata/AsyncReclaim events.")


if __name__ == "__main__":
    main()
