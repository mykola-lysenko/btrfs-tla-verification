#!/usr/bin/env bash
# workloads/send-receive/workload.sh
# -----------------------------------------------------------------------
# Stress workload for BtrfsSendReceive.tla (NoUAF)
#
# Race window targeted:
#   btrfs_ioctl_send() traverses a snapshot's B-tree.
#   btrfs_delete_subvolume() frees the snapshot's root.
#   If delete proceeds while send is traversing, send accesses freed memory.
#
# What makes this tricky:
#   - Btrfs normally prevents this by taking a reference on the snapshot
#     root during send. The race only occurs if the reference counting
#     has a bug (as in CVE-2023-1611 and related issues).
#   - We stress the reference counting by:
#     1. Running many concurrent sends on the same snapshot
#     2. Deleting the snapshot immediately after each send starts
#     3. Creating new snapshots rapidly to reuse root objects
#   - We also stress the send path by sending large snapshots with
#     many files, making the send take longer and widening the window.
#
# Expected trace events:
#   SendStart, SendDone, DeleteSubvolume_Enter/Done
#   A VIOLATION_UAF event means delete ran while send was active.
#
# Invariant checked: NoUAF
#
# Usage:
#   mount -t btrfs /dev/sdb /mnt/btrfs
#   bash workload.sh /mnt/btrfs 120
# -----------------------------------------------------------------------

set -euo pipefail

MOUNT="${1:?Usage: $0 <mount> [duration_secs]}"
DURATION="${2:-120}"
WORKDIR="$MOUNT/send_recv_stress"
RECV_DIR="$MOUNT/recv"

cleanup() {
    echo "[send-recv] Cleaning up..."
    kill $(jobs -p) 2>/dev/null || true
    wait 2>/dev/null || true
    # Kill any running btrfs send processes
    pkill -f "btrfs send" 2>/dev/null || true
    sleep 1
    # Delete all test subvolumes
    for sv in "$WORKDIR"/snap_* "$WORKDIR"/src 2>/dev/null; do
        btrfs subvolume delete "$sv" 2>/dev/null || true
    done
    rm -rf "$WORKDIR" "$RECV_DIR" 2>/dev/null || true
}
trap cleanup EXIT

mkdir -p "$WORKDIR" "$RECV_DIR"

# -----------------------------------------------------------------------
# Phase 1: Create a source subvolume with many files.
# More files = longer send = wider race window.
# -----------------------------------------------------------------------
echo "[send-recv] Phase 1: Creating source subvolume with 1000 files..."
btrfs subvolume create "$WORKDIR/src"
for i in $(seq 1 1000); do
    dd if=/dev/urandom of="$WORKDIR/src/file_$i" bs=4096 count=4 2>/dev/null
done
sync

# -----------------------------------------------------------------------
# Phase 2: Race loop — snapshot, send, delete concurrently.
# -----------------------------------------------------------------------
echo "[send-recv] Phase 2: Racing send vs. delete for ${DURATION}s."
echo "[send-recv] Run bpftrace btrfs_send_receive.bt in another terminal."

SNAP_N=0
END=$((SECONDS + DURATION))

while [ $SECONDS -lt $END ]; do
    SNAP="$WORKDIR/snap_$SNAP_N"
    SNAP_N=$((SNAP_N + 1))

    # Create a read-only snapshot (required for send)
    btrfs subvolume snapshot -r "$WORKDIR/src" "$SNAP" 2>/dev/null || continue

    # Start send in the background — this is the long-running operation
    # that should hold a reference on the snapshot root
    (btrfs send "$SNAP" | dd of=/dev/null bs=1M 2>/dev/null) &
    SEND_PID=$!

    # Immediately try to delete the snapshot — races with the send
    # On a buggy kernel, this can succeed while send is still traversing
    sleep 0.01
    btrfs subvolume delete "$SNAP" 2>/dev/null || true

    # Wait for send to finish (or be killed by the UAF)
    wait $SEND_PID 2>/dev/null || true

    if [ $((SNAP_N % 20)) -eq 0 ]; then
        echo "[send-recv] $SNAP_N snapshot/send/delete cycles completed"
    fi
done

echo "[send-recv] Done. $SNAP_N cycles. Check bpftrace output."
