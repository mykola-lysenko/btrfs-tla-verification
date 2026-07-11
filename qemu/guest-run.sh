#!/usr/bin/env bash
# qemu/guest-run.sh — runs INSIDE the QEMU guest (via vng --exec).
#
# Sets up a scratch btrfs on the virtio disks attached by run-vm-trace.sh,
# then runs the workload + bpftrace + checker harness.
#
# Usage: bash guest-run.sh <subsystem> <duration_secs> [edition]
#   edition: "tp" (tracepoint scripts, default) or "kprobe"
set -uo pipefail

SUBSYSTEM="${1:?usage: guest-run.sh <subsystem> <duration> [tp|kprobe]}"
DURATION="${2:-60}"
EDITION="${3:-tp}"
REPO="/repo"
MNT="/mnt/btrfs"

echo "[guest] kernel: $(uname -r)"
echo "[guest] cpus: $(nproc)"

# tracefs is needed by bpftrace for tracepoint format parsing
mountpoint -q /sys/kernel/tracing || mount -t tracefs tracefs /sys/kernel/tracing || true
TP_COUNT=$(bpftrace -l 'tracepoint:btrfs:*' 2>/dev/null | wc -l)
echo "[guest] btrfs tracepoints visible: $TP_COUNT"
if [[ "$TP_COUNT" -lt 10 ]]; then
    echo "[guest] ERROR: btrfs tracepoints missing — is CONFIG_BTRFS_FS set?"
    exit 1
fi

# Collect scratch virtio disks (attached with --disk by run-vm-trace.sh)
mapfile -t DISKS < <(ls /dev/vd[a-z] 2>/dev/null)
echo "[guest] scratch disks: ${DISKS[*]:-none}"
if [[ ${#DISKS[@]} -eq 0 ]]; then
    echo "[guest] ERROR: no virtio scratch disks found"
    exit 1
fi

MOUNT_OPTS=""
case "$SUBSYSTEM" in
    raid56)
        if [[ ${#DISKS[@]} -lt 3 ]]; then echo "[guest] need 3+ disks for raid5"; exit 1; fi
        mkfs.btrfs -f -d raid5 -m raid1 "${DISKS[@]:0:3}" >/dev/null
        DEV="${DISKS[0]}"
        ;;
    scrub)
        if [[ ${#DISKS[@]} -lt 2 ]]; then echo "[guest] need 2+ disks for raid1"; exit 1; fi
        mkfs.btrfs -f -d raid1 -m raid1 "${DISKS[@]:0:2}" >/dev/null
        DEV="${DISKS[0]}"
        ;;
    autodefrag)
        mkfs.btrfs -f "${DISKS[0]}" >/dev/null
        DEV="${DISKS[0]}"
        MOUNT_OPTS="-o autodefrag"
        ;;
    extent-buffer-lock|cow-path)
        # 4K nodesize: extent buffers fit one page, so eb->addr is always
        # mapped (the kprobe scripts read the b-tree level from the header
        # via eb->addr). Also deepens the tree — more lock traffic.
        mkfs.btrfs -f -n 4096 "${DISKS[0]}" >/dev/null
        DEV="${DISKS[0]}"
        ;;
    qgroup-race)
        # Span all scratch disks for a big metadata working set, and use a
        # small nodesize so the same metadata spreads over MORE leaves —
        # each commit and rescan touches more of the tree, widening the
        # CVE-2025-39759 window this workload targets.
        mkfs.btrfs -f -n 4096 -m single -d single "${DISKS[@]}" >/dev/null
        DEV="${DISKS[0]}"
        ;;
    *)
        mkfs.btrfs -f "${DISKS[0]}" >/dev/null
        DEV="${DISKS[0]}"
        ;;
esac

mkdir -p "$MNT"
# shellcheck disable=SC2086
mount $MOUNT_OPTS "$DEV" "$MNT"
echo "[guest] mounted $DEV at $MNT ($MOUNT_OPTS)"

# tp: tracepoint scripts (names audited against this kernel; see
#     tracing/audit_tp_fields.py). kprobe: function-entry scripts whose
#     action names match the Python checkers.
if [[ "$EDITION" == "kprobe" ]]; then
    export BPFTRACE_DIR="$REPO/tracing/bpftrace"
else
    export BPFTRACE_DIR="${BPFTRACE_DIR:-$REPO/tracing/bpftrace-tp}"
fi

bash "$REPO/workloads/run_trace_check.sh" "$SUBSYSTEM" "$MNT" "$DURATION"
RC=$?

umount "$MNT" || true
sync
echo "[guest] done, harness rc=$RC"
exit $RC
