#!/usr/bin/env bash
# qemu/run-vm-trace.sh — boot the btrfs kernel under QEMU/KVM (inside docker)
# and run one subsystem's workload + bpftrace + checker in the guest.
#
# The container rootfs (bpftrace, btrfs-progs, python3) becomes the guest
# userspace via virtme-ng's 9p root. The repo is bind-mounted at /repo, so
# traces and reports written by the harness land in workloads/results/ on
# the host.
#
# Usage:
#   bash run-vm-trace.sh <subsystem> [duration_secs] [edition]
#     edition: "tp" (tracepoint scripts, default) or "kprobe" (function-entry
#              scripts; action names match the Python checkers)
#
# Env overrides:
#   KSRC   — kernel source dir (default ~/qemu-btrfs/btrfs-devel-for-next)
#   CPUS   — guest vCPUs (default 8)
#   MEM    — guest RAM  (default 4G)
#   NDISKS — number of 4G scratch virtio disks (default 4)
#   IMAGE  — docker image (default btrfs-trace:latest)
set -euo pipefail

SUBSYSTEM="${1:?Usage: $0 <subsystem> [duration_secs] [tp|kprobe]}"
DURATION="${2:-60}"
EDITION="${3:-tp}"

QEMU_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_DIR="$(dirname "$QEMU_DIR")"
KSRC="${KSRC:-$HOME/qemu-btrfs/btrfs-devel-for-next}"
CPUS="${CPUS:-8}"
# Note: the harness buffers the live trace in /dev/shm (= MEM/2), so large
# traces need headroom — lock-heavy subsystems produce ~1 GB/min.
MEM="${MEM:-8G}"
NDISKS="${NDISKS:-4}"
IMAGE="${IMAGE:-btrfs-trace:latest}"
BZIMAGE="$KSRC/arch/x86/boot/bzImage"
SCRATCH="${SCRATCH:-$HOME/qemu-btrfs/scratch}"

[[ -f "$BZIMAGE" ]] || { echo "ERROR: kernel not built: $BZIMAGE (run build-kernel.sh)"; exit 1; }

# Scratch disks (sparse raw files, recreated fresh each run)
mkdir -p "$SCRATCH"
DISK_ARGS=()
for i in $(seq 1 "$NDISKS"); do
    rm -f "$SCRATCH/disk$i.img"
    truncate -s 4G "$SCRATCH/disk$i.img"
    DISK_ARGS+=(--disk "/scratch/disk$i.img")
done

KVM_ARGS=()
[[ -e /dev/kvm ]] && KVM_ARGS=(--device /dev/kvm)

exec docker run --rm "${KVM_ARGS[@]}" \
    -v "$REPO_DIR":/repo \
    -v "$KSRC":/work/kernel:ro \
    -v "$SCRATCH":/scratch \
    -w /repo \
    "$IMAGE" \
    vng --run /work/kernel/arch/x86/boot/bzImage \
        --cpus "$CPUS" --memory "$MEM" \
        --force-9p --rw \
        --user root \
        --verbose \
        "${DISK_ARGS[@]}" \
        -- bash /repo/qemu/guest-run.sh "$SUBSYSTEM" "$DURATION" "$EDITION"
