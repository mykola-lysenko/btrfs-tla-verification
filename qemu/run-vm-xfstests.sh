#!/usr/bin/env bash
# qemu/run-vm-xfstests.sh — boot the btrfs kernel under QEMU/KVM (inside
# docker) and run xfstests in the guest as a TRACED workload.
#
# xfstests is built into the btrfs-trace image (/opt/xfstests); its qgroup
# and quota groups are pre-built adversarial workloads — historical race
# reproducers — for the trace-validated models. The trace lands in
# workloads/results/xfstests_<TS>/ alongside the per-test xfstests results,
# ready for models/trace-validated/validate-trace.sh.
#
# Usage:
#   bash run-vm-xfstests.sh <check args...>
#     e.g. bash run-vm-xfstests.sh btrfs/022
#          bash run-vm-xfstests.sh -g qgroup
#
# Env overrides:
#   SUBSYSTEM — tracer/checker to attach (default qgroup)
#   EDITION   — kprobe (default; matches the TLA+ models) or tp
#   KSRC, CPUS, MEM, NDISKS, IMAGE, SCRATCH — as in run-vm-trace.sh
#   XFSTESTS_TIMEOUT — hard cap on the whole ./check run (default 3600s)
set -euo pipefail

[[ $# -ge 1 ]] || { echo "Usage: $0 <check args...>  (e.g. $0 -g qgroup)"; exit 1; }
CHECK_ARGS="$*"

SUBSYSTEM="${SUBSYSTEM:-qgroup}"
EDITION="${EDITION:-kprobe}"
QEMU_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_DIR="$(dirname "$QEMU_DIR")"
KSRC="${KSRC:-$HOME/qemu-btrfs/btrfs-devel-for-next}"
CPUS="${CPUS:-8}"
MEM="${MEM:-8G}"
NDISKS="${NDISKS:-4}"
IMAGE="${IMAGE:-btrfs-trace:latest}"
BZIMAGE="$KSRC/arch/x86/boot/bzImage"
SCRATCH="${SCRATCH:-$HOME/qemu-btrfs/scratch}"

[[ -f "$BZIMAGE" ]] || { echo "ERROR: kernel not built: $BZIMAGE (run build-kernel.sh)"; exit 1; }

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
    -e XFSTESTS_TIMEOUT="${XFSTESTS_TIMEOUT:-3600}" \
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
        -- bash /repo/qemu/guest-xfstests.sh "$CHECK_ARGS" "$EDITION" "$SUBSYSTEM"
