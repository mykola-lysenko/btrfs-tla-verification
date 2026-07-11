#!/usr/bin/env bash
# qemu/guest-xfstests.sh — runs INSIDE the QEMU guest (via vng).
#
# Runs xfstests as the traced workload: sets up TEST/SCRATCH devices on the
# virtio disks, writes /opt/xfstests/local.config, and hands the ./check
# invocation to workloads/run_trace_check.sh as WORKLOAD_OVERRIDE — so the
# bpftrace tracer, trace-fidelity rules (tmpfs buffering, ts-sort) and the
# post-hoc checker are exactly the same as for the hand-rolled workloads.
#
# Usage: bash guest-xfstests.sh "<check args>" [edition] [subsystem]
#   check args: passed to ./check verbatim, e.g. "-g qgroup" or "btrfs/022"
#   edition:    kprobe (default; action names match the TLA+ models) or tp
#   subsystem:  which tracer/checker to attach (default qgroup)
set -uo pipefail

CHECK_ARGS="${1:?usage: guest-xfstests.sh \"<check args>\" [kprobe|tp] [subsystem]}"
EDITION="${2:-kprobe}"
SUBSYSTEM="${3:-qgroup}"
REPO="/repo"
XFSTESTS="/opt/xfstests"
TEST_MNT="/mnt/test"
SCRATCH_MNT="/mnt/scratch"

echo "[guest] kernel: $(uname -r)"
echo "[guest] xfstests: $(cat $XFSTESTS/GITCOMMIT 2>/dev/null || echo '?')"

mountpoint -q /sys/kernel/tracing || mount -t tracefs tracefs /sys/kernel/tracing || true
TP_COUNT=$(bpftrace -l 'tracepoint:btrfs:*' 2>/dev/null | wc -l)
echo "[guest] btrfs tracepoints visible: $TP_COUNT"
if [[ "$TP_COUNT" -lt 10 ]]; then
    echo "[guest] ERROR: btrfs tracepoints missing — is CONFIG_BTRFS_FS set?"
    exit 1
fi

mapfile -t DISKS < <(ls /dev/vd[a-z] 2>/dev/null)
echo "[guest] virtio disks: ${DISKS[*]:-none}"
if [[ ${#DISKS[@]} -lt 2 ]]; then
    echo "[guest] ERROR: xfstests needs >= 2 disks (TEST_DEV + scratch)"
    exit 1
fi
TEST_DEV="${DISKS[0]}"
SCRATCH_POOL="${DISKS[*]:1}"

mkfs.btrfs -f "$TEST_DEV" >/dev/null
mkdir -p "$TEST_MNT" "$SCRATCH_MNT"
mount "$TEST_DEV" "$TEST_MNT"
echo "[guest] TEST_DEV=$TEST_DEV at $TEST_MNT, SCRATCH_DEV_POOL=$SCRATCH_POOL"

TS="$(date +%Y%m%d_%H%M%S)"
OUT_DIR="$REPO/workloads/results/xfstests_${TS}"
mkdir -p "$OUT_DIR/xfstests"

cat > "$XFSTESTS/local.config" <<EOF
export FSTYP=btrfs
export TEST_DEV=$TEST_DEV
export TEST_DIR=$TEST_MNT
export SCRATCH_DEV_POOL="$SCRATCH_POOL"
export SCRATCH_MNT=$SCRATCH_MNT
export RESULT_BASE=$OUT_DIR/xfstests
EOF
cp "$XFSTESTS/local.config" "$OUT_DIR/local.config"

if [[ "$EDITION" == "kprobe" ]]; then
    export BPFTRACE_DIR="$REPO/tracing/bpftrace"
else
    export BPFTRACE_DIR="${BPFTRACE_DIR:-$REPO/tracing/bpftrace-tp}"
fi

# A stuck test on a lockdep kernel can hang ./check forever; the whole run
# gets a hard cap instead (per-test results up to that point are kept).
XFSTESTS_TIMEOUT="${XFSTESTS_TIMEOUT:-3600}"
export OUT_DIR
export WORKLOAD_OVERRIDE="cd $XFSTESTS && timeout $XFSTESTS_TIMEOUT ./check $CHECK_ARGS; echo \"[guest] ./check exit: \$?\" | tee $OUT_DIR/check-exit.txt"

bash "$REPO/workloads/run_trace_check.sh" "$SUBSYSTEM" "$TEST_MNT" 0
RC=$?

umount "$SCRATCH_MNT" 2>/dev/null || true
umount "$TEST_MNT" 2>/dev/null || true
sync
echo "[guest] done, harness rc=$RC (xfstests results in $OUT_DIR/xfstests)"
exit $RC
