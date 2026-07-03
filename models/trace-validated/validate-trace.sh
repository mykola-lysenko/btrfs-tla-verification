#!/usr/bin/env bash
# validate-trace.sh — check that a real qgroup kernel trace is an accepted
# behavior of BtrfsQgroupLifecycle.tla.
#
# Usage:
#   bash validate-trace.sh <trace.jsonl> [max_events]
#
# Requires: docker image btrfs-trace:latest (has java),
#           ~/qemu-btrfs/tlc/tla2tools.jar
set -euo pipefail

TRACE="${1:?usage: validate-trace.sh <trace.jsonl> [max_events]}"
MAX="${2:-0}"
DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO="$(dirname "$(dirname "$DIR")")"
TLC_JAR="${TLC_JAR:-$HOME/qemu-btrfs/tlc/tla2tools.jar}"
IMAGE="${IMAGE:-btrfs-trace:latest}"

python3 "$REPO/tracing/trace_to_tla.py" "$TRACE" -o "$DIR" --max-events "$MAX"

LOG="$(mktemp)"
docker run --rm \
    -v "$(dirname "$TLC_JAR")":/tlc:ro \
    -v "$DIR":/spec -w /spec \
    "$IMAGE" \
    java -XX:+UseParallelGC -cp /tlc/tla2tools.jar tlc2.TLC \
         -workers "$(nproc)" -config BtrfsQgroupTrace.cfg BtrfsQgroupTrace.tla > "$LOG" 2>&1 || true

grep -E 'states generated|distinct states' "$LOG" | head -2
NEVENTS=$(python3 - "$DIR/BtrfsQgroupTraceData.tla" <<'PY'
import re, sys
print(len(re.findall(r'action \|->', open(sys.argv[1]).read())))
PY
)

if grep -q "Invariant TraceNotDone is violated" "$LOG"; then
    # The whole trace was replayed (idx advanced past the last event).
    echo "RESULT: TRACE ACCEPTED — all $NEVENTS events are a behavior of BtrfsQgroupLifecycle"
    rm -f "$LOG"; exit 0
elif grep -qE "Deadlock reached" "$LOG"; then
    # Divergence: report idx from the terminal state (how far replay got).
    REACHED=$(grep -oE '/\\ idx = [0-9]+' "$LOG" | tail -1 | grep -oE '[0-9]+')
    echo "RESULT: DIVERGENCE at event ${REACHED:-?} of $NEVENTS — the model cannot explain the trace"
    echo "  (inspect $LOG and BtrfsQgroupTraceData.tla around that index)"
    exit 1
else
    echo "RESULT: TLC ERROR OR INCONCLUSIVE — see $LOG"
    tail -20 "$LOG"
    exit 2
fi
