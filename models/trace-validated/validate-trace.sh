#!/usr/bin/env bash
# validate-trace.sh — check that a real qgroup kernel trace is an accepted
# behavior of BtrfsQgroupLifecycle.tla.
#
# Usage:
#   bash validate-trace.sh <trace.jsonl> [max_events]
#
# COVERAGE=1 additionally prints a transition-coverage report (which model
# actions the trace exercised) via coverage_report.py.
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

# TRACE_FS selects one filesystem's event group (see trace_to_tla.py --fs)
python3 "$REPO/tracing/trace_to_tla.py" "$TRACE" -o "$DIR" --max-events "$MAX" \
        ${TRACE_FS:+--fs "$TRACE_FS"}

# -deadlock DISABLES TLC's deadlock check. Necessary: observable events can
# be ambiguous (WaitRescanCompletion_Enter is both the rescan-wait ioctl and
# close_ctree), so replay forks branches and the wrong branch dies in a
# sink state. The verdict rests solely on TraceNotDone: violated => some
# branch consumed the whole trace (ACCEPTED); TLC finishing with no error
# => every branch got stuck (DIVERGENCE).
run_tlc() {  # $1 = extra TLC args, $2 = log file
    docker run --rm \
        -v "$(dirname "$TLC_JAR")":/tlc:ro \
        -v "$DIR":/spec -w /spec \
        "$IMAGE" \
        java -XX:+UseParallelGC -Xss512m -cp /tlc/tla2tools.jar tlc2.TLC \
             -workers "$(nproc)" $1 \
             -config "${TRACE_CFG:-BtrfsQgroupTrace.cfg}" BtrfsQgroupTrace.tla > "$2" 2>&1 || true
}
LOG="$DIR/last-validate.log"
run_tlc "-deadlock -coverage 1" "$LOG"

grep -E 'states generated|distinct states' "$LOG" | head -2
NEVENTS=$(python3 - "$DIR/BtrfsQgroupTraceData.tla" <<'PY'
import re, sys
print(len(re.findall(r'action \|->', open(sys.argv[1]).read())))
PY
)

if grep -q "Invariant TraceNotDone is violated" "$LOG"; then
    # The whole trace was replayed (idx advanced past the last event).
    echo "RESULT: TRACE ACCEPTED — all $NEVENTS events are a behavior of BtrfsQgroupLifecycle"
    if [ "${COVERAGE:-0}" = "1" ]; then
        echo
        python3 "$DIR/coverage_report.py" "$LOG"
    fi
    if [ "${PROBES:-0}" = "1" ]; then
        echo
        echo "== Witness probes (did the trace enter the CVE-relevant windows?) =="
        for cfg in "$DIR"/BtrfsQgroupTrace_probe_*.cfg; do
            name="$(basename "$cfg" .cfg)"; name="${name#BtrfsQgroupTrace_probe_}"
            PLOG="$DIR/last-probe-$name.log"
            docker run --rm \
                -v "$(dirname "$TLC_JAR")":/tlc:ro \
                -v "$DIR":/spec -w /spec \
                "$IMAGE" \
                java -XX:+UseParallelGC -Xss512m -cp /tlc/tla2tools.jar tlc2.TLC \
                     -workers "$(nproc)" -deadlock \
                     -config "$(basename "$cfg")" BtrfsQgroupTrace.tla > "$PLOG" 2>&1 || true
            if grep -qE "Invariant No\w+ is violated" "$PLOG"; then
                echo "  $name: ENTERED — the trace is consistent with reaching this window"
            elif grep -q "Invariant TraceNotDone is violated" "$PLOG"; then
                echo "  $name: never entered (full replay without reaching the window)"
            else
                echo "  $name: INCONCLUSIVE — see $PLOG"
            fi
        done
    fi
    exit 0
elif grep -q "No error has been found" "$LOG"; then
    # Every replay branch got stuck before consuming the trace.
    echo "RESULT: DIVERGENCE — the model cannot explain the full trace ($NEVENTS events)"
    if [ "${DIAG:-1}" = "1" ]; then
        # Diagnostic rerun WITH deadlock checking: dumps one stuck branch.
        # Its idx is a lower bound — an ambiguity branch may die earlier
        # than the deepest (true) divergence point.
        run_tlc "" "$DIR/last-diverge.log"
        REACHED=$(grep -oE '/\\ idx = [0-9]+' "$DIR/last-diverge.log" | tail -1 | grep -oE '[0-9]+')
        echo "  one stuck branch at event ${REACHED:-?} (see $DIR/last-diverge.log; idx is a lower bound)"
    fi
    exit 1
else
    echo "RESULT: TLC ERROR OR INCONCLUSIVE — see $LOG"
    tail -20 "$LOG"
    exit 2
fi
