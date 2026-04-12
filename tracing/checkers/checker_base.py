"""
checker_base.py
---------------
Shared base class for all Btrfs TLA+ trace conformance checkers.

Each subsystem checker subclasses BtrfsChecker, overrides process_event()
to maintain per-subsystem state, and calls self.violation() when an
invariant is breached.

Usage pattern:
    checker = MySubsystemChecker()
    checker.run(sys.stdin)   # reads JSON lines from stdin
    sys.exit(checker.exit_code())
"""

import json
import sys
from dataclasses import dataclass, field
from typing import Any, Dict, List, Optional


@dataclass
class TraceEvent:
    ts: int
    tid: int
    comm: str
    action: str
    raw: Dict[str, Any] = field(default_factory=dict)

    @classmethod
    def from_json(cls, line: str) -> Optional["TraceEvent"]:
        line = line.strip()
        if not line or line.startswith("#"):
            return None
        try:
            d = json.loads(line)
            return cls(
                ts=d.get("ts", 0),
                tid=d.get("tid", 0),
                comm=d.get("comm", "?"),
                action=d.get("action", ""),
                raw=d,
            )
        except json.JSONDecodeError:
            return None


class BtrfsChecker:
    """Base class for all Btrfs trace invariant checkers."""

    def __init__(self, name: str, invariant: str):
        self.name = name
        self.invariant = invariant
        self._violations: List[Dict[str, Any]] = []
        self._event_count = 0
        self._conforming = True

    # ------------------------------------------------------------------ #
    # Subclass interface                                                   #
    # ------------------------------------------------------------------ #

    def process_event(self, event: TraceEvent) -> None:
        """Override in subclass to handle each event and update state."""
        raise NotImplementedError

    # ------------------------------------------------------------------ #
    # Helpers for subclasses                                               #
    # ------------------------------------------------------------------ #

    def violation(self, event: TraceEvent, message: str) -> None:
        """Record an invariant violation."""
        v = {
            "ts": event.ts,
            "tid": event.tid,
            "comm": event.comm,
            "action": event.action,
            "message": message,
        }
        self._violations.append(v)
        self._conforming = False
        print(
            f"[VIOLATION] ts={event.ts} tid={event.tid} comm={event.comm!r} "
            f"action={event.action!r}: {message}",
            file=sys.stderr,
        )

    # ------------------------------------------------------------------ #
    # Runner                                                               #
    # ------------------------------------------------------------------ #

    def run(self, stream) -> None:
        """Read JSON events from stream and check invariants."""
        print(f"[{self.name}] Checking invariant: {self.invariant}")
        for line in stream:
            event = TraceEvent.from_json(line)
            if event is None:
                continue
            self._event_count += 1
            # Inline violation events emitted by bpftrace script itself
            if event.action.startswith("VIOLATION_"):
                self.violation(event, f"bpftrace inline violation: {event.action}")
                continue
            self.process_event(event)
        self._report()

    def _report(self) -> None:
        print(f"\n[{self.name}] Summary")
        print(f"  Events processed : {self._event_count}")
        print(f"  Violations found : {len(self._violations)}")
        if self._conforming:
            print(f"  Result           : CONFORMS to {self.invariant}")
        else:
            print(f"  Result           : VIOLATES {self.invariant}")
            for i, v in enumerate(self._violations, 1):
                print(f"  [{i}] ts={v['ts']} tid={v['tid']} {v['message']}")

    def exit_code(self) -> int:
        return 0 if self._conforming else 1
