#!/usr/bin/env python3
"""Finite falsification of Q1 and the fixed Q3 witness; not a proof of Q2.

Protocol: H-20260906-03. The canonical recurrence is replayed independently
with an ordinary Python set. A no-freshness variant is a negative control.
"""

from __future__ import annotations

import hashlib
from pathlib import Path
import subprocess


def main() -> None:
    discovery_end, holdout_end = 1000, 200000
    revision = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], text=True
    ).strip()
    print(f"source_revision={revision}")
    print(f"source_sha256={hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}")
    print(f"discovery=0..{discovery_end} holdout={discovery_end + 1}..{holdout_end}")
    first, last = {0: 0}, {0: 0}
    value = 0
    repeats = {"discovery": 0, "holdout": 0}
    violations = {"discovery": 0, "holdout": 0}
    prefix_four: set[int] = {0}
    boundary_examples: list[tuple[int, int, int]] = []
    for clock in range(1, holdout_end + 1):
        candidate = value - clock
        value = candidate if candidate > 0 and candidate not in first else value + clock
        split = "discovery" if clock <= discovery_end else "holdout"
        if value in last:
            repeats[split] += 1
            violations[split] += int(clock > value)
            if len(boundary_examples) < 3:
                boundary_examples.append((value, last[value], clock))
        first.setdefault(value, clock)
        last[value] = clock
        if clock <= 4:
            prefix_four.add(value)
        if clock == 131:
            assert value == 4
    assert 4 not in prefix_four
    assert first[4] == 131
    assert violations == {"discovery": 0, "holdout": 0}
    for split in ("discovery", "holdout"):
        print(f"{split}: repeat_events={repeats[split]} Q1_violations={violations[split]}")
    print(f"first_repeat_examples_(value,earlier,later)={boundary_examples}")
    print(f"Q3: m=4 H=4 prefix={sorted(prefix_four)} first_occurrence=131 PASS")
    print("Q2: no finite computation is used as evidence of an infinite tail")

    # Deliberately weaken precisely the freshness condition, keeping step
    # positivity and the addition branch. This is not the canonical orbit.
    value, first = 0, {0: 0}
    for clock in range(1, 1001):
        candidate = value - clock
        value = candidate if candidate > 0 else value + clock
        if value in first and clock > value:
            print(f"without_freshness: Q1 REFUTED value={value} earlier={first[value]} later={clock}")
            break
        first.setdefault(value, clock)
    else:
        raise AssertionError("negative control did not falsify Q1")


if __name__ == "__main__":
    main()
