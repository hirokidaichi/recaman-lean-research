#!/usr/bin/env python3
"""Audit positive blocker multiplicity after canonical l3blocked events.

The input trace must start at clock 1 and use the format emitted by
arc_death_rule_probe.cpp.  The comb table identifies l3blocked events in
completed arcs.  For each event clock s, the audited excursion ends at the
first e > s which is either a residue wrap or a late landing.  A use at t is
counted when s < t < e and the positive subtraction candidate a(t-1)-t was
already in the canonical history, hence forced an addition.
"""

from __future__ import annotations

import argparse
from collections import Counter
from dataclasses import dataclass, field
from pathlib import Path


@dataclass
class Excursion:
    c: int
    s: int
    e: int | None = None
    end_reason: str = ""
    total_uses: int = 0
    uses: dict[int, list[int]] = field(default_factory=dict)

    def count(self, candidate: int, clock: int) -> None:
        self.total_uses += 1
        self.uses.setdefault(candidate, []).append(clock)

    @property
    def max_multiplicity(self) -> int:
        return max((len(clocks) for clocks in self.uses.values()), default=0)


def parse_comb_events(path: Path, max_clock: int) -> list[Excursion]:
    events: list[Excursion] = []
    with path.open(encoding="utf-8") as rows:
        for raw in rows:
            fields = raw.split()
            if not fields:
                continue
            if fields[0] == "#":
                continue
            if len(fields) != 34:
                raise ValueError(
                    f"expected 34 columns in comb table, got {len(fields)}"
                )
            if (
                fields[11] == "1"
                and fields[12] == "l3blocked"
                and fields[20] == "1"
            ):
                c = int(fields[1])
                s = c + int(fields[16])
                if s <= max_clock:
                    events.append(Excursion(c=c, s=s))
    events.sort(key=lambda event: event.s)
    if len({event.s for event in events}) != len(events):
        raise ValueError("multiple l3blocked records share an event clock")
    return events


def audit_trace(path: Path, events: list[Excursion], max_clock: int) -> tuple[int, int]:
    by_start = {event.s: event for event in events}
    active: list[Excursion] = []
    first_birth = {0: 0}
    previous_value = 0
    previous_residue = 0
    expected_clock = 1
    recurrence_checks = 0

    with path.open(encoding="utf-8") as rows:
        for raw in rows:
            if raw.startswith("#") or not raw.strip():
                continue
            clock_text, value_text, quotient_text, residue_text, step = raw.split()
            clock = int(clock_text)
            value = int(value_text)
            quotient = int(quotient_text)
            residue = int(residue_text)
            if clock != expected_clock:
                raise ValueError(
                    f"trace must be contiguous from 1: expected {expected_clock}, got {clock}"
                )
            if clock > max_clock:
                break
            candidate = previous_value - clock if previous_value > clock else None
            candidate_seen = candidate is not None and candidate in first_birth
            expected_step = "S" if candidate is not None and not candidate_seen else "A"
            expected_value = candidate if expected_step == "S" else previous_value + clock
            if step != expected_step or value != expected_value:
                raise ValueError(
                    f"recurrence mismatch at {clock}: got {value} {step}, "
                    f"expected {expected_value} {expected_step}"
                )
            if value != quotient * clock + residue or not 0 <= residue < clock:
                raise ValueError(f"quotient/residue mismatch at {clock}")
            recurrence_checks += 1

            wrapped = clock > 1 and residue > previous_residue
            late = value < clock
            survivors: list[Excursion] = []
            for event in active:
                if wrapped or late:
                    event.e = clock
                    event.end_reason = "wrap" if wrapped else "late"
                else:
                    if candidate is not None and candidate_seen:
                        event.count(candidate, clock)
                    survivors.append(event)
            active = survivors

            first_birth.setdefault(value, clock)
            if clock in by_start:
                active.append(by_start[clock])
            previous_value = value
            previous_residue = residue
            expected_clock += 1

    if expected_clock - 1 < max_clock:
        raise ValueError(
            f"trace ended at {expected_clock - 1}, before requested clock {max_clock}"
        )
    unresolved = [event.s for event in events if event.e is None]
    if unresolved:
        raise ValueError(f"completed-arc events have no endpoint in trace: {unresolved}")
    return recurrence_checks, len(first_birth)


def split_name(s: int, discovery_end: int) -> str:
    return "discovery" if s <= discovery_end else "holdout"


def report(events: list[Excursion], discovery_end: int, max_clock: int,
           recurrence_checks: int, first_birth_count: int) -> str:
    lines = [
        "l3blocked positive-blocker multiplicity audit",
        f"ranges: discovery 1<=s<={discovery_end}; "
        f"holdout {discovery_end}<s<={max_clock}",
        f"recurrence checks={recurrence_checks} mismatches=0 "
        f"distinct visited values={first_birth_count}",
    ]
    for name in ("discovery", "holdout"):
        sample = [event for event in events if split_name(event.s, discovery_end) == name]
        total_uses = sum(event.total_uses for event in sample)
        max_mult = max((event.max_multiplicity for event in sample), default=0)
        end_reasons = Counter(event.end_reason for event in sample)
        violations = sum(
            1
            for event in sample
            for clocks in event.uses.values()
            if len(clocks) > 2
        )
        lines.append(
            f"{name}: excursions={len(sample)} positive blocked uses={total_uses} "
            f"max multiplicity={max_mult} violations(>2)={violations} "
            f"endpoints late={end_reasons['late']} wrap={end_reasons['wrap']}"
        )

    repeated = sorted(
        (
            event.c,
            event.s,
            event.e,
            candidate,
            clocks,
        )
        for event in events
        for candidate, clocks in event.uses.items()
        if len(clocks) >= 2
    )
    lines.append(f"resources with multiplicity>=2: {len(repeated)}")
    for c, s, e, candidate, clocks in repeated[:20]:
        birth = "unknown"
        # The recurrence audit guarantees prior membership; the exact birth is
        # recovered in a second lightweight pass only for displayed witnesses.
        lines.append(
            f"  c={c} s={s} e={e} w={candidate} firstBirth={birth} "
            f"uses={','.join(map(str, clocks))}"
        )
    return "\n".join(lines) + "\n"


def add_witness_births(text: str, trace: Path) -> str:
    candidates = {
        int(part.split("=", 1)[1])
        for line in text.splitlines()
        if line.startswith("  c=")
        for part in line.split()
        if part.startswith("w=")
    }
    births: dict[int, int] = {}
    if candidates:
        with trace.open(encoding="utf-8") as rows:
            for raw in rows:
                if raw.startswith("#") or not raw.strip():
                    continue
                clock_text, value_text, *_ = raw.split()
                value = int(value_text)
                if value in candidates and value not in births:
                    births[value] = int(clock_text)
                    if len(births) == len(candidates):
                        break
    for candidate, birth in births.items():
        text = text.replace(
            f"w={candidate} firstBirth=unknown", f"w={candidate} firstBirth={birth}"
        )
    return text


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("comb_ends", type=Path)
    parser.add_argument("trace", type=Path)
    parser.add_argument("--discovery-end", type=int, required=True)
    parser.add_argument("--holdout-end", type=int, required=True)
    args = parser.parse_args()
    if not 1 <= args.discovery_end < args.holdout_end:
        parser.error("require 1 <= discovery-end < holdout-end")
    events = parse_comb_events(args.comb_ends, args.holdout_end)
    checks, births = audit_trace(args.trace, events, args.holdout_end)
    output = report(events, args.discovery_end, args.holdout_end, checks, births)
    print(add_witness_births(output, args.trace), end="")


if __name__ == "__main__":
    main()
