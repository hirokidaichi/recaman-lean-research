#!/usr/bin/env python3
"""H-20260908-01: finite lag-11 window types and gap-type charge search.

P2 at lag d iff d=2k+1, k odd, and the k negative 1-indexed offsets in 1..d
sum to d(d+1)/4. Discovery is the finite list of 5-subsets of {1..11}
summing to 33; no period census is performed here.
"""
from __future__ import annotations

import hashlib
import itertools
import json
import pathlib
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[2]
OUT = ROOT / "docs/data/issue73_20260908/lag11"


def p2_offsets(d: int) -> list[tuple[int, ...]]:
    k = (d - 1) // 2
    target = d * (d + 1) // 4
    return [s for s in itertools.combinations(range(1, d + 1), k) if sum(s) == target]


def has_prefix_p2(offsets: tuple[int, ...], prefix: int) -> bool:
    inside = tuple(x for x in offsets if x <= prefix)
    k = (prefix - 1) // 2
    if len(inside) != k:
        return False
    return sum(inside) == prefix * (prefix + 1) // 4


def following_gap_options(offsets: tuple[int, ...]) -> list[dict]:
    """Charge targets inside the window.

    j=0 is the most recent S. Its following gap runs through the addition
    at t, so only a lower bound is known. j>0 has an exact following gap
    equal to the distance to the next more-recent S.
    """
    o = sorted(offsets)
    options = []
    for j, charged in enumerate(o):
        shift = -j
        if j == 0:
            gap_kind = "ge"
            gap = charged + 1
        else:
            gap_kind = "eq"
            gap = charged - o[j - 1]
        options.append(
            {
                "shift": shift,
                "charged_offset": charged,
                "gap_kind": gap_kind,
                "gap": gap,
                "u7_pool_overlap": u7_overlap(gap_kind, gap),
            }
        )
    return options


def u7_overlap(kind: str, gap: int) -> list[str]:
    """Candidate pools used by the audited U7 injection."""
    hits = []
    if kind == "eq" and gap == 1:
        hits.append("lag7_h1_gap=1")
    if kind == "eq" and gap == 3:
        hits.append("lag7_h2_gap=3")
    if kind == "eq" and gap >= 4:
        hits.append("lag3_gap>=4")
    if kind == "ge":
        # last-S: actual gap may be any integer >= `gap`
        if gap <= 1:
            hits.append("lag7_h1_gap=1")
        if gap <= 3:
            hits.append("lag7_h2_gap=3")
        hits.append("lag3_gap>=4")
    return hits


def assign_free_exact(types: list[dict]) -> dict:
    """Try to give every minimal type an exact internal gap outside {1,3,>=4}.

    Safe exact gaps relative to U7 pools: 2, and nothing else, unless we later
    prove incompatibility with lag-3 AAS. First attempt uses only gap=2.
    """
    remaining = []
    chosen = []
    for row in types:
        free = [o for o in row["options"] if o["gap_kind"] == "eq" and o["gap"] == 2]
        if not free:
            remaining.append(row)
            continue
        # prefer the unique option if possible; otherwise keep all for matching
        chosen.append({"type": row["offsets"], "options": free})
    return {"gap2_assigned": chosen, "no_gap2": [r["offsets"] for r in remaining]}


def greedy_unique_slots(types: list[dict], allow_gaps: set[int]) -> dict:
    """Assign each type a (shift, exact_gap, charged_offset) slot.

    Slots with the same (shift, gap, charged_offset) may be shared: t is
    recovered as image + charged_offset. Slots that only share gap, with
    distinct charged offsets, are kept but flagged as same-gap-multi-offset.
    """
    used = {}
    assignment = []
    failed = []
    for row in types:
        options = [
            o
            for o in row["options"]
            if o["gap_kind"] == "eq" and o["gap"] in allow_gaps
        ]
        options.sort(key=lambda o: (len(o["u7_pool_overlap"]), o["gap"], -o["shift"]))
        placed = False
        for o in options:
            slot = (o["shift"], o["gap"], o["charged_offset"])
            used.setdefault(slot, []).append(row["offsets"])
            assignment.append({"type": row["offsets"], "slot": list(slot), "option": o})
            placed = True
            break
        if not placed:
            failed.append(row["offsets"])
    by_gap = {}
    for (shift, gap, charged), members in used.items():
        by_gap.setdefault(gap, []).append(
            {"shift": shift, "charged_offset": charged, "types": members}
        )
    multi = {
        gap: slots
        for gap, slots in by_gap.items()
        if len({(s["shift"], s["charged_offset"]) for s in slots}) > 1
    }
    return {
        "assignment": assignment,
        "failed": failed,
        "slots": {str(k): v for k, v in used.items()},
        "same_gap_multi_offset": multi,
    }


def main() -> None:
    OUT.mkdir(parents=True, exist_ok=True)
    print("protocol=H-20260908-01 lag-11 finite type classification", flush=True)
    print(
        "source_revision="
        + subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip(),
        flush=True,
    )
    print(
        "script_sha256="
        + hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),
        flush=True,
    )

    raw = p2_offsets(11)
    assert len(raw) == 29
    lag3 = p2_offsets(3)
    lag7 = p2_offsets(7)
    print("lag3_types=" + json.dumps(lag3), flush=True)
    print("lag7_types=" + json.dumps(lag7), flush=True)

    rows = []
    for offsets in raw:
        min3 = has_prefix_p2(offsets, 3)
        min7 = has_prefix_p2(offsets, 7)
        rows.append(
            {
                "offsets": offsets,
                "minimal": not min3 and not min7,
                "has_p2_3": min3,
                "has_p2_7": min7,
                "h": min(offsets),
                "options": following_gap_options(offsets),
            }
        )

    minimal = [r for r in rows if r["minimal"]]
    print("raw_lag11_types=29", flush=True)
    print("minimal_lag11_types=" + str(len(minimal)), flush=True)
    for r in rows:
        print(
            "TYPE "
            + json.dumps(
                {
                    "offsets": r["offsets"],
                    "minimal": r["minimal"],
                    "h": r["h"],
                    "has_p2_3": r["has_p2_3"],
                    "has_p2_7": r["has_p2_7"],
                    "n_free_eq2": sum(
                        1
                        for o in r["options"]
                        if o["gap_kind"] == "eq" and o["gap"] == 2
                    ),
                    "options": r["options"],
                }
            ),
            flush=True,
        )

    gap2 = assign_free_exact(minimal)
    print("GAP2_SUMMARY=" + json.dumps(gap2["no_gap2"]), flush=True)
    print(
        "GAP2_COUNTS="
        + json.dumps(
            {
                "with_gap2": len(gap2["gap2_assigned"]),
                "without_gap2": len(gap2["no_gap2"]),
            }
        ),
        flush=True,
    )

    att_gap2 = greedy_unique_slots(minimal, {2})
    print(
        "ASSIGN_GAP2_ONLY="
        + json.dumps({"failed": att_gap2["failed"], "multi": att_gap2["same_gap_multi_offset"]}),
        flush=True,
    )

    # One permitted repair: also allow exact gaps that sit inside >=4,
    # but only as a diagnostic. A proof using these must still separate
    # lag3 images; this is not itself a proof.
    att_all = greedy_unique_slots(minimal, set(range(1, 12)) - {1, 3})
    print(
        "ASSIGN_EXACT_EXCEPT_1_3="
        + json.dumps(
            {
                "failed": att_all["failed"],
                "multi": {str(k): v for k, v in att_all["same_gap_multi_offset"].items()},
                "n_assigned": len(att_all["assignment"]),
            }
        ),
        flush=True,
    )

    payload = {
        "raw": 29,
        "minimal": [
            {
                "offsets": r["offsets"],
                "h": r["h"],
                "options": r["options"],
            }
            for r in minimal
        ],
        "non_minimal": [r["offsets"] for r in rows if not r["minimal"]],
        "gap2_only": att_gap2,
        "exact_except_1_3": att_all,
    }
    (OUT / "classification.json").write_text(json.dumps(payload, indent=2, default=str) + "\n")
    print("wrote " + str(OUT / "classification.json"), flush=True)

    if att_gap2["failed"]:
        print(
            "CONCLUSION=gap=2 does not cover all minimal types; "
            "period-independent U7-disjoint exact-gap-2 charge FAILS as a uniform rule",
            flush=True,
        )
    else:
        print("CONCLUSION=every minimal type has an exact gap-2 charge option", flush=True)

    if att_all["failed"]:
        print("STOP_CANDIDATE=no exact-gap assignment outside {1,3} for some type", flush=True)
    print("COMPLETE: finite type list only; not an all-period theorem", flush=True)


if __name__ == "__main__":
    sys.exit(main())
