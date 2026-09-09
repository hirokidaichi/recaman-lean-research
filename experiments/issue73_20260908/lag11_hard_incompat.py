#!/usr/bin/env python3
"""Local incompatibility of HARD=(1,4,7,10,11) with each U7 charge onto its S.

The HARD window fixes signs at t-1..t-11. A U7 image at one of those S phases
is an A-phase t' whose φ7 target equals that S. t' may be in the future.
This script only uses the forced past signs; unconstrained positions stay None.
A contradiction on forced signs means that S cannot be that kind of U7 image
whenever HARD occurs at t.
"""
from __future__ import annotations

import hashlib
import json
import subprocess

HARD = (1, 4, 7, 10, 11)
# Time relative to t: signs[k] = ε(t+k). Negative k is the past.
# Offset i in the P2 window is time t-i, i.e. key -i.
PAST = {-i: (-1 if i in HARD else 1) for i in range(1, 12)}
PAST[0] = 1  # t itself is A


def get(signs, k):
    return signs.get(k)


def force(signs, k, val, why, conflicts):
    old = signs.get(k)
    if old is None:
        signs[k] = val
        return True
    if old != val:
        conflicts.append({"offset_from_t": k, "have": old, "need": val, "why": why})
        return False
    return True


def try_lag3(target_offset):
    """lag3: t' = s+3, s=t-target_offset, pattern AAS: t'-1=A, t'-2=A, t'-3=S."""
    signs = dict(PAST)
    conflicts = []
    s = -target_offset
    tp = s + 3
    force(signs, tp, 1, "t' is A", conflicts)
    force(signs, tp - 1, 1, "lag3 AAS newest A", conflicts)
    force(signs, tp - 2, 1, "lag3 AAS mid A", conflicts)
    force(signs, tp - 3, -1, "lag3 last S", conflicts)
    # last S must be s
    if tp - 3 != s:
        conflicts.append({"why": "lag3 last-S is not the target", "tp-3": tp - 3, "s": s})
    return {"t_prime_offset": tp, "conflicts": conflicts, "forced": {str(k): v for k, v in sorted(signs.items()) if k not in PAST or signs[k] != PAST.get(k)}}


def try_lag7_h1(target_offset):
    """lag7 h1: charges to S_{l-2} = t'-7, offsets {1,6,7} are S, t'=s+7."""
    signs = dict(PAST)
    conflicts = []
    s = -target_offset
    tp = s + 7
    force(signs, tp, 1, "t' is A", conflicts)
    for off, val in {1: -1, 6: -1, 7: -1, 2: 1, 3: 1, 4: 1, 5: 1}.items():
        force(signs, tp - off, val, f"lag7h1 offset {off}", conflicts)
    if tp - 7 != s:
        conflicts.append({"why": "charge t'-7 is not target", "tp-7": tp - 7, "s": s})
    return {"t_prime_offset": tp, "conflicts": conflicts}


def try_lag7_h2(target_offset):
    """lag7 h2: charges to S_{l-1}=t'-5, offsets {2,5,7} are S, t'=s+5."""
    signs = dict(PAST)
    conflicts = []
    s = -target_offset
    tp = s + 5
    force(signs, tp, 1, "t' is A", conflicts)
    for off, val in {2: -1, 5: -1, 7: -1, 1: 1, 3: 1, 4: 1, 6: 1}.items():
        force(signs, tp - off, val, f"lag7h2 offset {off}", conflicts)
    if tp - 5 != s:
        conflicts.append({"why": "charge t'-5 is not target", "tp-5": tp - 5, "s": s})
    return {"t_prime_offset": tp, "conflicts": conflicts}


def main() -> None:
    print("protocol=H-20260908-01 HARD vs U7 local incompatibility", flush=True)
    print(
        "source_revision="
        + subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip(),
        flush=True,
    )
    print(
        "script_sha256="
        + hashlib.sha256(__import__("pathlib").Path(__file__).read_bytes()).hexdigest(),
        flush=True,
    )
    rows = []
    safe = []
    for off in HARD:
        rec = {
            "S_offset": off,
            "lag3": try_lag3(off),
            "lag7h1": try_lag7_h1(off),
            "lag7h2": try_lag7_h2(off),
        }
        kinds = []
        for name in ("lag3", "lag7h1", "lag7h2"):
            ok = not rec[name]["conflicts"]
            rec[name]["possible"] = ok
            if ok:
                kinds.append(name)
        rec["possible_u7_kinds"] = kinds
        if not kinds:
            safe.append(off)
        rows.append(rec)
        print("S_OFFSET=" + json.dumps({"offset": off, "possible": kinds, "n_conflicts": {k: len(rec[k]["conflicts"]) for k in ("lag3", "lag7h1", "lag7h2")}}), flush=True)
    print("SAFE_S_OFFSETS=" + json.dumps(safe), flush=True)
    if safe:
        print("CONCLUSION=HARD has S offsets that no U7 rule can occupy using only the forced past", flush=True)
    else:
        print("CONCLUSION=every HARD S is locally compatible with some U7 rule; need future signs or a different invariant", flush=True)


if __name__ == "__main__":
    main()
