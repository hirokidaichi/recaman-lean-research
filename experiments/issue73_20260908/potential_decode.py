#!/usr/bin/env python3
"""Decode frozen L=3,7,11,15,19 potentials into suffix statistics.

Hypothesis to falsify: P_L(s) equals the number of pending exact P2
contacts, or a bounded function of unsupplied A-suffixes. One formula
is allowed; it must recover validity on L=7 (Lean potential) and L=3.
"""
from __future__ import annotations

import gzip
import hashlib
import json
import subprocess
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SRC = ROOT / "docs/data/issue73_20260907"
OUT = ROOT / "docs/data/issue73_20260908/potential"


def load_potential(L: int) -> list[int]:
    gz = SRC / f"automaton_L{L}_potential.txt.gz"
    raw = gzip.decompress(gz.read_bytes()).decode()
    vals = [int(line) for line in raw.splitlines() if line != ""]
    assert len(vals) == 1 << L
    return vals


def is_supplied(mask: int, horizon: int) -> bool:
    for d in range(3, horizon + 1, 4):
        bits = mask & ((1 << d) - 1)
        if bits.bit_count() != (d + 1) // 2:
            continue
        moment = 0
        b = bits
        while b:
            low = b & -b
            moment += low.bit_length()
            b -= low
        if moment == d * (d + 1) // 4:
            return True
    return False


def pending_almost_p2(mask: int, horizon: int) -> int:
    """Number of lags d<=horizon whose signed sum is 1+2=3? No.

    Count windows that become P2 after appending one S, or that already
    are P2. Used only as a candidate statistic.
    """
    count = 0
    for d in range(3, horizon + 1, 4):
        bits = mask & ((1 << d) - 1)
        a = bits.bit_count()
        moment = 0
        b = bits
        while b:
            low = b & -b
            moment += low.bit_length()
            b -= low
        target_a = (d + 1) // 2
        target_m = d * (d + 1) // 4
        if a == target_a and moment == target_m:
            count += 1
        # one extra A or one extra S away: not used as a claim
    return count


def bitstring(mask: int, L: int) -> str:
    # LSB newest, A=1
    return "".join("A" if (mask >> i) & 1 else "S" for i in range(L))


def main() -> None:
    OUT.mkdir(parents=True, exist_ok=True)
    print("protocol=H-20260908-02 potential decode", flush=True)
    print(
        "source_revision="
        + subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip(),
        flush=True,
    )
    print(
        "script_sha256="
        + hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        flush=True,
    )

    lean7 = [0] * 128
    for s in [55, 63, 95, 111, 119, 127]:
        lean7[s] = 2
    for s in [7, 15, 23, 31, 39, 47, 59, 61, 62, 71, 79, 87, 91, 93, 94, 103, 110, 123, 125, 126]:
        lean7[s] = 1

    for L in (3, 7, 11, 15, 19):
        P = load_potential(L)
        counts = Counter(P)
        supplied = sum(1 for m in range(1 << L) if is_supplied(m, L))
        p2c = [pending_almost_p2(m, L) for m in range(1 << L)]
        # correlation of P with supplied and with p2-count
        pairs = Counter((P[m], p2c[m], int(is_supplied(m, L))) for m in range(1 << L))
        print(
            "POTENTIAL_SUMMARY="
            + json.dumps(
                {
                    "L": L,
                    "counts": dict(sorted(counts.items())),
                    "max": max(P),
                    "supplied_states": supplied,
                    "P_vs_p2count_supplied": {str(k): v for k, v in pairs.items()},
                },
                sort_keys=True,
            ),
            flush=True,
        )
        if L == 7:
            delta = sum(abs(P[m] - lean7[m]) for m in range(128))
            # potentials are unique up to additive constant; compare after shift
            shift = P[0] - lean7[0]
            delta_shift = sum(abs(P[m] - (lean7[m] + shift)) for m in range(128))
            print(
                json.dumps({"L7_vs_lean_l1": delta, "L7_vs_lean_shifted_l1": delta_shift, "shift": shift}),
                flush=True,
            )
            high = [m for m in range(128) if P[m] == max(P)]
            print("L7_MAX_STATES=" + json.dumps([bitstring(m, 7) for m in high]), flush=True)
        if L in (3, 7, 11):
            by_p = {}
            for m, val in enumerate(P):
                by_p.setdefault(val, []).append(bitstring(m, L))
            (OUT / f"L{L}_states_by_potential.json").write_text(
                json.dumps({str(k): v for k, v in sorted(by_p.items())}, indent=2) + "\n"
            )

    # Candidate F: P = min(k, number of P2 hits in the window)? check L=7
    P7 = load_potential(7)
    hits7 = [pending_almost_p2(m, 7) for m in range(128)]
    print(
        "L7_P_vs_p2hits=" + json.dumps(Counter(zip(P7, hits7))),
        flush=True,
    )
    print("COMPLETE: decode only; formula not yet claimed", flush=True)


if __name__ == "__main__":
    main()
