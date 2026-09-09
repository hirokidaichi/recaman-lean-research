#!/usr/bin/env python3
"""H-20260908-02 proposer/falsifier: closed-form all-L potential.

Discovery only on frozen L=3,7,11 potentials. Propose at most one F, then
falsify exhaustively on L=3,7 and on a sample of L=11. One repair allowed.
Does not claim E-070. Does not kill or restart L=23.
"""
from __future__ import annotations

import gzip
import hashlib
import json
import subprocess
from collections import Counter, deque
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


def p2_lags(mask: int, horizon: int) -> list[int]:
    hits = []
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
            hits.append(d)
    return hits


def bitstring(mask: int, L: int) -> str:
    return "".join("A" if (mask >> i) & 1 else "S" for i in range(L))


def newest_arun(mask: int, L: int) -> int:
    r = 0
    for i in range(L):
        if (mask >> i) & 1:
            r += 1
        else:
            break
    return r


def s_positions(mask: int, L: int) -> tuple[int, ...]:
    return tuple(i + 1 for i in range(L) if ((mask >> i) & 1) == 0)


def charge(mask: int, bit: int, L: int) -> int:
    if bit == 0:
        return -1
    return 1 if is_supplied(mask, L) else 0


def reconstruct_witnesses(L: int, P: list[int], limit: int = 30) -> list[dict]:
    """Min-length history achieving P[v] for high-P states (virtual source)."""
    size = 1 << L
    bound = size - 1
    supported = [is_supplied(m, L) for m in range(size)]
    parent = [-1] * size
    via = [-1] * size
    # longest-path DAG on a copy: reconstruct by incoming equality
    high = [m for m in range(size) if P[m] == max(P)]
    out = []
    for v in high[:limit]:
        # BFS backward along tight edges, prefer short
        prev = {v: None}
        q = deque([v])
        found = None
        while q:
            x = q.popleft()
            if P[x] == 0:
                found = x
                break
            # incoming: y -> x via bit = x&1, y = (x>>1) | (oldbit << (L-1))
            bit = x & 1
            y_low = x >> 1
            for old in (0, 1):
                y = y_low | (old << (L - 1))
                w = supported[y] if bit else -1
                if P[y] + w == P[x] and y not in prev:
                    prev[y] = (x, bit)
                    q.append(y)
        if found is None:
            out.append({"state": bitstring(v, L), "P": P[v], "witness": None})
            continue
        # walk forward from found to v
        word = []
        y = found
        while y != v:
            x, bit = prev[y]
            word.append("A" if bit else "S")
            y = x
        out.append(
            {
                "state": bitstring(v, L),
                "P": P[v],
                "start": bitstring(found, L),
                "start_P": P[found],
                "word_old_to_new": "".join(word),
            }
        )
    return out


def replay_window_from_zero(mask: int, L: int) -> tuple[int, list[int]]:
    """Replay the L bits of the window oldest-first, starting from 0."""
    # oldest is bit L-1, then L-2, ..., bit 0 newest
    s = 0
    bound = (1 << L) - 1
    height = 0
    heights = []
    for i in range(L - 1, -1, -1):
        bit = (mask >> i) & 1
        w = charge(s, bit, L)
        height += w
        heights.append(height)
        s = ((s << 1) | bit) & bound
    return height, heights


def future_allA_supplies(mask: int, L: int) -> int:
    bound = (1 << L) - 1
    n = 0
    s = mask
    for _ in range(L):
        if is_supplied(s, L):
            n += 1
        s = ((s << 1) | 1) & bound
    return n


def max_prefix_height(mask: int, L: int) -> int:
    _, hs = replay_window_from_zero(mask, L)
    return max([0] + hs)


def disjoint_p2_in_window(mask: int, L: int) -> int:
    """Greedy newest-first packing of P2 intervals using distinct A endpoints."""
    # For each A-position t (0=newest as the 'current' after that bit exists),
    # we consider the history as bits of the window. Walk oldest to newest;
    # whenever the current prefix-suffix is supplied and we take A, count if
    # the P2 lags don't reuse A-endpoints. Simpler: count supplied A steps
    # during the window replay from zero (intervals may overlap).
    s = 0
    bound = (1 << L) - 1
    c = 0
    for i in range(L - 1, -1, -1):
        bit = (mask >> i) & 1
        if bit and is_supplied(s, L):
            c += 1
        s = ((s << 1) | bit) & bound
    return c


def aas_count(mask: int, L: int) -> int:
    """Count occurrences of newest-first AAS as a consecutive triple."""
    c = 0
    for i in range(L - 2):
        trip = (mask >> i) & 7
        if trip == 0b011:  # bit0=A, bit1=A, bit2=S
            c += 1
    return c


def floor_arun(mask: int, L: int) -> int:
    r = newest_arun(mask, L)
    return (r + 1) // 4


def main() -> None:
    print("protocol=H-20260908-02 potential formula discovery/falsify", flush=True)
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

    for L in (3, 7, 11):
        P = load_potential(L)
        allA = (1 << L) - 1
        print(
            json.dumps(
                {
                    "L": L,
                    "P_allA": P[allA],
                    "maxP": max(P),
                    "n_max": sum(1 for x in P if x == max(P)),
                },
                sort_keys=True,
            ),
            flush=True,
        )
        # feature correlation at this L
        feats = Counter()
        mismatches = {name: 0 for name in ("arun4", "replay", "maxh", "p2pack", "aas", "fut")}
        for m in range(1 << L):
            r = newest_arun(m, L)
            replay, hs = replay_window_from_zero(m, L)
            maxh = max([0] + hs)
            pack = disjoint_p2_in_window(m, L)
            aas = aas_count(m, L)
            fut = future_allA_supplies(m, L)
            pred = {
                "arun4": (r + 1) // 4,
                "replay": max(0, replay),
                "maxh": maxh,
                "p2pack": pack,
                "aas": aas,
                "fut": fut,
            }
            for name, val in pred.items():
                if val != P[m]:
                    mismatches[name] += 1
        print("FEATURE_MISMATCH_" + json.dumps({"L": L, **mismatches}), flush=True)

        if L in (3, 7):
            print("WITNESSES_L%d=" % L + json.dumps(reconstruct_witnesses(L, P)), flush=True)
            rows = []
            for m in range(1 << L):
                if P[m] == 0:
                    continue
                rows.append(
                    {
                        "w": bitstring(m, L),
                        "P": P[m],
                        "sup": int(is_supplied(m, L)),
                        "lags": p2_lags(m, L),
                        "arun": newest_arun(m, L),
                        "S": list(s_positions(m, L)),
                        "replay": replay_window_from_zero(m, L)[0],
                        "maxh": max_prefix_height(m, L),
                        "pack": disjoint_p2_in_window(m, L),
                        "fut": future_allA_supplies(m, L),
                    }
                )
            rows.sort(key=lambda r: (-r["P"], r["w"]))
            print("NONZERO_L%d=" % L + json.dumps(rows), flush=True)

    # L=15,19 only all-A and max (cheap: load full array)
    for L in (15, 19):
        P = load_potential(L)
        allA = (1 << L) - 1
        # top states
        mx = max(P)
        high = [bitstring(m, L) for m in range(1 << L) if P[m] == mx]
        print(
            json.dumps(
                {
                    "L": L,
                    "P_allA": P[allA],
                    "maxP": mx,
                    "n_max": len(high),
                    "high_sample": high[:12],
                    "allA_is_max": P[allA] == mx,
                },
                sort_keys=True,
            ),
            flush=True,
        )


if __name__ == "__main__":
    main()
