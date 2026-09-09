#!/usr/bin/env python3
"""H-20260908-03: exhaustive U=A search on frozen unused periods.

A positive-sum word with every addition P2-supplied (unrestricted lag
1..p(p+1)) refutes E-067 and E-070. Clean exhaustive ranges are COMPUTED.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]


def all_supplied(word: tuple[int, ...]) -> tuple[bool, dict[int, list[int]]]:
    p = len(word)
    s = sum(word)
    if s <= 0:
        return False, {}
    # prefix on two periods for short lags, then closed form for wraps
    sig: dict[int, list[int]] = {}
    for t, step in enumerate(word):
        if step < 0:
            continue
        back = [word[(t - i) % p] for i in range(1, p + 1)]
        weight = sum(i * e for i, e in enumerate(back, 1))
        prefix = moment = 0
        hits: list[int] = []
        for r in range(p):
            if s != 0:
                quot, rem = divmod(1 - prefix, s)
                d = quot * p + r
                if rem == 0 and quot >= 0 and d > 0:
                    value = (
                        quot * weight
                        + p * s * quot * (quot - 1) // 2
                        + quot * p * prefix
                        + moment
                    )
                    if value == 0:
                        hits.append(d)
            prefix += back[r]
            moment += (r + 1) * back[r]
        if not hits:
            return False, {}
        sig[t] = hits
    return True, sig


def naive_hits(word: tuple[int, ...], t: int) -> list[int]:
    p = len(word)
    total = moment = 0
    hits = []
    for d in range(1, p * (p + 1) + 1):
        e = word[(t - d) % p]
        total += e
        moment += d * e
        if total == 1 and moment == 0:
            hits.append(d)
    return hits


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--min-period", type=int, required=True)
    parser.add_argument("--max-period", type=int, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    print("protocol=H-20260908-03 exhaustive U=A counterword search", flush=True)
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
    print(f"period_range=({args.min_period},{args.max_period})", flush=True)

    # Negative control: SSSSAAAASAAA must not be reported as U=A.
    control = tuple(1 if c == "A" else -1 for c in "SSSSAAAASAAA")
    ok, sig = all_supplied(control)
    print("control_SSSSAAAASAAA_UA=" + json.dumps(ok), flush=True)
    if ok:
        raise SystemExit("control failed: known unsupplied word reported as U=A")

    total_pos = 0
    ua = 0
    missing_hist = {}
    for p in range(args.min_period, args.max_period + 1):
        npos = 0
        nua = 0
        limit = 1 << p
        for mask in range(limit):
            word = tuple(1 if (mask >> i) & 1 else -1 for i in range(p))
            if sum(word) <= 0:
                continue
            npos += 1
            supplied, sig = all_supplied(word)
            if supplied:
                nua += 1
                # independent naive replay
                replay = {t: naive_hits(word, t) for t, e in enumerate(word) if e > 0}
                assert all(replay[t] for t in replay)
                witness = {
                    "period": p,
                    "word": "".join("A" if e > 0 else "S" for e in word),
                    "sign_sum": sum(word),
                    "mask": mask,
                    "suppliers": sig,
                    "naive": replay,
                    "positive_words_before": total_pos + npos,
                }
                args.output.write_text(json.dumps(witness, indent=2, sort_keys=True) + "\n")
                print("COUNTEREXAMPLE=" + json.dumps(witness, sort_keys=True), flush=True)
                print("STOP: E-067/E-070 refuted", flush=True)
                return
        total_pos += npos
        ua += nua
        print(
            json.dumps({"period": p, "positive_words": npos, "U_eq_A": nua}),
            flush=True,
        )
    summary = {
        "min_period": args.min_period,
        "max_period": args.max_period,
        "positive_words": total_pos,
        "U_eq_A": ua,
    }
    args.output.write_text(json.dumps(summary, indent=2) + "\n")
    print("NO_COUNTEREXAMPLE=" + json.dumps(summary, sort_keys=True), flush=True)
    print("COMPLETE: exhaustive clean range is COMPUTED, not a proof", flush=True)


if __name__ == "__main__":
    sys.exit(main())
