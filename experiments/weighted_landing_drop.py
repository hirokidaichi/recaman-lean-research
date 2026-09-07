#!/usr/bin/env python3
"""Frozen H-20260906-08 audit over arc_death_rule_probe's exact records."""
import argparse
from collections import Counter
import hashlib
from pathlib import Path


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("comb_ends", type=Path)
    args = parser.parse_args()
    rows = [line.split() for line in args.comb_ends.read_text().splitlines()
            if line.strip() and not line.startswith("#")]
    assert all(len(row) == 34 for row in rows)
    first_landings = {int(f[4]): int(f[5]) for f in rows}
    samples = {"discovery": [], "holdout": []}
    for f in rows:
        if not all(f[i] == "1" for i in (3, 6, 11, 17, 20)):
            continue
        c, v, j, h = (int(f[i]) for i in (1, 2, 7, 8))
        e = c + int(f[18])
        assert h == v + 1 + 3 * j
        u = first_landings[e]
        assert c < e and 0 < u < v
        row = (3 * (v - u) - 7 * j, c, v, j, e, u, f[12])
        samples["discovery" if c < 10**9 else "holdout"].append(row)
    print("protocol=H-20260906-08 discovery=c<1e9 holdout=1e9<=c<2e10")
    print("script_sha256=" + hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    print("table_sha256=" + hashlib.sha256(args.comb_ends.read_bytes()).hexdigest())
    print(f"table_records={len(rows)}")
    for split, sample in samples.items():
        bad = [r for r in sample if r[0] < 0]
        print(f"{split}: eligible={len(sample)} violations={len(bad)} "
              f"outcomes={dict(sorted(Counter(r[6] for r in sample).items()))}")
        print(f"{split}: least_slack_(slack,c,v,J,e,u,outcome)={sorted(sample)[:5]}")
        print(f"{split}: first_violations={sorted(bad, key=lambda r: r[1])[:10]}")


if __name__ == "__main__":
    main()
