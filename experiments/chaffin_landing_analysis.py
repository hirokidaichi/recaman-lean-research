#!/usr/bin/env python3
"""Per-decade analysis of Ben Chaffin's Recaman landing table and hole list.

Inputs (download from https://benchaffin.com/recaman/):
  rec-landings-1e612.txt   every arc minimum ("landing") up to 10^612 terms
  rec-holes-2_32.txt       every value below 2^32 not visited after 10^612 terms
Usage: chaffin_landing_analysis.py LANDINGS HOLES
The script only counts; it makes no claim beyond the printed numbers.
"""
import collections
import math
import re
import sys


def main() -> None:
    landings_path, holes_path = sys.argv[1], sys.argv[2]
    landings = []
    with open(landings_path) as handle:
        for line in handle:
            match = re.match(r"landing: r\[(\d+)\] = (\d+)", line.strip())
            if match:
                landings.append((int(match.group(1)), int(match.group(2))))
    print(f"landings={len(landings)} lastIndexDecade={len(str(landings[-1][0])) - 1}")
    blocks = collections.defaultdict(list)
    for index, value in landings:
        if index < 10:
            continue
        li, lv = math.log10(index), math.log10(value)
        blocks[int(li // 50)].append((li, lv))
    print("block n perDecade maxDepthRatio minValueExp maxDepthExp")
    for block in sorted(blocks):
        rows = blocks[block]
        print(f"[{50 * block},{50 * block + 50}) {len(rows)} {len(rows) / 50:.2f} "
              f"{max((li - lv) / li for li, lv in rows):.3f} "
              f"{min(lv for li, lv in rows):.1f} {max(li - lv for li, lv in rows):.1f}")
    print("landings with value < 1e7 and index >= 1e9:")
    for index, value in landings:
        if index >= 10**9 and value < 10**7:
            print(f"  index=10^{math.log10(index):.2f} value={value}")
    ratios = sorted((math.log10(i) - math.log10(v)) / math.log10(i)
                    for i, v in landings if i > 10**20)
    n = len(ratios)
    print(f"depthRatio(index>1e20) n={n} median={ratios[n // 2]:.3f} "
          f"q90={ratios[int(n * 0.9)]:.3f} q99={ratios[int(n * 0.99)]:.3f} max={ratios[-1]:.3f}")
    holes = 0
    by_decade = collections.Counter()
    first = []
    with open(holes_path) as handle:
        for line in handle:
            line = line.strip()
            if not line:
                continue
            if "-" in line:
                lo, hi = (int(x) for x in line.split("-"))
            else:
                lo = hi = int(line)
            holes += hi - lo + 1
            by_decade[len(str(lo)) - 1] += hi - lo + 1
            if len(first) < 300:
                first.extend(range(lo, min(hi, lo + 50) + 1))
    print(f"holes<2^32 after 1e612: {holes} density={holes / 2**32:.6f} byDecade={dict(sorted(by_decade.items()))}")
    print(f"first 300 holes mod 3: {dict(collections.Counter(h % 3 for h in first[:300]))}")
    print(f"first 30 holes: {first[:30]}")


if __name__ == "__main__":
    main()
