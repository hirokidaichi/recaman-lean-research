#!/usr/bin/env python3
"""Exact independent replay of the frozen arbitrary-prefix countermodel family."""
import hashlib
from math import isqrt
from pathlib import Path
import subprocess


def check(prefix_horizon: int) -> None:
    value, prefix = 0, {0}
    for clock in range(1, prefix_horizon + 1):
        candidate = value - clock
        value = candidate if candidate > 0 and candidate not in prefix else value + clock
        prefix.add(value)
    w = 2 * (max(prefix) // 2 + 1)
    d = max(10, 2 * ((isqrt(w + 16) + 4) // 2 + 1))
    assert d % 2 == 0 and d * d - 8 * d > w
    v = d * d + w
    j = v // 2
    h = v + 1 + 3 * j
    n = 16 * h + (2 if h % 2 else 0)
    b, c, value = n - 2, n + 2 * j + 1, 3 * n + h - 1
    seed = prefix | {0, value, v - 1}
    seed.update(v + 3 * k for k in range(1, j + 1))
    seed.update((k - 2) * c + v + k * (k - 3) // 2 for k in range(4, d + 1))
    assert prefix.issubset(seed)
    assert len(seed) <= b + 1 and max(seed) <= b * (b + 1) // 2
    assert value % 2 == (b * (b + 1) // 2) % 2
    assert 16 * v < 7 * h
    seed_size = len(seed)
    seen = seed
    residue = value % b
    word = "SS" + "AS" * j + "S" + "A" * d + "S" * d
    uses: dict[int, int] = {}
    for clock, expected in enumerate(word, b + 1):
        candidate = value - clock
        blocked = candidate > 0 and candidate in seen
        sign = "S" if candidate > 0 and not blocked else "A"
        assert sign == expected, (prefix_horizon, clock, sign, expected)
        if c + 5 < clock < c + 2 * d and blocked:
            uses[candidate] = uses.get(candidate, 0) + 1
        value = candidate if sign == "S" else value + clock
        seen.add(value)
        next_residue = value % clock
        assert next_residue <= residue, (prefix_horizon, clock, residue, next_residue)
        residue = next_residue
        if clock == c:
            assert value == v and v - 1 in seen and 2 * c + v + 2 in seen
        if n <= clock < c:
            k = (clock - n) // 2
            expected_value = n + h - k if (clock - n) % 2 == 0 else 2 * n + h + 1 + k
            assert value == expected_value
    assert clock == c + 2 * d and value == w and w > max(prefix)
    assert len(uses) == d - 5 and max(uses.values()) == 1
    next_landing = clock
    for clock in range(next_landing + 1, next_landing + 2 * w + 5):
        candidate = value - clock
        value = candidate if candidate > 0 and candidate not in seen else value + clock
        seen.add(value)
        next_residue = value % clock
        if next_residue > residue:
            break
        residue = next_residue
    else:
        raise AssertionError("arc completion not found within two-step residue bound")
    print(f"prefix={prefix_horizon} prefix_size={len(prefix)} prefix_max={max(prefix)} "
          f"w={w} D={d} v={v} J={j} h={h} n={n} b={b} c={c} "
          f"seed_size={seed_size} ratio_slack={16*v-7*h} "
          f"next_landing={next_landing} wrap={clock} "
          f"blocked_uses={len(uses)} max_multiplicity=1 PASS", flush=True)


def main() -> None:
    print("protocol=H-20260906-07", flush=True)
    print("source_revision=" + subprocess.check_output(
        ["git", "rev-parse", "HEAD"], text=True).strip(), flush=True)
    print("source_sha256=" + hashlib.sha256(Path(__file__).read_bytes()).hexdigest(), flush=True)
    for prefix_horizon in (0, 4, 128, 1000, 10000, 200000):
        check(prefix_horizon)


if __name__ == "__main__":
    main()
