#!/usr/bin/env python3
"""Exact finite-history search for H-20260906-04.

Branching chooses the initial history, never changes an already executed
greedy decision. Every subtraction target is forbidden from later preload.
Any witness is independently replayed from the final, fixed seed.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
import subprocess
import time


@dataclass(frozen=True)
class State:
    clock: int
    value: int
    required: frozenset[int]
    forbidden: frozenset[int]
    produced: frozenset[int]
    word: str


def choose(state: State, sign: str) -> State | None:
    clock = state.clock + 1
    candidate = state.value - clock
    seen = state.required | state.produced
    required, forbidden = state.required, state.forbidden
    if sign == "S":
        if candidate <= 0 or candidate in seen:
            return None
        value = candidate
        forbidden = forbidden | {candidate}
    else:
        if candidate > 0 and candidate not in seen:
            if candidate in forbidden:
                return None
            required = required | {candidate}
        value = state.value + clock
    return State(clock, value, required, forbidden,
                 state.produced | {value}, state.word + sign)


def make_prefix(v: int, n_shift: int = 0) -> tuple[State, dict[str, int]]:
    j = (9 * v - 7) // 21 + 1
    h = v + 1 + 3 * j
    n = 16 * h + (2 if h % 2 else 0) + n_shift
    assert n_shift % 4 == 0
    b, current = n - 2, 3 * n + h - 1
    state = State(b, current, frozenset({0, current, v - 1}),
                  frozenset(), frozenset({current}), "")
    for sign in "SS" + "AS" * j + "SAAAA":
        next_state = choose(state, sign)
        if next_state is None:
            raise AssertionError(f"invalid forced prefix v={v} sign={sign}")
        assert next_state.value % next_state.clock <= state.value % state.clock
        state = next_state
    c = n + 2 * j + 1
    assert state.clock == c + 4 and state.value == 4 * c + v + 10
    assert 16 * v < 7 * h
    return state, {"v": v, "J": j, "hPrev": h, "n": n,
                   "b": b, "current": current, "c": c}


def search(prefix: State, node_cap: int, deadline: float) -> tuple[str, State | None, int]:
    stack, nodes = [prefix], 0
    while stack:
        if nodes >= node_cap or time.monotonic() >= deadline:
            return "UNKNOWN", None, nodes
        state = stack.pop()
        nodes += 1
        q, r = divmod(state.value, state.clock)
        # Reaching quotient zero without a wrap must traverse q,...,1.
        # This lower bound is valid for both sign choices; additions cost more.
        if r < q * (q + 1) // 2:
            continue
        # Stack order explores a fresh subtraction first.
        for sign in ("A", "S"):
            nxt = choose(state, sign)
            if nxt is None or nxt.value % nxt.clock > r:
                continue
            if nxt.value < nxt.clock:
                return "COUNTEREXAMPLE", nxt, nodes
            stack.append(nxt)
    return "EXHAUSTED", None, nodes


def replay(witness: State, params: dict[str, int]) -> dict[str, object]:
    b, current, c, v = (params[k] for k in ("b", "current", "c", "v"))
    seed = set(witness.required)
    assert 0 in seed and current in seed
    assert not seed.intersection(witness.forbidden)
    assert len(seed) <= b + 1
    assert max(seed) <= b * (b + 1) // 2
    assert current % 2 == (b * (b + 1) // 2) % 2
    seen, value, residue = set(seed), current, current % b
    rows = [[b, value, value // b, residue, "initial"]]
    for clock, expected in enumerate(witness.word, b + 1):
        candidate = value - clock
        sign = "S" if candidate > 0 and candidate not in seen else "A"
        assert sign == expected, (clock, sign, expected)
        value = candidate if sign == "S" else value + clock
        assert value % clock <= residue
        residue = value % clock
        seen.add(value)
        rows.append([clock, value, value // clock, residue, sign])
        if clock == c:
            assert value == v and v - 1 in seen and 2 * c + v + 2 in seen
    assert value < clock and clock > c and value < v
    result: dict[str, object] = {
        "parameters": params, "seed": sorted(seed), "word": witness.word,
        "next_landing": [clock, value], "trace": rows,
        "seed_cardinality": len(seed), "seed_max": max(seed),
        "seed_constraints": "PASS", "fixed_seed_replay": "PASS",
    }
    # Finish the arc using this same history, with no further choices/preload.
    for next_clock in range(clock + 1, clock + 100001):
        candidate = value - next_clock
        value = candidate if candidate > 0 and candidate not in seen else value + next_clock
        next_residue = value % next_clock
        seen.add(value)
        if next_residue > residue:
            result["next_wrap"] = [next_clock, value]
            return result
        residue = next_residue
    raise AssertionError("counterexample arc did not complete within replay limit")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--seconds", type=int, default=900)
    parser.add_argument("--node-cap", type=int, default=100000)
    args = parser.parse_args()
    print("protocol=H-20260906-04", flush=True)
    print("source_revision=" + subprocess.check_output(
        ["git", "rev-parse", "HEAD"], text=True).strip(), flush=True)
    print("source_sha256=" + hashlib.sha256(Path(__file__).read_bytes()).hexdigest(), flush=True)
    print(f"node_cap={args.node_cap} time_cap_seconds={args.seconds}", flush=True)
    deadline = time.monotonic() + args.seconds
    results: list[dict[str, object]] = []
    total_nodes = 0
    for v in range(10, 161):
        split = "discovery" if v <= 80 else "holdout"
        prefix, params = make_prefix(v)
        status, witness, nodes = search(prefix, args.node_cap, deadline)
        total_nodes += nodes
        print(f"{split} v={v} J={params['J']} status={status} nodes={nodes}", flush=True)
        results.append({"v": v, "split": split, "status": status, "nodes": nodes})
        if witness is not None:
            found = replay(witness, params)
            # The frozen holdout changes clock scale, retaining word and seed
            # synthesis rules. A new search cannot be used as a replay success.
            shifted, shifted_params = make_prefix(v, 4 * params["n"])
            for sign in witness.word[len(prefix.word):]:
                shifted_next = choose(shifted, sign)
                assert shifted_next is not None
                shifted = shifted_next
            holdout = replay(shifted, shifted_params)
            args.out.write_text(json.dumps({"search": results, "witness": found,
                                           "clock_shift_holdout": holdout}, indent=2) + "\n")
            print(f"witness={args.out} fixed_seed_replay=PASS shifted_clock_replay=PASS", flush=True)
            print(f"total_nodes={total_nodes}", flush=True)
            return
        if time.monotonic() >= deadline:
            break
    args.out.write_text(json.dumps({"search": results, "total_nodes": total_nodes}, indent=2) + "\n")
    print(f"total_nodes={total_nodes} result={args.out}", flush=True)


if __name__ == "__main__":
    main()
