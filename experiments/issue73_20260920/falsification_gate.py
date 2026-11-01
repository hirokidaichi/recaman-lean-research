#!/usr/bin/env python3
"""Enforcing p=1..11 regression gate for the H-20260917-01 Q/W probe.

This executes the frozen baseline computation.  Passing is finite OBSERVED evidence only.
"""

import argparse
import ast
import hashlib
import importlib.util
import subprocess
import sys
from pathlib import Path


HERE = Path(__file__).resolve().parent
BASELINE = HERE / "baseline_q_w.py"
BASELINE_SHA256 = "50b0e26f6a878e0c7ae229303026469a4f13c4fc0a21ee5b1ac591164145aea7"
PROTOCOL = (
    "PROTOCOL periods=1..11 words=all positive-sign-sum bit words "
    "lag_range=1..p(p+1)_inclusive full_U=yes Hall=all_subsets "
    "B=all_subsets holdout=no"
)
EXPECTED_TOTAL = {
    "words": 1872,
    "hall_words": 1872,
    "q_donors": 52,
    "q_tight": 104,
    "q_nonempty": 52,
    "q_violations": 0,
    "w_tight": 2202,
    "w_occurrences": 32,
    "w_violations": 0,
}
FAULTS = (
    "drop-ss2",
    "drop-tightness",
    "empty-target",
    "wrong-oldest-offset",
    "inject-violation",
    "incomplete-output",
)


class GateFailure(RuntimeError):
    pass


def require(condition, message):
    if not condition:
        raise GateFailure(message)


def load_baseline():
    digest = hashlib.sha256(BASELINE.read_bytes()).hexdigest()
    require(digest == BASELINE_SHA256, f"baseline hash mismatch: {digest}")
    spec = importlib.util.spec_from_file_location("issue73_baseline_q_w", BASELINE)
    require(spec is not None and spec.loader is not None, "cannot load baseline")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def run_baseline(timeout=30):
    try:
        proc = subprocess.run(
            [sys.executable, "-u", str(BASELINE), "11"],
            cwd=HERE.parents[1],
            text=True,
            capture_output=True,
            timeout=timeout,
            check=False,
        )
    except subprocess.TimeoutExpired as exc:
        raise GateFailure(f"baseline timed out after {timeout}s") from exc
    require(proc.returncode == 0, f"baseline exited {proc.returncode}")
    require(not proc.stderr, f"baseline wrote stderr: {proc.stderr.strip()}")
    return proc.stdout


def literal_line(lines, prefix):
    matches = [line[len(prefix):] for line in lines if line.startswith(prefix)]
    require(len(matches) == 1, f"expected one {prefix.strip()} line, got {len(matches)}")
    try:
        return ast.literal_eval(matches[0])
    except (SyntaxError, ValueError) as exc:
        raise GateFailure(f"invalid literal after {prefix.strip()}") from exc


def parse_output(output, fault=None):
    lines = output.splitlines()
    if fault == "incomplete-output":
        lines = [line for line in lines if not line.startswith("PERIOD 11 ")]
    require(lines and lines[0] == PROTOCOL, "protocol marker mismatch or missing")
    period_rows = {}
    for line in lines:
        if not line.startswith("PERIOD "):
            continue
        parts = line.split(" ", 2)
        require(len(parts) == 3, "malformed PERIOD line")
        period_rows[int(parts[1])] = ast.literal_eval(parts[2])
    require(sorted(period_rows) == list(range(1, 12)), "period completion is not exactly 1..11")
    total = literal_line(lines, "TOTAL ")
    require(isinstance(total, dict), "TOTAL is not a dictionary")
    if fault == "empty-target":
        total = dict(total, q_donors=0, q_tight=0, q_nonempty=0, w_occurrences=0)
    if fault == "inject-violation":
        total = dict(total, q_violations=1)
    require(total == EXPECTED_TOTAL, f"TOTAL mismatch: {total}")
    summed = {key: sum(row[key] for row in period_rows.values()) for key in EXPECTED_TOTAL}
    require(summed == total, f"PERIOD rows do not sum to TOTAL: {summed}")
    require(total["q_donors"] > 0 and total["q_nonempty"] > 0, "Q target is empty")
    require(total["w_tight"] > 0 and total["w_occurrences"] > 0, "W target is empty")
    require(any(line.startswith("FIRST_Q_NONEMPTY ") for line in lines), "missing first Q witness")
    require(any(line.startswith("FIRST_W_APPLICABLE ") for line in lines), "missing first W witness")
    return total


def validate_controls(base, fault=None):
    # Q nonempty wrapping control: selected B and N are checked, not merely aggregate text.
    q_word = "SSAASAAA"
    q_u = base.full_u(q_word)
    require(base.hall(q_u), "p8 Q control lost Hall")
    require(sorted(q_u) == [3, 7], "p8 Q control U mismatch")
    require(q_u[3][0] == 11 and base.ss_count(q_u[3][1]) == 2, "p8 donor mismatch")
    require(base.neighborhood(q_u, [7]) == {4}, "p8 selected B neighborhood mismatch")
    require(q_u[3][3] == 0 and q_u[3][3] not in {4}, "p8 true-oldest control failed")

    # W nonempty control includes the selected B, neighborhood, member, and next sign.
    w_word = "SSAAAASAAA"
    w_u = base.full_u(w_word)
    w_b = [4, 7, 9]
    require(base.hall(w_u) and sorted(w_u) == w_b, "p10 W control U/Hall mismatch")
    require(base.neighborhood(w_u, w_b) == {0, 1, 6}, "p10 selected B neighborhood mismatch")
    require(w_u[7][0] == 7 and w_u[7][1] == base.W1, "p10 w1 member mismatch")
    require(w_word[(7 + 1) % len(w_word)] == "A", "p10 next sign is not A")

    # Wrong oldest-offset implementation must be caught on the full-U p15 control.
    o_word = "AAAASAAASASASSS"
    o_u = base.full_u(o_word)
    lag, _window, _cover, true_phase, true_offset = o_u[3]
    chosen_offset = 11 if fault == "wrong-oldest-offset" else true_offset
    chosen_phase = (3 - chosen_offset) % len(o_word)
    require(base.hall(o_u) and lag == 11, "p15 offset control setup mismatch")
    require(true_offset == 10 and true_phase == 8, "p15 true oldest mismatch")
    require(chosen_offset == true_offset and chosen_phase == true_phase,
            "fixed offset 11 does not select the true oldest S")
    require(o_word[(3 - 11) % len(o_word)] == "A", "p15 false-offset bit ceased to be A")

    # Dropping SS=2 makes this real full-U, Hall-valid p12 case violate weakened Q.
    nq_word = "AAAASAAASSSS"
    nq_u = base.full_u(nq_word)
    nq_b = [2, 5, 7]
    nq_d, nq_window, _cover, nq_oldest, _off = nq_u[3]
    nq_n = base.neighborhood(nq_u, nq_b)
    require(base.hall(nq_u) and nq_n == {4, 10, 11} and len(nq_n) == len(nq_b),
            "p12 weakened-Q control setup mismatch")
    require(nq_d == 11 and base.ss_count(nq_window) == 3 and nq_oldest == 4,
            "p12 weakened-Q donor mismatch")
    q_applicable = nq_d == 11 and (fault == "drop-ss2" or base.ss_count(nq_window) == 2)
    require(not (q_applicable and nq_oldest in nq_n), "SS=2-dropped Q admits known counterexample")

    # Dropping tightness makes this real full-U, Hall-valid p8 case violate weakened W.
    nw_word = "SSAAAASA"
    nw_u = base.full_u(nw_word)
    nw_b = [7]
    nw_n = base.neighborhood(nw_u, nw_b)
    require(base.hall(nw_u) and sorted(nw_u) == [4, 7], "p8 weakened-W U/Hall mismatch")
    require(nw_u[7][0] == 7 and nw_u[7][1] == base.W1, "p8 weakened-W member mismatch")
    require(nw_n == {0, 1, 6} and nw_word[0] == "S", "p8 weakened-W details mismatch")
    w_applicable = fault == "drop-tightness" or len(nw_n) == len(nw_b)
    require(not (w_applicable and nw_word[(7 + 1) % len(nw_word)] != "A"),
            "tightness-dropped W admits known counterexample")


def evaluate(output, fault=None):
    base = load_baseline()
    parse_output(output, fault)
    validate_controls(base, fault)


def main(argv=None):
    parser = argparse.ArgumentParser()
    parser.add_argument("--timeout", type=int, default=30)
    parser.add_argument("--emit-baseline", action="store_true")
    parser.add_argument("--simulate-fault", choices=FAULTS)
    args = parser.parse_args(argv)
    try:
        output = run_baseline(args.timeout)
        if args.emit_baseline:
            print(output, end="")
        evaluate(output, args.simulate_fault)
    except GateFailure as exc:
        print(f"REJECT: {exc}", file=sys.stderr)
        return 2
    print("ACCEPT: fixed p=1..11 Q/W regression and all falsification controls passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
