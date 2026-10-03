#!/usr/bin/env python3
"""Independent recomputation and parser attacks for the slot-0130 gate."""

import ast
import hashlib
import importlib.util
import itertools
import json
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path
from unittest.mock import patch

REPO = Path("/Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research")
GATE = REPO / "experiments/issue73_20260920/falsification_gate.py"
EXPECTED = {
    "words": 1872, "hall_words": 1872, "q_donors": 52,
    "q_tight": 104, "q_nonempty": 52, "q_violations": 0,
    "w_tight": 2202, "w_occurrences": 32, "w_violations": 0,
}
W1 = "SAAAASS"


def hist(word, end, length):
    return tuple(1 if word[(end - j) % len(word)] == "A" else -1
                 for j in range(1, length + 1))


def is_p2(values):
    return sum(values) == 1 and sum((j + 1) * v for j, v in enumerate(values)) == 0


def supply(word, end):
    p = len(word)
    for length in range(1, p * (p + 1) + 1):
        values = hist(word, end, length)
        if is_p2(values):
            s_offsets = tuple(j + 1 for j, v in enumerate(values) if v == -1)
            s_phases = frozenset((end - j) % p for j in s_offsets)
            letters = "".join("A" if v == 1 else "S" for v in values)
            return length, letters, s_phases, max(s_offsets), (end - max(s_offsets)) % p
    return None


def all_supplies(word):
    return {u: rec for u, c in enumerate(word) if c == "A" and (rec := supply(word, u))}


def subsets(values):
    values = tuple(values)
    for size in range(len(values) + 1):
        yield from itertools.combinations(values, size)


def neighbors(universe, members):
    result = set()
    for member in members:
        result.update(universe[member][2])
    return result


def has_hall(universe):
    return all(len(members) <= len(neighbors(universe, members))
               for members in subsets(universe))


def ss_count(word):
    return sum(a == b == "S" for a, b in zip(word, word[1:]))


def analyze(word):
    universe = all_supplies(word)
    if not has_hall(universe):
        return None
    row = {key: 0 for key in EXPECTED if key not in ("words", "hall_words")}
    phases = tuple(universe)
    for donor in phases:
        lag, window, _, _, oldest = universe[donor]
        if lag != 11 or ss_count(window) != 2:
            continue
        row["q_donors"] += 1
        for members in subsets(u for u in phases if u != donor):
            if any(universe[u][0] not in (3, 7, 11) for u in members):
                continue
            nbh = neighbors(universe, members)
            if len(nbh) != len(members):
                continue
            row["q_tight"] += 1
            row["q_nonempty"] += bool(members)
            row["q_violations"] += oldest in nbh
    for members in subsets(phases):
        if not members or any(universe[u][0] not in (3, 7) for u in members):
            continue
        if len(neighbors(universe, members)) != len(members):
            continue
        row["w_tight"] += 1
        for u in members:
            if universe[u][0] == 7 and universe[u][1] == W1:
                row["w_occurrences"] += 1
                row["w_violations"] += word[(u + 1) % len(word)] != "A"
    return row


def independent_recompute():
    totals = {key: 0 for key in EXPECTED}
    for p in range(1, 12):
        for bits in itertools.product("SA", repeat=p):
            word = "".join(bits)
            if 2 * word.count("A") <= p:
                continue
            totals["words"] += 1
            row = analyze(word)
            if row is None:
                continue
            totals["hall_words"] += 1
            for key, value in row.items():
                totals[key] += value
    assert totals == EXPECTED, totals

    e240 = all_supplies("AAAASSAAAASAAASASS")
    assert [(u, e240[u][0]) for u in e240] == [(2, 3), (7, 11), (8, 3), (11, 7), (13, 3)]
    assert has_hall(e240) and neighbors(e240, (2, 8, 11, 13)) == {4, 5, 10, 17}
    assert e240[7][4] == 14 and e240[7][3] == 11

    q8 = all_supplies("SSAASAAA")
    assert [(u, q8[u][0]) for u in q8] == [(3, 11), (7, 3)]
    assert has_hall(q8) and neighbors(q8, (7,)) == {4} and q8[3][4] == 0

    w10 = all_supplies("SSAAAASAAA")
    assert [(u, w10[u][0]) for u in w10] == [(4, 3), (7, 7), (9, 3)]
    assert has_hall(w10) and neighbors(w10, (4, 7, 9)) == {0, 1, 6}
    assert w10[7][1] == W1 and "SSAAAASAAA"[8] == "A"

    off15 = all_supplies("AAAASAAASASASSS")
    assert has_hall(off15) and off15[3][0] == 11 and off15[3][3:] == (10, 8)
    assert "AAAASAAASASASSS"[(3 - 11) % 15] == "A"

    nq = all_supplies("AAAASAAASSSS")
    assert has_hall(nq) and nq[3][0] == 11 and ss_count(nq[3][1]) == 3
    assert nq[3][4] == 4 and neighbors(nq, (2, 5, 7)) == {4, 10, 11}

    nw = all_supplies("SSAAAASA")
    assert has_hall(nw) and [(u, nw[u][0]) for u in nw] == [(4, 3), (7, 7)]
    assert neighbors(nw, (7,)) == {0, 1, 6} and nw[7][1] == W1 and "SSAAAASA"[0] == "S"
    details = {
        "E240": {"sign_sum": 2 * "AAAASSAAAASAAASASS".count("A") - 18,
                 "U": [(u, r[0], r[1], sorted(r[2]), r[3], r[4]) for u, r in e240.items()],
                 "hall": has_hall(e240), "B": [2, 8, 11, 13],
                 "N": sorted(neighbors(e240, (2, 8, 11, 13))),
                 "donor_ss": ss_count(e240[7][1])},
        "Q_P8": {"U": [(u, r[0], r[1], sorted(r[2]), r[3], r[4]) for u, r in q8.items()],
                  "hall": has_hall(q8), "B": [7], "N": sorted(neighbors(q8, (7,)))},
        "W_P10": {"U": [(u, r[0], r[1], sorted(r[2]), r[3], r[4]) for u, r in w10.items()],
                   "hall": has_hall(w10), "B": [4, 7, 9],
                   "N": sorted(neighbors(w10, (4, 7, 9))), "next": "SSAAAASAAA"[8]},
        "OFFSET_P15": {"donor": [off15[3][0], off15[3][1], off15[3][3], off15[3][4]],
                        "offset11_phase": (3 - 11) % 15,
                        "offset11_bit": "AAAASAAASASASSS"[(3 - 11) % 15]},
        "WEAK_Q_P12": {"donor": [nq[3][0], nq[3][1], ss_count(nq[3][1]), nq[3][4]],
                        "B": [2, 5, 7], "N": sorted(neighbors(nq, (2, 5, 7)))},
        "WEAK_W_P8": {"U": [(u, r[0], r[1]) for u, r in nw.items()],
                       "B": [7], "N": sorted(neighbors(nw, (7,))), "next": "SSAAAASA"[0]},
    }
    print("CONTROL_DETAILS", json.dumps(details, sort_keys=True))
    return totals


def load_gate():
    spec = importlib.util.spec_from_file_location("audited_gate", GATE)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def replace_period_field(output, period, key, value):
    result = []
    for line in output.splitlines():
        if line.startswith(f"PERIOD {period} "):
            row = ast.literal_eval(line.split(" ", 2)[2])
            row[key] = value
            line = f"PERIOD {period} {row!r}"
        result.append(line)
    return "\n".join(result) + "\n"


def gate_attacks():
    gate = load_gate()
    real = gate.run_baseline(timeout=30)
    gate.evaluate(real)
    results = {}

    def accepted(name, payload, fault=None):
        try:
            gate.evaluate(payload, fault)
        except Exception as exc:
            results[name] = {"accepted": False, "exception": type(exc).__name__, "message": str(exc)}
        else:
            results[name] = {"accepted": True}

    accepted("missing_total", "\n".join(x for x in real.splitlines() if not x.startswith("TOTAL ")))
    accepted("missing_period_11", "\n".join(x for x in real.splitlines() if not x.startswith("PERIOD 11 ")))
    p1 = next(x for x in real.splitlines() if x.startswith("PERIOD 1 "))
    accepted("duplicate_period_1", real + p1 + "\n")
    with patch.object(gate, "run_baseline", return_value=real + p1 + "\n"):
        results["duplicate_period_1_main_returncode"] = gate.main([])

    p1row = ast.literal_eval(p1.split(" ", 2)[2])
    p2 = next(x for x in real.splitlines() if x.startswith("PERIOD 2 "))
    p2row = ast.literal_eval(p2.split(" ", 2)[2])
    neg = replace_period_field(real, 1, "words", -1)
    neg = replace_period_field(neg, 2, "words", p2row["words"] + p1row["words"] + 1)
    accepted("negative_count_cancellation", neg)
    with patch.object(gate, "run_baseline", return_value=neg):
        results["negative_count_cancellation_main_returncode"] = gate.main([])

    bad_witness = "\n".join(
        "FIRST_Q_NONEMPTY garbage" if x.startswith("FIRST_Q_NONEMPTY ") else x
        for x in real.splitlines()) + "\n"
    accepted("malformed_first_q_witness", bad_witness)
    for fault in gate.FAULTS:
        accepted("simulate_" + fault, real, fault)

    timeout = subprocess.run([sys.executable, str(GATE), "--timeout", "0"], text=True,
                             capture_output=True, cwd=REPO)
    results["timeout_cli"] = {"returncode": timeout.returncode,
                              "stdout": timeout.stdout.strip(), "stderr": timeout.stderr.strip()}
    with tempfile.TemporaryDirectory(dir=Path(__file__).parent) as temp_name:
        temp = Path(temp_name)
        shutil.copy2(GATE, temp / GATE.name)
        (temp / "baseline_q_w.py").write_text("raise SystemExit(9)\n", encoding="utf-8")
        failed = subprocess.run([sys.executable, str(temp / GATE.name)], text=True,
                                capture_output=True, cwd=REPO)
        results["actual_child_nonzero"] = {"returncode": failed.returncode,
                                            "stdout": failed.stdout.strip(),
                                            "stderr": failed.stderr.strip()}
        fake = "print(" + repr(real) + ", end='')\n"
        (temp / "baseline_q_w.py").write_text(fake, encoding="utf-8")
        forged = subprocess.run([sys.executable, str(temp / GATE.name)], text=True,
                                capture_output=True, cwd=REPO)
        results["forged_expected_output_wrong_source"] = {"returncode": forged.returncode,
                                                            "stdout": forged.stdout.strip(),
                                                            "stderr": forged.stderr.strip()}
    return results


def main():
    print("GATE_SHA256", hashlib.sha256(GATE.read_bytes()).hexdigest())
    print("INDEPENDENT_TOTAL", independent_recompute())
    print("ATTACK_RESULTS", json.dumps(gate_attacks(), sort_keys=True, ensure_ascii=True))


if __name__ == "__main__":
    main()
