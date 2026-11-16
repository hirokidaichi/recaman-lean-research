#!/usr/bin/env python3
"""Check that cited theorems prove human-pinned statements (Comparator-style trial).

For each row of cases.tsv, generate a tiny Lean file that imports Pins.lean's
dependencies and tries, in two modes, to prove the pinned Prop from the theorem:

  exact   : example : PIN := @THM                       (type must be defeq)
  implies : example : PIN := by unfold PIN; intros; apply @THM <;> assumption

and audits axioms of the successful check (only propext / Classical.choice /
Quot.sound allowed, matching scripts/check.sh).  Exit 1 if any result differs
from the expectation column.  Run from anywhere:

    python3 experiments/autoresearch_trial_20261116/statement_pin/check_pins.py
"""
from __future__ import annotations

import csv
import re
import subprocess
import sys
import tempfile
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def lean_check(body: str) -> tuple[bool, str]:
    pins = (HERE / "Pins.lean").read_text()
    src = pins + "\n\nopen RecamanPins in\n" + body + "\n"
    with tempfile.NamedTemporaryFile("w", suffix=".lean", dir=HERE, delete=False) as f:
        f.write(src)
        path = Path(f.name)
    try:
        r = subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT,
                           capture_output=True, text=True, timeout=600)
    finally:
        path.unlink(missing_ok=True)
    out = (r.stdout + r.stderr).strip()
    return r.returncode == 0 and "error" not in out.lower(), out


def axioms_ok(out: str) -> bool:
    m = re.search(r"depends on axioms: \[([^\]]*)\]", out)
    if m is None:
        return "does not depend on any axioms" in out
    used = {a.strip() for a in m.group(1).split(",") if a.strip()}
    return used <= ALLOWED


def run_case(pin: str, thm: str, mode: str) -> tuple[str, str]:
    if mode == "exact":
        body = f"theorem pin_check : {pin} := @{thm}\n#print axioms pin_check"
    else:
        body = (f"theorem pin_check : {pin} := by\n  unfold {pin}\n  intros\n  apply @{thm} <;> assumption\n"
                f"#print axioms pin_check")
    ok, out = lean_check(body)
    if ok and not axioms_ok(out):
        return "fail", "unexpected axiom: " + out
    err = next((l for l in out.splitlines() if "error" in l.lower()), "")
    err = err.split("error:", 1)[-1].strip()
    if "unsolved goals" in out or "assumption" in out:
        # report the first goal that no hypothesis closes (the missing assumption)
        goals = [l.strip() for l in out.splitlines() if l.strip().startswith("⊢")]
        if goals:
            err += " | open goal " + goals[0]
    return ("pass" if ok else "fail"), err[:220]


def main() -> int:
    rows = list(csv.DictReader(open(HERE / "cases.tsv"), delimiter="\t"))
    bad = 0
    for row in rows:
        for mode in ("exact", "implies"):
            t0 = time.time()
            got, note = run_case(row["pin"], row["theorem"], mode)
            exp = row[f"expected_{mode}"]
            flag = "ok " if got == exp else "MISMATCH"
            bad += got != exp
            print(f"{flag} {row['case']:<16} {mode:<8} got={got:<4} expected={exp:<4} "
                  f"{time.time() - t0:5.1f}s  {note if got == 'fail' else ''}")
    print(f"{len(rows) * 2 - bad}/{len(rows) * 2} checks matched expectations")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
