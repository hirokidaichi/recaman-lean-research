#!/usr/bin/env python3
"""Regression tests for the Lean-dependent harness gates (G6 pins, vacuity lint).

Needs the built library (`lake build`); run by `make test-lean-gates` / `make test`,
not by `make test-tools`. Mutating fixtures live in TemporaryDirectory.
"""
import csv
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
TOOL = ROOT / "scripts/harness_lean.py"
sys.path.insert(0, str(ROOT / "scripts"))
import harness_lean  # noqa: E402


def run(*args):
    return subprocess.run([sys.executable, str(TOOL), *map(str, args)], cwd=ROOT,
                          capture_output=True, text=True, timeout=1800)


class PinGateTests(unittest.TestCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory(prefix="recaman-lean-gate-test-")
        self.addCleanup(directory.cleanup)
        self.tmp = Path(directory.name)

    def test_live_pins_pass(self):
        result = run("--check-pins")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("definitions lock matches", result.stdout)

    def test_pin_cases_match_expectations(self):
        with open(ROOT / "scripts/lean/pin_cases.tsv", encoding="utf-8") as fh:
            rows = list(csv.DictReader(fh, delimiter="\t"))
        result = run("--check-theorem", *[x for r in rows for x in (r["pin"], r["theorem"])])
        lines = [l.split("\t") for l in result.stdout.splitlines() if l.startswith(("pass", "fail"))]
        self.assertEqual(len(lines), len(rows), result.stdout + result.stderr)
        for row, line in zip(rows, lines):
            with self.subTest(case=row["case"]):
                self.assertEqual(line[0], row["expected"], line)

    def test_definition_drift_is_rejected(self):
        lock = (ROOT / "docs/protected_pins/definitions.lock").read_text(encoding="utf-8").splitlines()
        target = next(i for i, l in enumerate(lock) if l.startswith("Recaman.ShortPeriodicSupply.signSum\t"))
        cases = {
            "changed": lock[:target] + [lock[target][:-4] + "0000"] + lock[target + 1:],
            "missing from the lock": lock[:target] + lock[target + 1:],
            "no longer used": lock + ["Recaman.Unused\tdef\t0\t0"],
        }
        for detail, lines in cases.items():
            with self.subTest(detail=detail):
                path = self.tmp / f"{detail.replace(' ', '_')}.lock"
                path.write_text("\n".join(lines) + "\n", encoding="utf-8")
                result = run("--check-pins", ROOT / "docs/EVIDENCE_REGISTRY.tsv", path)
                self.assertEqual(result.returncode, 1, result.stdout)
                self.assertIn(detail, result.stderr)

    def test_proved_label_needs_a_theorem_that_proves_the_pin(self):
        original = (ROOT / "docs/EVIDENCE_REGISTRY.tsv").read_text(encoding="utf-8").splitlines(keepends=True)
        rows = []
        for line in original:
            cols = line.rstrip("\n").split("\t")
            if cols[0] == "E-070":
                # the 2026-09-14 failure: a conditional or restricted theorem cited for the claim
                cols[1] = "PROVED-LEAN"
                cols[5] = ("Recaman.LowSSPeriodicSupply.periodic_lowSS_capacity;"
                           "Recaman.LineCapacityPeriodic.periodic_capacity_of_line")
                line = "\t".join(cols) + "\n"
            rows.append(line)
        registry = self.tmp / "registry.tsv"
        registry.write_text("".join(rows), encoding="utf-8")
        result = run("--check-pins", registry)
        self.assertEqual(result.returncode, 1, result.stdout)
        self.assertIn("E-070: G6 labelled PROVED-LEAN but no audit symbol proves RecamanProtected.E070", result.stderr)

    def test_fingerprints_see_definition_values(self):
        def deps(value):
            out = harness_lean.run_lean(
                "import HarnessTools\nnamespace RecamanProtected\n"
                f"def TestX : Nat := {value}\ndef TestPin : Prop := TestX = TestX\nend RecamanProtected\n"
                "#pin_deps RecamanProtected.TestPin\n")
            return [l for l in out.splitlines() if l.startswith("RecamanProtected.TestX\t")]
        harness_lean.compile_module(harness_lean.TOOLS)
        zero, one = deps(0), deps(1)
        self.assertEqual(len(zero), 1, zero)
        self.assertNotEqual(zero, one)


class VacuityLintTests(unittest.TestCase):
    BAD = ["bad_concl_hyp", "bad_free_nat", "bad_grand_capacity_inequality",
           "bad_unused_hyp", "bad_contradictory"]

    def test_fixtures_flagged_and_genuine_theorems_clean(self):
        result = run("--vacuity-symbols", *[f"VacuityFixtures.{b}" for b in self.BAD],
                     "Recaman.CleanWindowCapacity.clean_capacity",
                     "Recaman.LineCapacityPeriodic.periodic_capacity_of_line", "--strict")
        self.assertEqual(result.returncode, 1, result.stderr)
        self.assertIn("5 flagged, 0 unknown, 7 theorems", result.stdout)
        for b in self.BAD:
            self.assertIn(f"FLAG VacuityFixtures.{b}", result.stdout)
        self.assertNotIn("clean_capacity", result.stdout)

    def test_report_only_by_default_and_names_unused_hypotheses(self):
        result = run("--vacuity-row", "E-720")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("nearest_source_window hyps=5 unused=[hhb]", result.stdout)


if __name__ == "__main__":
    unittest.main(verbosity=2)
