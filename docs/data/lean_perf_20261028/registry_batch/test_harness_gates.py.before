#!/usr/bin/env python3
"""Positive and adversarial CLI tests for the research harness (stdlib only)."""
import csv
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
GATE = ROOT / "scripts/harness_gate.py"
SUBSTANTIVE = "Recaman.TwelveGateT6Unconditional.tight_avoiding_le_two_all_lag_three_general"
CONJUNCT = "Recaman.anchorBoundary_exitNormal_at_landing"
CONDITIONAL = "Recaman.CapacityEqualityInduction.hcap_of_eqclassW"
HEADER = ["id", "label", "branch", "claim", "artifact", "audit_symbols", "reopen_gate"]


class HarnessGateTests(unittest.TestCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory(prefix="recaman-gate-test-")
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)
        (self.root / "Recaman").symlink_to(ROOT / "Recaman", target_is_directory=True)
        (self.root / "docs/statement_audits").mkdir(parents=True)
        self.registry = self.root / "registry.tsv"
        self.audit = self.root / "docs/statement_audits/E-993.md"
        self.registry_with(SUBSTANTIVE)

    def run_gate(self, *args, cwd=None):
        return subprocess.run(
            [sys.executable, str(GATE), *map(str, args)],
            cwd=cwd or self.root, capture_output=True, text=True,
        )

    def registry_with(self, *symbols):
        with self.registry.open("w", encoding="utf-8", newline="") as output:
            writer = csv.writer(output, delimiter="\t", lineterminator="\n")
            writer.writerow(HEADER)
            writer.writerow(["E-993", "PROVED-LEAN", "fixture", "bounded fixture claim",
                             "Recaman/TwelveGateT6Unconditional.lean", ";".join(symbols), "none"])

    def template(self):
        result = self.run_gate("--audit-template", "E-993", self.registry)
        self.assertEqual(result.returncode, 0, result.stderr)
        return result.stdout

    def completed(self):
        text = self.template().replace(
            "- reviewer: TODO (name, YYYY-MM-DD)", "- reviewer: Harness fixture, 2026-10-21")
        for number, answer in [(1, "yes"), (2, "no"), (3, "no")]:
            text = re.sub(rf"^{number}\. .+$", f"{number}. {answer}", text, flags=re.M)
        return text

    def assert_rejected(self, gate, detail=""):
        result = self.run_gate("--check-registry", self.registry)
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn(gate, result.stderr)
        self.assertIn(detail, result.stderr)
        self.assertNotIn("Traceback", result.stderr)
        return result

    def test_live_registry_and_protected_claims(self):
        for args in [["--check-registry"], ["--check-protected"]]:
            with self.subTest(args=args):
                result = self.run_gate(*args, cwd=ROOT)
                self.assertEqual(result.returncode, 0, result.stderr)

    def test_g1_unresolved_symbol(self):
        self.registry_with("Recaman.no_such_theorem_xyz")
        self.assert_rejected("G1", "no_such_theorem_xyz")

    def test_g3_arithmetic_only_module(self):
        scratch = self.root / "pure.lean"
        scratch.write_text("namespace Recaman\ntheorem gate_taut (n : Nat) : n = n := rfl\nend Recaman\n")
        result = self.run_gate("--lint-module", scratch)
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("0/1 substantive", result.stdout)

    def test_g3_wrapper_only_row(self):
        self.registry_with("Recaman.a_zero_eq_zero")
        self.assert_rejected("G3", "no substantive theorem")

    def test_g4_inflated_name(self):
        self.registry_with("Recaman.grand_permanent_high_internal_blocker_synthesis")
        self.assert_rejected("G4", "inflated name")

    def test_g5_missing_audit(self):
        self.assert_rejected("G5", "missing docs/statement_audits/E-993.md")

    # The three acceptance gaps reproduced in the 2026-10-21 audit.
    def test_regression_g5_unfilled_template(self):
        self.audit.write_text(self.template(), encoding="utf-8")
        result = self.assert_rejected("G5", "check 1 needs an explicit yes/no answer")
        self.assertIn("reviewer", result.stderr)

    def test_regression_g5_signature_only(self):
        code = self.template().split("```lean", 1)[1].split("```", 1)[0]
        self.audit.write_text("```lean" + code + "```\n", encoding="utf-8")
        self.assert_rejected("G5", "reviewer")

    def test_regression_g2_conjunct_hidden_by_substantive_companion(self):
        self.registry_with(SUBSTANTIVE, CONJUNCT)
        self.audit.write_text(self.completed(), encoding="utf-8")
        result = self.assert_rejected("G2", "conjunct-is-hypothesis")
        self.assertNotIn("G3", result.stderr)
        self.assertNotIn("G5", result.stderr)

    def test_g5_completed_audit(self):
        self.audit.write_text(self.completed(), encoding="utf-8")
        result = self.run_gate("--check-registry", self.registry)
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_g5_conditional_theorem_with_named_hypothesis(self):
        self.registry_with(CONDITIONAL)
        text = self.completed().replace("2. no", "2. yes — hE : EqClassW (conditional reduction)")
        self.audit.write_text(text, encoding="utf-8")
        result = self.run_gate("--check-registry", self.registry)
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_g5_multiline_reviewer(self):
        text = self.completed().replace("Harness fixture, 2026-10-21", "Harness fixture,\n  2026-10-21")
        self.audit.write_text(text, encoding="utf-8")
        result = self.run_gate("--check-registry", self.registry)
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_g5_altered_signature(self):
        text = self.completed().replace("lag u = 3 ∨ lag u = 7", "lag u = 3")
        self.assertNotEqual(text, self.completed())
        self.audit.write_text(text, encoding="utf-8")
        self.assert_rejected("G5", "does not quote the signature")

    def test_g5_incomplete_check_or_reviewer(self):
        complete = self.completed()
        for old, new, detail in [
            ("2. no", "", "check 2"),
            ("2. no", "2. yes/no, which", "check 2"),
            ("2. no", "2. yes", "conditional hypothesis"),
            ("3. no", "3. no\n3. yes", "check 3"),
            ("Harness fixture, 2026-10-21", "TODO, 2026-10-21", "reviewer"),
            ("Harness fixture, 2026-10-21", "Harness fixture", "reviewer"),
            ("Harness fixture, 2026-10-21", "2026-10-21", "reviewer"),
        ]:
            with self.subTest(mutation=new):
                self.audit.write_text(complete.replace(old, new), encoding="utf-8")
                self.assert_rejected("G5", detail)

    def test_g5_checks_inside_code_do_not_count(self):
        text = self.completed().replace("1. yes\n2. no\n3. no", "```text\n1. yes\n2. no\n3. no\n```")
        self.audit.write_text(text, encoding="utf-8")
        self.assert_rejected("G5", "completed check 1")

    def test_g5_signature_must_be_in_the_correct_section(self):
        text = self.completed()
        code = text.split("```lean", 1)[1].split("```", 1)[0]
        text = "```lean" + code + "```\n" + text.replace(code, "\n-- signature omitted\n")
        self.audit.write_text(text, encoding="utf-8")
        self.assert_rejected("G5", "does not quote the signature")

    def test_g5_every_theorem_needs_all_three_answers(self):
        self.registry_with(SUBSTANTIVE, CONDITIONAL)
        text = self.completed()
        before, after = text.rsplit("3. no", 1)
        self.audit.write_text(before + after, encoding="utf-8")
        self.assert_rejected("G5", CONDITIONAL + ": needs exactly one completed check 3")

    def test_p_protected_label_changed(self):
        original = (ROOT / "docs/EVIDENCE_REGISTRY.tsv").read_text(encoding="utf-8")
        self.registry.write_text(original.replace("E-070\tCONJECTURED", "E-070\tPROVED-LEAN"), encoding="utf-8")
        result = self.run_gate("--check-protected", self.registry, ROOT / "docs/PROTECTED_CLAIMS.tsv")
        self.assertEqual(result.returncode, 1, result.stderr)
        self.assertIn("E-070: protected label is CONJECTURED", result.stderr)


if __name__ == "__main__":
    unittest.main(verbosity=2)
