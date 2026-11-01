#!/usr/bin/env python3
"""Positive and adversarial CLI tests for the research harness (stdlib only)."""
import csv
import os
from pathlib import Path
import re
import shutil
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


class RegistryWrapperTests(unittest.TestCase):
    """Exercise the TSV/link preflight independently of theorem classification."""

    def setUp(self):
        directory = tempfile.TemporaryDirectory(prefix="recaman-registry-test-")
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)
        for folder in ["scripts", "docs", "Recaman", "bin"]:
            (self.root / folder).mkdir()
        self.wrapper = self.root / "scripts/check_research_registry.sh"
        shutil.copyfile(ROOT / "scripts/check_research_registry.sh", self.wrapper)
        (self.root / "scripts/harness_gate.py").write_text(
            "import os, sys\n"
            "print('delegated ' + sys.argv[1], flush=True)\n"
            "if os.environ.get('FAIL_GATE') == sys.argv[1]:\n"
            "    print('fixture gate rejected', file=sys.stderr)\n"
            "    sys.exit(1)\n", encoding="utf-8")
        self.registry = self.root / "docs/EVIDENCE_REGISTRY.tsv"
        self.frontier = self.root / "docs/CURRENT_FRONTIER.md"
        self.audit = self.root / "Recaman/Audit.lean"
        self.artifact = self.root / "Recaman/Foo.lean"
        self.row = ["E-001", "PROVED-LEAN", "fixture", "claim", "Recaman/Foo.lean",
                    "Recaman.Foo.foo", "none"]
        self.reset_fixture()

    def reset_fixture(self):
        self.registry.write_text("\t".join(HEADER) + "\n" + "\t".join(self.row) + "\n",
                                 encoding="utf-8")
        self.frontier.write_text("現状: E-001の検査\n", encoding="utf-8")
        self.audit.write_text("#print axioms Recaman.Foo.foo\n", encoding="utf-8")
        self.artifact.write_text("-- fixture artifact\n", encoding="utf-8")

    def run_wrapper(self, **env):
        return subprocess.run(["bash", str(self.wrapper)], cwd=self.root,
                              env={**os.environ, **env}, capture_output=True, text=True)

    def assert_rejected(self, detail):
        result = self.run_wrapper()
        self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn(detail, result.stderr)
        self.assertNotIn("delegated", result.stdout)

    def test_valid_fixture_delegates_both_existing_gates(self):
        result = self.run_wrapper()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("1 entries, 1 PROVED-LEAN", result.stdout)
        self.assertIn("delegated --check-registry", result.stdout)
        self.assertIn("delegated --check-protected", result.stdout)

    def test_link_checks_do_not_launch_rg(self):
        marker = self.root / "rg-called"
        rg = self.root / "bin/rg"
        rg.write_text('#!/bin/sh\nprintf called >> "$RG_MARKER"\nexit 99\n', encoding="utf-8")
        rg.chmod(0o755)
        result = self.run_wrapper(PATH=str(rg.parent) + os.pathsep + os.environ["PATH"],
                                  RG_MARKER=str(marker))
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertFalse(marker.exists(), "link checks should use the in-process text snapshots")

    def test_required_files_and_artifact_are_checked(self):
        for file in [self.registry, self.frontier, self.audit, self.artifact]:
            with self.subTest(file=file.name):
                self.reset_fixture()
                file.unlink()
                self.assert_rejected("missing")

    def test_header_and_row_shape_are_checked(self):
        valid = self.registry.read_text(encoding="utf-8")
        for text, detail in [(valid.replace("id\tlabel", "label\tid", 1), "unexpected evidence registry header"),
                             (valid.replace("\tfixture\tclaim\t", "\tfixture\t\t"), "empty field"),
                             (valid.replace("\tnone\n", "\n"), "has 6 fields"),
                             (valid.replace("\tnone\n", "\tnone\textra\n"), "has 8 fields")]:
            with self.subTest(detail=detail):
                self.registry.write_text(text, encoding="utf-8")
                self.assert_rejected(detail)

    def test_duplicate_id_is_rejected(self):
        with self.registry.open("a", encoding="utf-8") as output:
            output.write("\t".join(self.row) + "\n")
        self.assert_rejected("duplicate evidence ids")

    def test_id_label_and_symbol_fields_are_checked(self):
        for field, value, detail in [(0, "E-01", "invalid evidence id"),
                                     (1, "PROVED", "invalid evidence label"),
                                     (5, "-", "has no audit symbol"),
                                     (5, "Recaman.Foo.foo;bad", "invalid audit symbol")]:
            with self.subTest(value=value):
                row = self.row.copy()
                row[field] = value
                self.registry.write_text("\t".join(HEADER) + "\n" + "\t".join(row) + "\n",
                                         encoding="utf-8")
                self.assert_rejected(detail)

    def test_all_frontier_and_symbol_links_are_checked(self):
        self.frontier.write_text("E-002\n", encoding="utf-8")
        self.assert_rejected("E-001 is not referenced")
        self.reset_fixture()
        self.row[5] += ";Recaman.Foo.other"
        self.reset_fixture()
        self.assert_rejected("unaudited symbol for E-001: Recaman.Foo.other")

    def test_matching_stays_literal_and_keeps_existing_substring_semantics(self):
        self.audit.write_text("#print axioms RecamanXFooXfoo\n", encoding="utf-8")
        self.assert_rejected("unaudited symbol")
        self.frontier.write_text("E-001suffix\n", encoding="utf-8")
        self.audit.write_text("#print axioms Recaman.Foo.foo_suffix\n", encoding="utf-8")
        self.assertEqual(self.run_wrapper().returncode, 0)

    def test_text_snapshots_are_reloaded_on_each_invocation(self):
        self.assertEqual(self.run_wrapper().returncode, 0)
        self.audit.write_text("-- removed audit symbol\n", encoding="utf-8")
        self.assert_rejected("unaudited symbol")
        self.reset_fixture()
        self.frontier.write_text("-- removed evidence reference\n", encoding="utf-8")
        self.assert_rejected("not referenced")

    def test_empty_proved_set_and_unterminated_last_row_keep_rejection(self):
        self.registry.write_text(self.registry.read_text().replace("PROVED-LEAN", "COMPUTED"))
        self.assert_rejected("unexpectedly empty")
        self.reset_fixture()
        self.registry.write_text(self.registry.read_text().rstrip("\n"))
        self.assert_rejected("unexpectedly empty")

    def test_nul_cannot_join_fragments_into_an_accepted_reference(self):
        for file, content in [(self.frontier, b"E-0\x0001\n"),
                              (self.audit, b"#print axio\x00ms Recaman.Foo.foo\n")]:
            with self.subTest(file=file.name):
                self.reset_fixture()
                file.write_bytes(content)
                self.assert_rejected("NUL")

    def test_gate_failures_are_not_hidden(self):
        first = self.run_wrapper(FAIL_GATE="--check-registry")
        self.assertEqual(first.returncode, 1)
        self.assertIn("fixture gate rejected", first.stderr)
        self.assertNotIn("delegated --check-protected", first.stdout)
        second = self.run_wrapper(FAIL_GATE="--check-protected")
        self.assertEqual(second.returncode, 1)
        self.assertIn("fixture gate rejected", second.stderr)


if __name__ == "__main__":
    unittest.main(verbosity=2)
