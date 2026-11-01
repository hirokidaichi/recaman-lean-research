#!/usr/bin/env python3
"""Check brief freshness using disposable, changing source documents."""
import csv
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
HEADER = ["id", "label", "branch", "claim", "artifact", "audit_symbols", "reopen_gate"]


class ResearchBriefTests(unittest.TestCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory(prefix="recaman-brief-test-")
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)
        for name in ["scripts", "docs", "Recaman"]:
            (self.root / name).mkdir()
        self.script = self.root / "scripts/dev_tool.py"
        shutil.copyfile(ROOT / "scripts/dev_tool.py", self.script)
        self.frontier = self.root / "docs/CURRENT_FRONTIER.md"
        self.frontier.write_text(
            "# Frontier\n最終更新: 2026-10-21\n\n## Research brief\n"
            "- Candidate A is computed for length <= 8 (E-101).\n\n"
            "## History\nObsolete claim, must not enter the brief.\n", encoding="utf-8")
        self.registry = self.root / "docs/EVIDENCE_REGISTRY.tsv"
        self.write_registry("COMPUTED")
        (self.root / "docs/PROTECTED_CLAIMS.tsv").write_text("id\tlabel\nE-001\tCONJECTURED\n")
        (self.root / "docs/MODULE_IMPORT_CONTRACTS.tsv").write_text(
            "module\tdirect_imports\tpurpose\nRecaman.Foo\t-\tfixture\n")
        (self.root / "Recaman/Audit.lean").write_text("#print axioms Recaman.Foo\n")
        (self.root / "Recaman/Foo.lean").write_text("-- count fixture\n")

    def write_registry(self, label):
        with self.registry.open("w", encoding="utf-8", newline="") as output:
            writer = csv.writer(output, delimiter="\t", lineterminator="\n")
            writer.writerow(HEADER)
            for eid, status in [("E-001", "CONJECTURED"), ("E-101", label)]:
                writer.writerow([eid, status, "fixture", "claim", "fixture.md", "-", "gate"])

    def brief(self):
        # Run outside the fixture root to exercise script-relative resolution.
        return subprocess.run([sys.executable, str(self.script), "brief"], cwd=ROOT,
                              capture_output=True, text=True)

    def test_frontier_and_registry_updates_are_read_each_time(self):
        before = self.brief()
        self.assertEqual(before.returncode, 0, before.stderr)
        self.assertIn("length <= 8", before.stdout)
        self.assertIn("E-101 [COMPUTED]", before.stdout)
        self.assertNotIn("Obsolete claim", before.stdout)
        self.frontier.write_text(self.frontier.read_text().replace(
            "Candidate A is computed for length <= 8", "Candidate A was refuted at length 9"))
        self.write_registry("REFUTED")
        after = self.brief()
        self.assertEqual(after.returncode, 0, after.stderr)
        self.assertIn("refuted at length 9", after.stdout)
        self.assertIn("E-101 [REFUTED]", after.stdout)
        self.assertNotIn("length <= 8", after.stdout)
        self.assertNotIn("E-101 [COMPUTED]", after.stdout)

    def test_counts_are_dynamic_and_not_claimed_as_verified(self):
        before = self.brief()
        self.assertEqual(before.returncode, 0, before.stderr)
        self.assertIn("Lean source files: 2", before.stdout)
        self.assertIn("audit declarations: 1", before.stdout)
        (self.root / "Recaman/Bar.lean").write_text("-- another fixture\n")
        with (self.root / "Recaman/Audit.lean").open("a") as output:
            output.write("#print axioms Recaman.Bar\n")
        after = self.brief()
        self.assertIn("Lean source files: 3", after.stdout)
        self.assertIn("audit declarations: 2", after.stdout)
        self.assertIn("SOURCE COUNTS — run make check to verify", after.stdout)
        self.assertNotIn("declarations verified", after.stdout)

    def test_missing_empty_or_duplicate_section_fails_without_stale_fallback(self):
        for body in ["# No current section\n", "## Research brief\n\n## History\nold\n",
                     "## Research brief\nE-101\n## Research brief\nE-101\n"]:
            with self.subTest(body=body):
                self.frontier.write_text(body)
                result = self.brief()
                self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
                self.assertIn("needs one nonempty", result.stderr)
                self.assertEqual(result.stdout, "")

    def test_unknown_evidence_id_fails(self):
        self.frontier.write_text(self.frontier.read_text().replace("E-101", "E-999"))
        result = self.brief()
        self.assertEqual(result.returncode, 1, result.stderr)
        self.assertIn("unknown brief/protected evidence IDs: E-999", result.stderr)

    def test_evidence_ids_next_to_japanese_are_included(self):
        self.frontier.write_text("## Research brief\n参照E-101で部分場合を確認。\n")
        result = self.brief()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("E-101 [COMPUTED]", result.stdout)
        self.frontier.write_text("## Research brief\n参照E-999で未登録。\n")
        result = self.brief()
        self.assertEqual(result.returncode, 1, result.stdout)
        self.assertIn("unknown brief/protected evidence IDs: E-999", result.stderr)

    def test_ascii_id_continuations_are_not_partial_evidence_ids(self):
        self.frontier.write_text("## Research brief\nAE-999 E-9990 E-999suffix E-999_x\n")
        result = self.brief()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertNotIn("E-999 [", result.stdout)

    def test_duplicate_registry_id_fails(self):
        with self.registry.open("a") as output:
            output.write("E-101\tCOMPUTED\tfixture\tclaim\tfixture.md\t-\tgate\n")
        result = self.brief()
        self.assertEqual(result.returncode, 1, result.stderr)
        self.assertIn("duplicate evidence IDs", result.stderr)


if __name__ == "__main__":
    unittest.main(verbosity=2)
