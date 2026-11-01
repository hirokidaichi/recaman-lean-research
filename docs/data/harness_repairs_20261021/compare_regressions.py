#!/usr/bin/env python3
"""Verify the three new regressions fail on the audited baseline and pass now."""
import importlib.util
import io
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[3]
BASE = "5606b64d27290a9959e1dbf19d5e7c58840a0a85"
NAMES = [
    "test_regression_g5_unfilled_template",
    "test_regression_g5_signature_only",
    "test_regression_g2_conjunct_hidden_by_substantive_companion",
]


def run_tests(module, gate):
    module.GATE = gate
    suite = unittest.TestSuite(module.HarnessGateTests(name) for name in NAMES)
    return unittest.TextTestRunner(stream=io.StringIO()).run(suite)


spec = importlib.util.spec_from_file_location("harness_tests", ROOT / "scripts/test_harness_gates.py")
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)
with tempfile.TemporaryDirectory(prefix="recaman-baseline-gate-") as directory:
    old = Path(directory)
    for name in ["harness_gate.py", "report_vacuity.py"]:
        content = subprocess.run(
            ["git", "show", f"{BASE}:scripts/{name}"], cwd=ROOT,
            capture_output=True, text=True, check=True,
        ).stdout
        (old / name).write_text(content, encoding="utf-8")
    baseline = run_tests(module, old / "harness_gate.py")
    assert len(baseline.failures) == 3 and not baseline.errors, baseline
    print(f"baseline {BASE}: 3/3 regression assertions fail (old gate accepts all three)")
current = run_tests(module, ROOT / "scripts/harness_gate.py")
assert current.wasSuccessful(), current
print("current working tree: 3/3 regression assertions pass (G5, G5, G2 reject)")
