#!/usr/bin/env python3
"""Read-only repository audit; gate fixtures live in a temporary directory.

Run from any directory. A zero gate exit in the three fixtures is the observed
gap, not a desired regression-test expectation. No Lean declaration is added.
"""

from __future__ import annotations

import collections
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parents[3]
GATE = ROOT / "scripts/harness_gate.py"
SUBSTANTIVE = (
    "Recaman.TwelveGateT6Unconditional."
    "tight_avoiding_le_two_all_lag_three_general"
)
CONJUNCT = "Recaman.anchorBoundary_exitNormal_at_landing"


def run(*args: str, cwd: Path = ROOT) -> subprocess.CompletedProcess[str]:
    return subprocess.run(args, cwd=cwd, capture_output=True, text=True, check=False)


def gate_fixtures() -> dict:
    results = {}
    with tempfile.TemporaryDirectory(prefix="recaman-environment-audit-") as directory:
        fixture = Path(directory)
        (fixture / "Recaman").symlink_to(ROOT / "Recaman", target_is_directory=True)
        audits = fixture / "docs/statement_audits"
        audits.mkdir(parents=True)
        registry = fixture / "registry.tsv"
        audit = audits / "E-993.md"

        def template(symbols: str) -> str:
            registry.write_text(
                "id\tlabel\tbranch\tclaim\tartifact\taudit_symbols\treopen_gate\n"
                "E-993\tPROVED-LEAN\ttest\taudit enforcement fixture\t"
                "Recaman/TwelveGateT6Unconditional.lean\t"
                f"{symbols}\tnone\n",
                encoding="utf-8",
            )
            output = run(
                sys.executable, str(GATE), "--audit-template", "E-993",
                str(registry), cwd=fixture,
            )
            if output.returncode:
                raise RuntimeError(output.stderr)
            return output.stdout

        def check(name: str, body: str) -> None:
            audit.write_text(body, encoding="utf-8")
            output = run(
                sys.executable, str(GATE), "--check-registry", str(registry),
                cwd=fixture,
            )
            results[name] = {
                "exit_code": output.returncode,
                "stdout": output.stdout.strip(),
                "stderr": output.stderr.strip(),
            }

        unfilled = template(SUBSTANTIVE)
        check("G5_unfilled_template", unfilled)
        signature = unfilled.split("```lean", 1)[1].split("```", 1)[0]
        check("G5_signature_only", "```lean" + signature + "```\n")
        mixed = template(SUBSTANTIVE + ";" + CONJUNCT)
        mixed = mixed.replace("(name, date)", "environment audit 2026-10-21")
        mixed = mixed.replace(
            ": yes/no, which", ": yes — a conclusion conjunct is a hypothesis"
        ).replace(": yes/no", ": yes")
        check("G2_conjunct_hypothesis_with_substantive_companion", mixed)
    return results


def main() -> None:
    rows = [
        line.split("\t")
        for line in (ROOT / "docs/EVIDENCE_REGISTRY.tsv").read_text().splitlines()[1:]
    ]
    brief = run(sys.executable, "scripts/dev_tool.py", "brief")
    if brief.returncode:
        raise RuntimeError(brief.stderr)
    files = [
        "scripts/harness_gate.py", "scripts/report_vacuity.py",
        "scripts/dev_tool.py", "scripts/test_harness_gates.sh",
        "scripts/check.sh", "Makefile", "experiments/Makefile",
        ".github/workflows/ci.yml", "lean-toolchain",
        "docs/CURRENT_FRONTIER.md", "docs/EVIDENCE_REGISTRY.tsv",
        "Recaman/TwelveGateT6Unconditional.lean", "Recaman/DebtBoundary.lean",
    ]
    fingerprints = {
        name: hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
        for name in files if (ROOT / name).is_file()
    }
    lean_hash = hashlib.sha256()
    for path in sorted((ROOT / "Recaman").glob("*.lean")):
        lean_hash.update(str(path.relative_to(ROOT)).encode() + b"\0")
        lean_hash.update(hashlib.sha256(path.read_bytes()).digest())
    print(json.dumps({
        "source_revision": run("git", "rev-parse", "HEAD").stdout.strip(),
        "python_version": sys.version.split()[0],
        "source_sha256": fingerprints,
        "Recaman_directory_sha256": lean_hash.hexdigest(),
        "registry_labels": dict(sorted(collections.Counter(row[1] for row in rows).items())),
        "audit_print_count": sum(
            line.startswith("#print axioms ")
            for line in (ROOT / "Recaman/Audit.lean").read_text().splitlines()
        ),
        "brief_stdout": brief.stdout,
        "isolated_gate_fixtures": gate_fixtures(),
        "interpretation": "Fixture exit 0 means the incomplete or disallowed row was accepted.",
    }, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
