#!/usr/bin/env python3
"""Capture exact stdout/stderr and exit status for the frozen module checks."""
import hashlib
import json
from pathlib import Path
import subprocess
import time


ROOT = Path(__file__).resolve().parents[4]
OUT = Path(__file__).resolve().parent
COMMANDS = [
    ("literal", 15, ["python3", "-u", str(OUT / "check_literal.py")]),
    ("statement_audit", 15, ["python3", "-u", str(OUT / "audit_signatures.py")]),
    ("vacuity", 60, ["python3", "scripts/report_vacuity.py", "--all",
                     "Recaman/ShortTightDonorAvoidance.lean"]),
    ("lint", 60, ["python3", "scripts/harness_gate.py", "--lint-module",
                  "Recaman/ShortTightDonorAvoidance.lean"]),
    ("target_build", 180, ["lake", "build", "Recaman.ShortTightDonorAvoidance"]),
    ("symbol", 60, ["lake", "env", "lean",
                    "docs/data/issue73_20260923/slot0100/symbol_check.lean"]),
    ("full_check", 300, ["./scripts/check.sh"]),
]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(name, timeout, args):
    start = time.time()
    try:
        result = subprocess.run(args, cwd=ROOT, capture_output=True, timeout=timeout)
        stdout, stderr, code, timed_out = result.stdout, result.stderr, result.returncode, False
    except subprocess.TimeoutExpired as ex:
        stdout, stderr, code, timed_out = ex.stdout or b"", ex.stderr or b"", None, True
    (OUT / (name + ".stdout")).write_bytes(stdout)
    (OUT / (name + ".stderr")).write_bytes(stderr)
    record = {"name": name, "argv": args, "cwd": str(ROOT), "timeout_seconds": timeout,
              "start_unix": start, "elapsed_seconds": time.time() - start,
              "exit_code": code, "timed_out": timed_out,
              "stdout_sha256": hashlib.sha256(stdout).hexdigest(),
              "stderr_sha256": hashlib.sha256(stderr).hexdigest()}
    print(json.dumps(record, sort_keys=True), flush=True)
    return record


if __name__ == "__main__":
    revisions = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT).decode().strip()
    sources = ["Recaman/ShortTightDonorAvoidance.lean",
               "docs/HYPOTHESIS_CARD_2026-09-20_DONOR_LENGTH_BOUNDARY.md",
               "docs/data/issue73_20260923/slot0100/check_literal.py",
               "docs/data/issue73_20260923/slot0100/audit_signatures.py",
               "docs/data/issue73_20260923/slot0100/symbol_check.lean",
               "docs/data/issue73_20260923/slot0100/run_checks.py"]
    meta = {"head": revisions, "sources_sha256": {p: sha(ROOT / p) for p in sources},
            "seed": None, "witness": "known frozen literal", "holdout": None}
    (OUT / "run_metadata.json").write_text(json.dumps(meta, indent=2, sort_keys=True) + "\n")
    records = [run(*spec) for spec in COMMANDS]
    (OUT / "commands.json").write_text(json.dumps(records, indent=2, sort_keys=True) + "\n")
