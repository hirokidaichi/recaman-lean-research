#!/usr/bin/env python3
"""Capture independent Lean/harness runs without writing into the repository."""

import hashlib
import json
from pathlib import Path
import subprocess
import time

root = Path("/Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research")
out = Path("/tmp/recaman-audit-20260923-0100-sol")
checks = [
    ("vacuity", 45, ["python3", "scripts/report_vacuity.py", "--all", "Recaman/ShortTightDonorAvoidance.lean"]),
    ("lint", 45, ["python3", "scripts/harness_gate.py", "--lint-module", "Recaman/ShortTightDonorAvoidance.lean"]),
    ("statement_audit_registry", 45, ["python3", "scripts/harness_gate.py", "--check-registry"]),
    ("full_check", 480, ["./scripts/check.sh"]),
]
records = []
for name, timeout, argv in checks:
    start = time.time()
    try:
        run = subprocess.run(argv, cwd=root, capture_output=True, timeout=timeout)
        stdout, stderr, code, timed_out = run.stdout, run.stderr, run.returncode, False
    except subprocess.TimeoutExpired as ex:
        stdout, stderr, code, timed_out = ex.stdout or b"", ex.stderr or b"", None, True
    (out / (name + ".stdout")).write_bytes(stdout)
    (out / (name + ".stderr")).write_bytes(stderr)
    record = {
        "name": name, "argv": argv, "cwd": str(root), "timeout_seconds": timeout,
        "started_unix": start, "elapsed_seconds": time.time()-start,
        "exit_code": code, "timed_out": timed_out,
        "stdout_sha256": hashlib.sha256(stdout).hexdigest(),
        "stderr_sha256": hashlib.sha256(stderr).hexdigest(),
    }
    records.append(record)
    print(json.dumps(record, sort_keys=True), flush=True)
(out / "gate_commands.json").write_text(json.dumps(records, ensure_ascii=False, indent=2) + "\n")
