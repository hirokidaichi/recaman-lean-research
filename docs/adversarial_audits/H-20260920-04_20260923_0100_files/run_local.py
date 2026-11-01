#!/usr/bin/env python3
"""Record exact local audit commands, raw streams, exits, and timeouts."""

import hashlib
import json
from pathlib import Path
import subprocess
import time

root = Path("/Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research")
out = Path("/tmp/recaman-audit-20260923-0100-sol")
commands = [
    ("independent_literal_check", 30, ["python3", "-u", str(out / "independent_literal_check.py")]),
    ("known_controls", 30, ["python3", "-u", str(out / "known_controls.py")]),
    ("axiom_check", 60, ["lake", "env", "lean", str(out / "axiom_check.lean")]),
]
records = []
for name, timeout, argv in commands:
    start = time.time()
    try:
        process = subprocess.run(argv, cwd=root, capture_output=True, timeout=timeout)
        stdout, stderr, code, timed_out = process.stdout, process.stderr, process.returncode, False
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
(out / "local_commands.json").write_text(json.dumps(records, ensure_ascii=False, indent=2) + "\n")
