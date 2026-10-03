#!/usr/bin/env python3
import json
import subprocess
import time
from pathlib import Path

AUDIT = Path("/tmp/recaman-weekly-audit-20260924-0200-sol")
ROOT = Path("/Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research")

jobs = [
    ("inventory_check", ["python3", "source/inventory_check.py"], AUDIT, 30),
    ("repo_targets_verify", ["shasum", "-a", "256", "-c", str(AUDIT / "prehash/REPO_TARGETS.sha256")], ROOT, 30),
    ("prior_0100_manifest", ["shasum", "-a", "256", "-c", "SHA256SUMS"], ROOT / "docs/adversarial_audits/H-20260917-01_20260924_0100_files", 30),
    ("prior_0130_manifest", ["shasum", "-a", "256", "-c", "SHA256SUMS"], ROOT / "docs/adversarial_audits/H-20260920-02_20260924_0130_files", 30),
]

records = []
for name, argv, cwd, timeout in jobs:
    start = time.time()
    try:
        result = subprocess.run(argv, cwd=cwd, capture_output=True, timeout=timeout)
        exit_code = result.returncode
        stdout = result.stdout
        stderr = result.stderr
        timed_out = False
    except subprocess.TimeoutExpired as exc:
        exit_code = 124
        stdout = exc.stdout or b""
        stderr = exc.stderr or b""
        timed_out = True
    (AUDIT / f"raw/{name}.stdout").write_bytes(stdout)
    (AUDIT / f"raw/{name}.stderr").write_bytes(stderr)
    (AUDIT / f"raw/{name}.exit").write_text(f"{exit_code}\n")
    records.append({
        "name": name,
        "argv": argv,
        "cwd": str(cwd),
        "timeout_seconds": timeout,
        "start_unix": start,
        "elapsed_seconds": time.time() - start,
        "exit": exit_code,
        "timed_out": timed_out,
    })

(AUDIT / "raw/run_metadata.json").write_text(json.dumps(records, ensure_ascii=True, indent=2) + "\n")
raise SystemExit(1 if any(r["exit"] != 0 for r in records) else 0)
