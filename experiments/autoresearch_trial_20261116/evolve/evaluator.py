"""OpenEvolve evaluator for the H+ rediscovery benchmark (fixed; never evolved).

combined_score = mean over seeds of
    best_hplus + 0.15 * min(5, max_u_at_hplus0) + 0.03 * min(5, max_u_at_hplus_m1)
so 1.0+ means an H+ violation was found, and the baselines sit near 0.3-0.4.
Discovery seeds 0,1 at 300,000 evaluations each; holdout (seeds 100-104,
5,000,000 evaluations) is run only once at the end, outside OpenEvolve.
"""
import json
import os
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
PROFILE = """(version 1)
(allow default)
(deny network*)
(deny file-write*)
(allow file-write* (subpath "/private/tmp") (subpath "/private/var/folders") (literal "/dev/null"))
"""
N, BUDGET, SEEDS = 34, 300_000, "0,1"


def score_row(r):
    return (r["best_hplus"] + 0.15 * min(5, r["max_u_at_hplus0"])
            + 0.03 * min(5, r["max_u_at_hplus_m1"]))


def evaluate(program_path):
    env = dict(os.environ, PYTHONDONTWRITEBYTECODE="1")
    cmd = ["sandbox-exec", "-p", PROFILE, "python3", str(HERE / "run_candidate.py"),
           str(program_path), str(N), str(BUDGET), SEEDS]
    try:
        p = subprocess.run(cmd, capture_output=True, text=True, timeout=100, env=env)
    except subprocess.TimeoutExpired:
        return {"combined_score": 0.0, "error": "timeout (100 s)"}
    if p.returncode != 0:
        return {"combined_score": 0.0, "error": p.stderr[-800:]}
    rows = json.loads(p.stdout.strip().splitlines()[-1])
    scores = [score_row(r) for r in rows]
    return {
        "combined_score": round(sum(scores) / len(scores), 4),
        "best_hplus": max(r["best_hplus"] for r in rows),
        "hits": sum(r["best_hplus"] >= 1 for r in rows),
        "max_u_at_hplus0": max(r["max_u_at_hplus0"] for r in rows),
        "seconds": round(sum(r["seconds"] for r in rows), 2),
        "calls": sum(r["calls"] for r in rows),
    }


if __name__ == "__main__":
    import sys
    print(json.dumps(evaluate(sys.argv[1] if len(sys.argv) > 1 else HERE / "initial_program.py")))
