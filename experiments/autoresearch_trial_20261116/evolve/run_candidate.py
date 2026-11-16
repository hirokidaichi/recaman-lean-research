"""Run one candidate strategy on the fixed benchmark and print metrics as JSON.

Invoked by evaluator.py inside `sandbox-exec` (no network, no writes outside
/private/tmp), so LLM-written code cannot touch the repository.
"""
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import bench  # noqa: E402

program, n, budget = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
seeds = [int(x) for x in sys.argv[4].split(",")]
mod = bench.load(program)
rows = [bench.run_task(mod, n, budget, s) for s in seeds]
print(json.dumps(rows))
