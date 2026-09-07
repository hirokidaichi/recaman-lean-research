#!/usr/bin/env python3
"""The frozen prefix-128 stress test in H-20260906-06."""
import argparse
from dataclasses import replace
import hashlib
import json
from pathlib import Path
import subprocess
import time

from seeded_survival_falsifier import make_prefix, replay, search


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    value, prefix_values = 0, {0}
    for clock in range(1, 129):
        candidate = value - clock
        value = candidate if candidate > 0 and candidate not in prefix_values else value + clock
        prefix_values.add(value)
    print("protocol=H-20260906-06 prefix_horizon=128 "
          f"prefix_size={len(prefix_values)} prefix_max={max(prefix_values)}", flush=True)
    print("source_revision=" + subprocess.check_output(
        ["git", "rev-parse", "HEAD"], text=True).strip(), flush=True)
    for script in (Path(__file__), Path(__file__).with_name("seeded_survival_falsifier.py")):
        print(f"sha256 {script.name} {hashlib.sha256(script.read_bytes()).hexdigest()}", flush=True)
    results = []
    deadline = time.monotonic() + 900
    payload = {"prefix": sorted(prefix_values), "search": results}
    for v in range(10, 161):
        prefix, params = make_prefix(v)
        if prefix_values.intersection(prefix.forbidden):
            status, witness, nodes = "PREFIX_INCOMPATIBLE", None, 0
        else:
            prefix = replace(prefix, required=prefix.required | prefix_values)
            status, witness, nodes = search(prefix, 100000, deadline)
        print(f"v={v} status={status} nodes={nodes}", flush=True)
        results.append({"v": v, "status": status, "nodes": nodes})
        if witness:
            result = replay(witness, params)
            assert prefix_values.issubset(witness.required)
            assert result["next_landing"][1] not in prefix_values
            payload["witness"] = result
            print(f"WITNESS parameters={params} landing={result['next_landing']} "
                  f"seed_size={result['seed_cardinality']}", flush=True)
            break
        if time.monotonic() >= deadline:
            print("TIME_CAP", flush=True)
            break
    args.out.write_text(json.dumps(payload, indent=2) + "\n")


if __name__ == "__main__":
    main()
