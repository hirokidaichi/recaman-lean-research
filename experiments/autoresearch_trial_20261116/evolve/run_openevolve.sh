#!/usr/bin/env bash
# Usage: run_openevolve.sh <venv-with-openevolve> <output-dir> [iterations]
# The LLM (claude -p) runs in an empty directory; candidates run in sandbox-exec.
set -euo pipefail
HERE="$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)"
VENV="$1"; OUT="$2"; ITERS="${3:-16}"
mkdir -p "$OUT/llm_cwd"
sed "s|cwd: null|cwd: \"$OUT/llm_cwd\"|" "$HERE/config.yaml" > "$OUT/config.yaml"
"$VENV/bin/openevolve-run" "$HERE/initial_program.py" "$HERE/evaluator.py" \
  --config "$OUT/config.yaml" --output "$OUT/run" --iterations "$ITERS"
