#!/usr/bin/env bash
set -euo pipefail

RECAMAN_PROJECT_ROOT="$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)"
cd "$RECAMAN_PROJECT_ROOT"

if command -v lake >/dev/null 2>&1; then
  RECAMAN_LAKE=(lake)
elif [[ -x ./scripts/lakew ]]; then
  RECAMAN_LAKE=(./scripts/lakew)
else
  echo "error: lake was not found" >&2
  exit 1
fi

if ! command -v rg >/dev/null 2>&1; then
  echo "error: rg (ripgrep) was not found" >&2
  exit 1
fi

"${RECAMAN_LAKE[@]}" build
"${RECAMAN_LAKE[@]}" env lean Recaman/Audit.lean

if rg -n --glob '*.lean' '\b(sorry|admit|native_decide|axiom)\b' .; then
  echo "error: prohibited proof escape or declaration found" >&2
  exit 1
fi

echo "All Lean builds and audits passed."

