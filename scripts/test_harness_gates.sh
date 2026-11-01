#!/usr/bin/env bash
# Mutating fixtures are isolated in TemporaryDirectory.
set -euo pipefail
RECAMAN_TEST_ROOT="$(CDPATH='' cd -- "$(dirname -- "$0")/.." && pwd)"
exec python3 "$RECAMAN_TEST_ROOT/scripts/test_harness_gates.py" "$@"
