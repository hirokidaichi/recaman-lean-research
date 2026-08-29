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

RECAMAN_AUDIT_LOG="$(mktemp)"
trap 'rm -f "$RECAMAN_AUDIT_LOG"' EXIT
"${RECAMAN_LAKE[@]}" env lean Recaman/Audit.lean | tee "$RECAMAN_AUDIT_LOG"

# The audit output is advisory unless the permitted axiom set is enforced.
# Each report starts with a quoted declaration name and may wrap onto
# continuation lines that begin with a space, so rejoin before matching.
awk '
function flush(record,   trimmed) {
  if (record == "") return
  total += 1
  trimmed = record
  sub(/[ \t]+$/, "", trimmed)
  if (trimmed ~ /does not depend on any axioms$/) return
  if (trimmed ~ /depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, ?(propext|Classical\.choice|Quot\.sound))*\]$/) return
  print "unexpected axiom dependency: " trimmed > "/dev/stderr"
  bad += 1
}
BEGIN { current = ""; total = 0; bad = 0 }
/^'"'"'/ { flush(current); current = $0; next }
/^[ \t]/ { sub(/^[ \t]+/, " "); current = current $0; next }
{ flush(current); current = "" }
END {
  flush(current)
  if (total == 0) {
    print "error: the axiom audit produced no reports" > "/dev/stderr"
    exit 1
  }
  if (bad > 0) {
    print "error: " bad " of " total " audited declarations use an unexpected axiom" > "/dev/stderr"
    exit 1
  }
  print "Axiom audit: " total " declarations, all within {propext, Classical.choice, Quot.sound}."
}
' "$RECAMAN_AUDIT_LOG"

if rg -n --glob '*.lean' '\b(sorry|admit|native_decide|axiom)\b' .; then
  echo "error: prohibited proof escape or declaration found" >&2
  exit 1
fi

echo "All Lean builds and audits passed."
