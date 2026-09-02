#!/usr/bin/env bash
set -euo pipefail

RECAMAN_REGISTRY_ROOT="$(CDPATH='' cd -- "$(dirname -- "$0")/.." && pwd)"
cd "$RECAMAN_REGISTRY_ROOT"

RECAMAN_REGISTRY="docs/EVIDENCE_REGISTRY.tsv"
RECAMAN_FRONTIER="docs/CURRENT_FRONTIER.md"
RECAMAN_AUDIT="Recaman/Audit.lean"
RECAMAN_EXPECTED_HEADER=$'id\tlabel\tbranch\tclaim\tartifact\taudit_symbols\treopen_gate'

for required in "$RECAMAN_REGISTRY" "$RECAMAN_FRONTIER" "$RECAMAN_AUDIT"; do
  if [[ ! -f "$required" ]]; then
    echo "error: missing research registry input: $required" >&2
    exit 1
  fi
done

if ! command -v rg >/dev/null 2>&1; then
  echo "error: rg (ripgrep) was not found" >&2
  exit 1
fi

IFS= read -r RECAMAN_ACTUAL_HEADER < "$RECAMAN_REGISTRY"
if [[ "$RECAMAN_ACTUAL_HEADER" != "$RECAMAN_EXPECTED_HEADER" ]]; then
  echo "error: unexpected evidence registry header" >&2
  exit 1
fi

if ! awk -F '\t' '
  NR == 1 { next }
  NF != 7 {
    print "error: registry row " NR " has " NF " fields, expected 7" > "/dev/stderr"
    bad = 1
    next
  }
  {
    for (field = 1; field <= 7; field += 1) {
      if ($field == "") {
        print "error: registry row " NR " has an empty field" > "/dev/stderr"
        bad = 1
      }
    }
  }
  END { exit bad }
' "$RECAMAN_REGISTRY"; then
  exit 1
fi

RECAMAN_DUPLICATE_IDS="$(tail -n +2 "$RECAMAN_REGISTRY" | cut -f1 | sort | uniq -d)"
if [[ -n "$RECAMAN_DUPLICATE_IDS" ]]; then
  echo "error: duplicate evidence ids:" >&2
  echo "$RECAMAN_DUPLICATE_IDS" >&2
  exit 1
fi

RECAMAN_ROW_COUNT=0
RECAMAN_PROVED_LEAN_COUNT=0

while IFS=$'\t' read -r evidence_id evidence_label branch claim artifact audit_symbols reopen_gate; do
  if [[ "$evidence_id" == "id" ]]; then
    continue
  fi
  : "$branch" "$claim" "$reopen_gate"

  RECAMAN_ROW_COUNT=$((RECAMAN_ROW_COUNT + 1))

  if [[ ! "$evidence_id" =~ ^E-[0-9][0-9][0-9]$ ]]; then
    echo "error: invalid evidence id: $evidence_id" >&2
    exit 1
  fi

  case "$evidence_label" in
    PROVED-LEAN|PROVED-PAPER|COMPUTED|OBSERVED|CONJECTURED|REFUTED|STOPPED) ;;
    *)
      echo "error: invalid evidence label for $evidence_id: $evidence_label" >&2
      exit 1
      ;;
  esac

  if [[ ! -f "$artifact" ]]; then
    echo "error: missing artifact for $evidence_id: $artifact" >&2
    exit 1
  fi

  if ! rg -F -q "$evidence_id" "$RECAMAN_FRONTIER"; then
    echo "error: $evidence_id is not referenced by $RECAMAN_FRONTIER" >&2
    exit 1
  fi

  if [[ "$evidence_label" == "PROVED-LEAN" ]]; then
    RECAMAN_PROVED_LEAN_COUNT=$((RECAMAN_PROVED_LEAN_COUNT + 1))
    if [[ "$audit_symbols" == "-" ]]; then
      echo "error: PROVED-LEAN row $evidence_id has no audit symbol" >&2
      exit 1
    fi
  fi

  if [[ "$audit_symbols" != "-" ]]; then
    RECAMAN_OLD_IFS="$IFS"
    IFS=';'
    for audit_symbol in $audit_symbols; do
      if [[ ! "$audit_symbol" =~ ^Recaman\.[A-Za-z0-9_.]+$ ]]; then
        echo "error: invalid audit symbol for $evidence_id: $audit_symbol" >&2
        exit 1
      fi
      if ! rg -F -q "#print axioms $audit_symbol" "$RECAMAN_AUDIT"; then
        echo "error: unaudited symbol for $evidence_id: $audit_symbol" >&2
        exit 1
      fi
    done
    IFS="$RECAMAN_OLD_IFS"
  fi
done < "$RECAMAN_REGISTRY"

if [[ "$RECAMAN_ROW_COUNT" -eq 0 || "$RECAMAN_PROVED_LEAN_COUNT" -eq 0 ]]; then
  echo "error: evidence registry is unexpectedly empty" >&2
  exit 1
fi

echo "Research registry audit: $RECAMAN_ROW_COUNT entries, $RECAMAN_PROVED_LEAN_COUNT PROVED-LEAN rows linked to Recaman/Audit.lean."
