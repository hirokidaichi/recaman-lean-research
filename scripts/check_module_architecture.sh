#!/usr/bin/env bash
set -euo pipefail

RECAMAN_ARCH_ROOT="$(CDPATH='' cd -- "$(dirname -- "$0")/.." && pwd)"
cd "$RECAMAN_ARCH_ROOT"

RECAMAN_ARCH_ROOT_FILE="Recaman.lean"
RECAMAN_ARCH_MODULE_DIR="Recaman"
RECAMAN_ARCH_CONTRACTS="docs/MODULE_IMPORT_CONTRACTS.tsv"
RECAMAN_ARCH_EXPECTED_HEADER=$'module\tdirect_imports\tpurpose'

for RECAMAN_ARCH_REQUIRED in \
    "$RECAMAN_ARCH_ROOT_FILE" \
    "$RECAMAN_ARCH_MODULE_DIR/Audit.lean" \
    "$RECAMAN_ARCH_CONTRACTS"; do
  if [[ ! -f "$RECAMAN_ARCH_REQUIRED" ]]; then
    echo "error: missing module architecture input: $RECAMAN_ARCH_REQUIRED" >&2
    exit 1
  fi
done

RECAMAN_ARCH_NODES="$(mktemp)"
RECAMAN_ARCH_EDGES="$(mktemp)"
trap 'rm -f "$RECAMAN_ARCH_NODES" "$RECAMAN_ARCH_EDGES"' EXIT

printf 'Recaman\t%s\n' "$RECAMAN_ARCH_ROOT_FILE" > "$RECAMAN_ARCH_NODES"
while IFS= read -r RECAMAN_ARCH_FILE; do
  RECAMAN_ARCH_MODULE="${RECAMAN_ARCH_FILE%.lean}"
  RECAMAN_ARCH_MODULE="${RECAMAN_ARCH_MODULE//\//.}"
  printf '%s\t%s\n' "$RECAMAN_ARCH_MODULE" "$RECAMAN_ARCH_FILE" \
    >> "$RECAMAN_ARCH_NODES"
done < <(find "$RECAMAN_ARCH_MODULE_DIR" -maxdepth 1 -type f -name '*.lean' -print | sort)

if ! awk -F '\t' '
  {
    if (seen[$1]++) {
      print "error: duplicate module node: " $1 > "/dev/stderr"
      bad = 1
    }
  }
  END { exit bad }
' "$RECAMAN_ARCH_NODES"; then
  exit 1
fi

while IFS=$'\t' read -r RECAMAN_ARCH_MODULE RECAMAN_ARCH_FILE; do
  awk -v source="$RECAMAN_ARCH_MODULE" '
    $1 == "import" {
      for (field = 2; field <= NF; field += 1) {
        print source "\t" $field
      }
    }
  ' "$RECAMAN_ARCH_FILE" >> "$RECAMAN_ARCH_EDGES"
done < "$RECAMAN_ARCH_NODES"

if ! awk -F '\t' '
  {
    key = $1 SUBSEP $2
    if (seen[key]++) {
      print "error: duplicate direct import: " $1 " -> " $2 > "/dev/stderr"
      bad = 1
    }
    if ($1 == $2) {
      print "error: self import: " $1 > "/dev/stderr"
      bad = 1
    }
  }
  END { exit bad }
' "$RECAMAN_ARCH_EDGES"; then
  exit 1
fi

if ! awk -F '\t' '
  NR == FNR { node[$1] = 1; next }
  $2 ~ /^Recaman(\.|$)/ && !($2 in node) {
    print "error: unresolved project import: " $1 " -> " $2 > "/dev/stderr"
    bad = 1
  }
  END { exit bad }
' "$RECAMAN_ARCH_NODES" "$RECAMAN_ARCH_EDGES"; then
  exit 1
fi

if ! awk -F '\t' '
  NR == FNR {
    node[$1] = 1
    next
  }
  $2 in node {
    degree[$1] += 1
    adjacency[$1, degree[$1]] = $2
    indegree[$2] += 1
  }
  END {
    reachable["Recaman"] = 1
    do {
      changed = 0
      for (source in node) {
        if (!reachable[source]) continue
        for (edge = 1; edge <= degree[source]; edge += 1) {
          target = adjacency[source, edge]
          if (!reachable[target]) {
            reachable[target] = 1
            changed = 1
          }
        }
      }
    } while (changed)

    missing = 0
    library_count = 0
    reachable_library_count = 0
    for (module in node) {
      if (module == "Recaman" || module == "Recaman.Audit") continue
      library_count += 1
      if (reachable[module]) {
        reachable_library_count += 1
      } else {
        print "error: module is outside the Recaman root closure: " module > "/dev/stderr"
        missing += 1
      }
    }

    for (module in node) active[module] = 1
    do {
      changed = 0
      for (module in node) {
        if (!active[module] || indegree[module] != 0) continue
        active[module] = 0
        changed = 1
        for (edge = 1; edge <= degree[module]; edge += 1) {
          target = adjacency[module, edge]
          indegree[target] -= 1
        }
      }
    } while (changed)

    cycle_affected = 0
    for (module in node) {
      if (active[module]) {
        print "error: module is in or downstream of an import cycle: " module > "/dev/stderr"
        cycle_affected += 1
      }
    }

    if (missing || cycle_affected) exit 1
    print "Module graph audit: Recaman root reaches " reachable_library_count \
      " of " library_count " library modules; Audit is a separate acyclic entry point."
  }
' "$RECAMAN_ARCH_NODES" "$RECAMAN_ARCH_EDGES"; then
  exit 1
fi

IFS= read -r RECAMAN_ARCH_ACTUAL_HEADER < "$RECAMAN_ARCH_CONTRACTS"
if [[ "$RECAMAN_ARCH_ACTUAL_HEADER" != "$RECAMAN_ARCH_EXPECTED_HEADER" ]]; then
  echo "error: unexpected module import contract header" >&2
  exit 1
fi

if ! awk -F '\t' '
  NR == 1 { next }
  NF != 3 {
    print "error: import contract row " NR " has " NF " fields, expected 3" > "/dev/stderr"
    bad = 1
    next
  }
  {
    for (field = 1; field <= 3; field += 1) {
      if ($field == "") {
        print "error: import contract row " NR " has an empty field" > "/dev/stderr"
        bad = 1
      }
    }
    if (seen[$1]++) {
      print "error: duplicate import contract module: " $1 > "/dev/stderr"
      bad = 1
    }
  }
  END { exit bad }
' "$RECAMAN_ARCH_CONTRACTS"; then
  exit 1
fi

RECAMAN_ARCH_CONTRACT_COUNT=0
while IFS=$'\t' read -r RECAMAN_ARCH_MODULE RECAMAN_ARCH_IMPORTS RECAMAN_ARCH_PURPOSE; do
  if [[ "$RECAMAN_ARCH_MODULE" == "module" ]]; then
    continue
  fi
  : "$RECAMAN_ARCH_PURPOSE"
  RECAMAN_ARCH_SOURCE="$(printf '%s\n' "$RECAMAN_ARCH_MODULE" | sed 's#\.#/#g').lean"
  if [[ ! -f "$RECAMAN_ARCH_SOURCE" ]]; then
    echo "error: import contract module has no source: $RECAMAN_ARCH_MODULE" >&2
    exit 1
  fi
  RECAMAN_ARCH_ACTUAL_IMPORTS="$(awk '
    $1 == "import" {
      for (field = 2; field <= NF; field += 1) print $field
    }
  ' "$RECAMAN_ARCH_SOURCE" | paste -sd ';' -)"
  if [[ -z "$RECAMAN_ARCH_ACTUAL_IMPORTS" ]]; then
    RECAMAN_ARCH_ACTUAL_IMPORTS="-"
  fi
  if [[ "$RECAMAN_ARCH_ACTUAL_IMPORTS" != "$RECAMAN_ARCH_IMPORTS" ]]; then
    echo "error: direct import contract mismatch for $RECAMAN_ARCH_MODULE" >&2
    echo "  expected: $RECAMAN_ARCH_IMPORTS" >&2
    echo "  actual:   $RECAMAN_ARCH_ACTUAL_IMPORTS" >&2
    exit 1
  fi
  RECAMAN_ARCH_CONTRACT_COUNT=$((RECAMAN_ARCH_CONTRACT_COUNT + 1))
done < "$RECAMAN_ARCH_CONTRACTS"

if [[ "$RECAMAN_ARCH_CONTRACT_COUNT" -eq 0 ]]; then
  echo "error: module import contract registry is unexpectedly empty" >&2
  exit 1
fi

echo "Import contract audit: $RECAMAN_ARCH_CONTRACT_COUNT frontier modules match their direct-import boundary."
