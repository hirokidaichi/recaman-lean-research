#!/bin/sh
set -eu

base=/tmp/recaman-weekly-audit-20260924-0200-sol/source
orig=$base/writer_originals
final=$base/writer_final

check_full() {
  label=$1
  original=$2
  append=$3
  full=$4
  original_bytes=$(wc -c < "$original" | tr -d ' ')

  head -c "$original_bytes" "$full" | cmp - "$original"
  separator=$(dd if="$full" bs=1 skip="$original_bytes" count=1 2>/dev/null | od -An -tu1 | tr -d ' ')
  test "$separator" = 10
  tail -c +$((original_bytes + 2)) "$full" | cmp - "$append"
  printf '%s: PASS original_bytes=%s separator=LF\n' "$label" "$original_bytes"
}

check_full weekly \
  "$orig/original_weekly_report_at_freeze.md" \
  "$final/weekly_report_append_draft.md" \
  "$final/proposed_weekly_report_full.md"

check_full main_card \
  "$orig/original_main_card_at_freeze.md" \
  "$final/main_card_append_draft.md" \
  "$final/proposed_main_card_full.md"
