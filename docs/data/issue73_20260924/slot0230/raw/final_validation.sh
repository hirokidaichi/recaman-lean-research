#!/bin/sh
set -eu

repo=/Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research
slot="$repo/docs/data/issue73_20260924/slot0230"
cd "$repo"

echo "HEAD $(git rev-parse HEAD)"
shasum -a 256 -c docs/adversarial_audits/H-20260917-01_20260924_0200_PARENT_SHA256SUMS
cmp <(cat "$slot/original_weekly_report_at_freeze.md" "$slot/weekly_report_append_draft.md") "$slot/proposed_weekly_report_full.md"
echo "weekly full = original + append: OK"
cmp <(cat "$slot/original_main_card_at_freeze.md" "$slot/main_card_append_draft.md") "$slot/proposed_main_card_full.md"
echo "main card full = original + append: OK"
cmp <(cat "$slot/original_handoff_at_freeze.md" "$slot/handoff_append_draft.md") "$slot/proposed_handoff_full.md"
echo "handoff full = original + append: OK"
test "$(shasum -a 256 docs/adversarial_audits/H-20260917-01_20260924_0230_parent_files/AUTOMATION_STOP.json | cut -d ' ' -f 1)" = c96851c9079b6ba199c52fc836c303f6005d0a8b2bd5893524d08ef0f1bc2168
echo "automation evidence hash: OK"
for f in "$slot"/*.md "$slot"/raw/*.txt "$slot"/raw/*.stdout "$slot"/raw/*.sh
do
  git diff --no-index --check /dev/null "$f" >/dev/null 2>&1 || code=$?
  if test "${code:-0}" -ne 1
  then
    echo "whitespace check failed: $f" >&2
    exit 1
  fi
  unset code
done
echo "candidate whitespace checks: OK"
