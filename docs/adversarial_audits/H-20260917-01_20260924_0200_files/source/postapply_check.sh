#!/bin/sh
set -eu

repo=/Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research
audit=/tmp/recaman-weekly-audit-20260924-0200-sol

cmp "$repo/docs/RESEARCH_WEEKLY_REPORT_2026-09-24.md" \
  "$audit/source/writer_final/proposed_weekly_report_full.md"
printf 'weekly_full_cmp: PASS\n'

cmp "$repo/docs/HYPOTHESIS_CARD_2026-09-17_SHORT_TIGHT_DONOR_AVOIDANCE.md" \
  "$audit/source/writer_final/proposed_main_card_full.md"
printf 'main_card_full_cmp: PASS\n'

test "$(git -C "$repo" rev-parse HEAD)" = 08c08565c743f39350c9b959e1df7d30aa1cae5d
printf 'head: PASS %s\n' "$(git -C "$repo" rev-parse HEAD)"

printf 'live_sha256:\n'
shasum -a 256 \
  "$repo/docs/RESEARCH_WEEKLY_REPORT_2026-09-24.md" \
  "$repo/docs/HYPOTHESIS_CARD_2026-09-17_SHORT_TIGHT_DONOR_AVOIDANCE.md" \
  "$repo/Recaman/ShortTightDonorAvoidance.lean" \
  "$repo/Recaman/SS2OldestPattern.lean"
