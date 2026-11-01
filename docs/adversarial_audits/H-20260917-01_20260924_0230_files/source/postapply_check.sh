#!/bin/sh
set -eu

repo=/Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research
audit=/tmp/recaman-weekly-audit-20260924-0230-sol
cd "$repo"

cmp docs/RESEARCH_WEEKLY_REPORT_2026-09-24.md \
  "$audit/source/candidates/proposed_weekly_report_full.final.md"
cmp docs/HYPOTHESIS_CARD_2026-09-17_SHORT_TIGHT_DONOR_AVOIDANCE.md \
  "$audit/source/candidates/proposed_main_card_full.final.md"
cmp docs/RESEARCH_HANDOFF_2026-09-24_SOL.md \
  "$audit/source/candidates/proposed_handoff_full.final.md"
test "$(git rev-parse HEAD)" = 08c08565c743f39350c9b959e1df7d30aa1cae5d
sha256sum \
  docs/RESEARCH_WEEKLY_REPORT_2026-09-24.md \
  docs/HYPOTHESIS_CARD_2026-09-17_SHORT_TIGHT_DONOR_AVOIDANCE.md \
  docs/RESEARCH_HANDOFF_2026-09-24_SOL.md \
  Recaman/ShortTightDonorAvoidance.lean \
  Recaman/SS2OldestPattern.lean \
  docs/EVIDENCE_REGISTRY.tsv \
  docs/PROTECTED_CLAIMS.tsv \
  docs/CURRENT_FRONTIER.md \
  docs/PROOF_MAP.md
printf 'postapply_byte_compare=3/3 OK\n'
