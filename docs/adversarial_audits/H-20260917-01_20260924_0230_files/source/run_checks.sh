#!/bin/sh
set -eu

repo=/Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research
out=/tmp/recaman-weekly-audit-20260924-0230-sol/raw
slot=docs/data/issue73_20260924/slot0230

cd "$repo"
date '+%Y-%m-%d %H:%M:%S %Z' > "$out/time.stdout"
git rev-parse HEAD > "$out/head.stdout"
git status --short > "$out/git_status.stdout"

sha256sum -c docs/adversarial_audits/H-20260917-01_20260924_0200_PARENT_SHA256SUMS \
  > "$out/parent_manifest.stdout" 2> "$out/parent_manifest.stderr"
printf '%s\n' "$?" > "$out/parent_manifest.exit"

(cd docs/adversarial_audits/H-20260917-01_20260924_0200_files && sha256sum -c SHA256SUMS.final) \
  > "$out/prior_audit_manifest.stdout" 2> "$out/prior_audit_manifest.stderr"
printf '%s\n' "$?" > "$out/prior_audit_manifest.exit"

for prior in slot0100 slot0130 slot0200; do
  (cd "docs/data/issue73_20260924/$prior" && sha256sum -c SHA256SUMS) \
    > "$out/${prior}_manifest.stdout" 2> "$out/${prior}_manifest.stderr"
  printf '%s\n' "$?" > "$out/${prior}_manifest.exit"
done

sha256sum \
  "$slot/original_weekly_report_at_freeze.md" \
  "$slot/original_main_card_at_freeze.md" \
  "$slot/original_handoff_at_freeze.md" \
  "$slot/proposed_weekly_report_full.md" \
  "$slot/proposed_main_card_full.md" \
  "$slot/proposed_handoff_full.md" \
  "$slot/candidate_packet.md" \
  "$slot/commands.md" \
  Recaman/ShortTightDonorAvoidance.lean \
  Recaman/SS2OldestPattern.lean \
  Recaman/OwnerFamilyLagEleven.lean \
  Recaman/PeriodicOwnerFamilyLagEleven.lean \
  Recaman/Audit.lean \
  docs/statement_audits/E-360.md \
  docs/EVIDENCE_REGISTRY.tsv \
  docs/PROTECTED_CLAIMS.tsv \
  docs/CURRENT_FRONTIER.md \
  docs/PROOF_MAP.md \
  docs/RESEARCH_PLAN_2026-09-17_ONE_WEEK.md \
  docs/adversarial_audits/H-20260917-01_20260924_0230_parent_files/AUTOMATION_STOP.json \
  /Users/hirokidaichi/.codex/automations/recam-n-1-3/automation.toml \
  > "$out/target_hashes.stdout"

for file in proposed_weekly_report_full.md proposed_main_card_full.md proposed_handoff_full.md; do
  git diff --no-index --check /dev/null "$slot/$file" \
    > "$out/$file.diffcheck.stdout" 2> "$out/$file.diffcheck.stderr" || code=$?
  code=${code:-0}
  printf '%s\n' "$code" > "$out/$file.diffcheck.exit"
  test "$code" -eq 1
  code=
done

python3 /tmp/recaman-weekly-audit-20260924-0230-sol/source/audit_checks.py \
  > "$out/audit_checks.final.stdout" 2> "$out/audit_checks.final.stderr"
printf '%s\n' "$?" > "$out/audit_checks.final.exit"

python3 - <<'PY' > "$out/automation_parse.stdout" 2> "$out/automation_parse.stderr"
import json
from pathlib import Path

repo = Path('/Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research')
evidence = json.loads((repo / 'docs/adversarial_audits/H-20260917-01_20260924_0230_parent_files/AUTOMATION_STOP.json').read_text())
live_text = Path('/Users/hirokidaichi/.codex/automations/recam-n-1-3/automation.toml').read_text()
assert evidence['after']['status'] == 'PAUSED'
assert evidence['changedFields'] == ['status', 'updated_at']
assert evidence['extension'] is False
assert 'id = "recam-n-1-3"' in live_text
assert 'status = "PAUSED"' in live_text
assert 'UNTIL=20260923T173000Z' in live_text
assert '最後とし、自動延長しない' in live_text
print('automation=PAUSED')
print('rrule_until=2026-09-23T17:30:00Z=2026-09-24T02:30:00JST')
print('changed_fields=status,updated_at')
PY
printf '%s\n' "$?" > "$out/automation_parse.exit"

ps -axo pid=,ppid=,etime=,command= | \
  rg 'matching_closure|baseline_q_w|donor_length_boundary|fixed_controls|harness_gate.py|scripts/check.sh|lake build' \
  > "$out/research_processes.stdout" 2> "$out/research_processes.stderr" || code=$?
code=${code:-0}
printf '%s\n' "$code" > "$out/research_processes.exit"
