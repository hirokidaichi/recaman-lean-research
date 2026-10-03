# Writer command record

All commands used cwd
`/Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research`.
Writer start `2026-09-24 01:32:23 JST`; HEAD
`08c08565c743f39350c9b959e1df7d30aa1cae5d`.

## Read-only discovery and identity

```text
date '+%Y-%m-%d %H:%M:%S %Z'
pwd
git status -s
git rev-parse HEAD
find docs/adversarial_audits -maxdepth 2 -type f | sort
find docs/data/issue73_20260923 -maxdepth 4 -type f | sort
find docs/data/issue73_20260924 -maxdepth 4 -type f | sort
rg -n 'donor|Donor|SS2|short|tight|prefix|minimal|oldest|E-240|E-069|E-345|E-351|E-360|H-20260920-0[2345]' docs/GLOSSARY.md docs/PROOF_MAP.md docs/CURRENT_FRONTIER.md docs/RESEARCH_PORTFOLIO.md docs/EVIDENCE_REGISTRY.tsv
```

The writer directly read with `sed -n`:

```text
AGENTS.md
docs/AI_RESEARCH_PROTOCOL.md
README.md
docs/STATUS_REPORT_2026-08-30.md
docs/ROADMAP.md
docs/RESEARCH_PLAN_2026-09-17_ONE_WEEK.md
docs/RESEARCH_HANDOFF_2026-09-23_SOL.md
docs/RESEARCH_HANDOFF_2026-09-24_SOL.md
docs/RESEARCH_WEEKLY_REPORT_2026-09-24.md
docs/HYPOTHESIS_CARD_2026-09-20_DONOR_WITHOUT_MINIMALITY.md
docs/HYPOTHESIS_CARD_2026-09-20_SHORT_PREFIX_REDUCTION.md
docs/HYPOTHESIS_CARD_2026-09-20_DONOR_LENGTH_BOUNDARY.md
docs/HYPOTHESIS_CARD_2026-09-20_MINIMAL_DONOR_PATTERNS.md
Recaman/ShortTightDonorAvoidance.lean
Recaman/SS2OldestPattern.lean
docs/adversarial_audits/H-20260920-0{2,3,4,5}_20260923_*.md
docs/adversarial_audits/H-20260920-0{2,3,4,5}_20260923_*_files/*REPORT*.md
docs/data/issue73_20260923/slot0{100,130,200,230}/candidate_packet.md
docs/data/issue73_20260923/slot0{100,130,200,230}/proposed_card_final.md
```

Selected independent raw outputs were read directly, including p16 literal JSON,
H-02 finite recount tail, H-05 prefix/inequality JSON, manifests and command records.

## Exact source hashes

```text
shasum -a 256 Recaman/ShortTightDonorAvoidance.lean Recaman/SS2OldestPattern.lean \
  docs/HYPOTHESIS_CARD_2026-09-20_DONOR_WITHOUT_MINIMALITY.md \
  docs/HYPOTHESIS_CARD_2026-09-20_SHORT_PREFIX_REDUCTION.md \
  docs/HYPOTHESIS_CARD_2026-09-20_DONOR_LENGTH_BOUNDARY.md \
  docs/HYPOTHESIS_CARD_2026-09-20_MINIMAL_DONOR_PATTERNS.md \
  docs/RESEARCH_WEEKLY_REPORT_2026-09-24.md docs/RESEARCH_HANDOFF_2026-09-24_SOL.md \
  docs/adversarial_audits/H-20260920-02_20260923_0130.md \
  docs/adversarial_audits/H-20260920-03_20260923_0200.md \
  docs/adversarial_audits/H-20260920-04_20260923_0100.md \
  docs/adversarial_audits/H-20260920-05_20260923_0230.md
```

Exact hashes used are in `SOURCE_SHA256SUMS`. Exit 0.

## Writer validation

```text
cmp docs/HYPOTHESIS_CARD_2026-09-20_DONOR_WITHOUT_MINIMALITY.md docs/data/issue73_20260924/slot0130/original_h02_card_at_freeze.md
cmp docs/HYPOTHESIS_CARD_2026-09-20_SHORT_PREFIX_REDUCTION.md docs/data/issue73_20260924/slot0130/original_h03_card_at_freeze.md
cmp docs/HYPOTHESIS_CARD_2026-09-20_DONOR_LENGTH_BOUNDARY.md docs/data/issue73_20260924/slot0130/original_h04_card_at_freeze.md
cmp docs/HYPOTHESIS_CARD_2026-09-20_MINIMAL_DONOR_PATTERNS.md docs/data/issue73_20260924/slot0130/original_h05_card_at_freeze.md
cmp docs/RESEARCH_WEEKLY_REPORT_2026-09-24.md docs/data/issue73_20260924/slot0130/original_weekly_report_at_freeze.md
shasum -a 256 -c docs/data/issue73_20260924/slot0130/SOURCE_SHA256SUMS
git diff --check -- docs/data/issue73_20260924/slot0130
```

All exits were 0. Each card full proposal was also compared against its frozen original,
one blank line, and its append using `cmp` with process substitution; all four exits were 0.
The weekly full proposal intentionally also changes the opening scope paragraph, so it is not
byte-concatenation of the frozen weekly text and append.

One final verification attempt used the wrong cwd with the bare command
`shasum -a 256 -c SOURCE_SHA256SUMS`; it exited 2 with "No such file or directory".
The corrected repo-root command
`shasum -a 256 -c docs/data/issue73_20260924/slot0130/SOURCE_SHA256SUMS`
then exited 0 with all 16 entries OK. The failed path invocation is not evidence.

## Explicitly not run by writer

The writer did not run `report_vacuity.py`, `harness_gate.py`, statement-audit generation,
Lean, `./scripts/check.sh`, a finite census, discovery, or holdout. The independent joint auditor
did run current-slot fixed controls and gates; those commands and raw outputs belong to the parent
audit archive and must not be attributed to the writer. Previously saved 9/23 gate outputs were
read only and reused only at matching hashes.

No random seed or new cutoff exists. No stage or commit was run.
