# Exact execution record

This corrects only the abbreviated `Exact commands` section of
`AUDIT_REPORT.md`. That original report and its original `SHA256SUMS` are kept
unchanged. Commands below are the substantive process argv actually executed,
not a claim that the later reconstruction itself was run. Shell redirection and
exit capture surrounded each argv as shown by the named `.stdout`, `.stderr`,
and `.exit` files.

## Common state

- Repository cwd (`REPO`):
  `/Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research`
- Audit cwd (`AUDIT`): `/tmp/recaman-audit-20260923-0230-sol`
- HEAD at start: `08c08565c743f39350c9b959e1df7d30aa1cae5d`
- Target was untracked in a dirty tree; exact dirty listing is in the first tool
  transcript and summarized in `START_STATE.txt`.
- Every substantive execution below had wall timeout 120 seconds. No seed was
  used; all finite checks were exhaustive.

## Pre-execution hashes

The first read-only shell invocation at `2026-09-23 02:33:43 JST`, before any
audit execution, ran this exact command from `REPO`:

```text
date '+%Y-%m-%d %H:%M:%S %Z'; git rev-parse HEAD; git status --short; mkdir -p /tmp/recaman-audit-20260923-0230-sol; sha256sum Recaman/SS2OldestPattern.lean experiments/issue73_20260920/ss2_intervening_prefix.py docs/data/issue73_20260920/daytime/intervening_discovery.jsonl docs/data/issue73_20260920/daytime/intervening_holdout.jsonl docs/data/issue73_20260920/daytime/PRE_INTERVENING_SHA256SUMS docs/HYPOTHESIS_CARD_2026-09-20_MINIMAL_DONOR_PATTERNS.md docs/HYPOTHESIS_CARD_2026-09-17_SHORT_TIGHT_DONOR_AVOIDANCE.md docs/SS2_MINIMAL_DONOR_PATTERN_ARGUMENT_2026-09-20.md docs/RESEARCH_PLAN_2026-09-17_ONE_WEEK.md
```

Its output was returned by the tool and key hashes were immediately sent to the
parent. `START_STATE.txt` is explicitly a later transcription, not an original
raw redirect. Relevant pre-run hashes were:

```text
a9540f5f891198ec91eefd73f62f9e35d4e59f645936dc3a349504e529b325de  Recaman/SS2OldestPattern.lean
1ae348ab0b64db9168f7db27b07cf6763757939763d32f79fe8bdcb1be2d545a  experiments/issue73_20260920/ss2_intervening_prefix.py
2a6a156469a4f589f455522fa5e65e29d90e2cf33a54d81356b3fd7991b52a2c  intervening_discovery.jsonl
e0589e5cc2ddca2d2343a88879ae4993117de7c1631a972cebd628dabb9aa3b5  intervening_holdout.jsonl
```

Each new independent audit source was hashed after creation and before its
first execution. Those exact `sha256sum` outputs are preserved in
`PRE_RUN_SHA256SUMS`:

```text
f38ff7c24e62103cc97ae6b28c6feec3bef925c414114bccd1b95335aba8b6a3  independent_check.py
3c5866fcf635d684e16937dead2a523dc685bdf729e3406890430f0ad43ee440  TargetAxioms.lean
e4201f304e9391e65e9f3cbcef058d3c58ef2dc31266b0493b5f3019efe05170  inequality_check.py
698c8628d066380a504ef76b3788006a02e9eb74d647e5cb80c87b67b2fd5a67  full_counts_check.py
```

## Executed argv and raw files

| # | cwd | Exact argv | Source identity at execution | Exit | Raw stdout / stderr |
|---:|---|---|---|---:|---|
| 1 | `REPO` | `["timeout","120","python3","/tmp/recaman-audit-20260923-0230-sol/independent_check.py"]` | `independent_check.py` SHA `f38ff7c24e62103cc97ae6b28c6feec3bef925c414114bccd1b95335aba8b6a3` | 0 | `independent_check.stdout` / `independent_check.stderr`; `independent_check.exit` |
| 2 | `REPO` | `["timeout","120","python3","/tmp/recaman-audit-20260923-0230-sol/inequality_check.py"]` | `inequality_check.py` SHA `e4201f304e9391e65e9f3cbcef058d3c58ef2dc31266b0493b5f3019efe05170` | 0 | `inequality_check.stdout` / `inequality_check.stderr`; `inequality_check.exit` |
| 3 | `REPO` | `["timeout","120","python3","/tmp/recaman-audit-20260923-0230-sol/full_counts_check.py"]` | `full_counts_check.py` SHA `698c8628d066380a504ef76b3788006a02e9eb74d647e5cb80c87b67b2fd5a67` | 0 | `full_counts_check.stdout` / `full_counts_check.stderr`; `full_counts_check.exit` |
| 4 | `REPO` | `["timeout","120","python3","experiments/issue73_20260920/ss2_intervening_prefix.py","--mode","discovery"]` | experiment SHA `1ae348ab0b64db9168f7db27b07cf6763757939763d32f79fe8bdcb1be2d545a` | 0 | `original_discovery.stdout` / `original_discovery.stderr`; `original_discovery.exit` |
| 5 | `REPO` | `["timeout","120","python3","experiments/issue73_20260920/ss2_intervening_prefix.py","--mode","holdout"]` | same experiment SHA `1ae348ab...` | 0 | `original_holdout.stdout` / `original_holdout.stderr`; `original_holdout.exit` |
| 6 | `REPO` | `["timeout","120","lake","env","lean","/tmp/recaman-audit-20260923-0230-sol/TargetAxioms.lean"]` | diagnostic SHA `3c5866fcf635d684e16937dead2a523dc685bdf729e3406890430f0ad43ee440`; target SHA `a9540f5f...` | 0 | `target_axioms.stdout` / `target_axioms.stderr`; `target_axioms.exit` |
| 7 | `REPO` | `["timeout","120","python3","scripts/report_vacuity.py","--all","Recaman/SS2OldestPattern.lean"]` | target SHA `a9540f5f...`; script post-run current SHA `9047ec7d616cf490e91c19d048072e3a799e58884b173aa4cac9a1202dd3a6ac` | 0 | `report_vacuity.stdout` / `report_vacuity.stderr`; `report_vacuity.exit` |
| 8 | `REPO` | `["timeout","120","python3","scripts/harness_gate.py","--lint-module","Recaman/SS2OldestPattern.lean"]` | target SHA `a9540f5f...`; script post-run current SHA `e07f50f2696a28ffc441ff2d99675bd8d8b4389ea0717a88833259adc6ca1107` | 0 | `harness_lint.stdout` / `harness_lint.stderr`; `harness_lint.exit` |
| 9 | `REPO` | `["timeout","120","lake","env","lean","Recaman/SS2OldestPattern.lean"]` | target SHA `a9540f5f891198ec91eefd73f62f9e35d4e59f645936dc3a349504e529b325de` | 0 | `direct_lean.stdout` / `direct_lean.stderr`; `direct_lean.exit` |
| 10 | `REPO` | `["timeout","120","./scripts/check.sh"]` | dirty repo state at HEAD above; target SHA `a9540f5f...`; `check.sh` post-run current SHA `38a5f90fa92a9a73fb54a69ffda5e34095c7bfe4fd6c70674f11148b1a26e536` | 0 | `whole_check.stdout` / `whole_check.stderr`; `whole_check.exit` |

Rows 7, 8, and 10 did not have separate script hashes persisted before their
execution. The displayed script hashes were measured later at 02:42:45 JST and
are post-run current-state hashes only; they must not be represented as pre-run
provenance. The target hash was recorded before those executions. The first
tool call returned the four result objects for rows 7-10; all exact argv above
are copied from those submitted command strings, not guessed from output.

The actual shell wrapper for rows 1-10 redirected stdout/stderr to the named raw
files, captured `rc=$?`, and wrote the decimal exit to the named `.exit` file.
No stderr file has content.

## Comparison commands

After rows 4-5, the following exact read-only commands were executed from
`REPO`; their exit values were printed to the tool result, but no separate raw
file was created at that moment:

```text
cmp -s /tmp/recaman-audit-20260923-0230-sol/original_discovery.stdout docs/data/issue73_20260920/daytime/intervening_discovery.jsonl
cmp -s /tmp/recaman-audit-20260923-0230-sol/original_holdout.stdout docs/data/issue73_20260920/daytime/intervening_holdout.jsonl
```

Both printed exit 0. This is a reconstructed record of already executed argv,
not a newly fabricated raw log. The output hashes independently establish the
same byte identity:

```text
2a6a156469a4f589f455522fa5e65e29d90e2cf33a54d81356b3fd7991b52a2c  original_discovery.stdout
e0589e5cc2ddca2d2343a88879ae4993117de7c1631a972cebd628dabb9aa3b5  original_holdout.stdout
```

## Exact outputs, cutoffs, and seed

- Row 1: all binary words lengths 1..18; target count 8, failures 0. Independent
  exact-SS2 composition pools length 20/24 were 1,620/3,630; full-premise
  selected counts 8/16; failures 0. Seed `None`.
- Row 2: cutoff 12, q values 0..4; q-budget instances 11,517, AA instances
  1,361; failures 0. Seed `None`.
- Row 3: all binary words lengths 1..18; q values actual SS count through 4;
  q-budget 434,721, AA 45,976; target equality 3, strict-negative 5; four
  premise-deletion controls all conclude `false`. Seed `None`.
- Row 4: every binary word through length 18; checked 8; PASS; failures 0.
- Row 5: generated known ranges length 20/24; checked 8/16; PASS; failures 0.
- Row 6: exact signatures and target axioms printed; only repository-allowed
  core axioms. Row 7: 0/13 flagged. Row 8: 13/13 substantive. Row 9: compile
  exit 0. Row 10: 392 jobs, root 389/389 modules, 2,572 declarations in its
  printed axiom set, exit 0.

The detailed JSON/text is in the raw stdout files, whose hashes are pinned by
the manifests. No claimed range beyond those listed was executed.

## Manifest verification

The original manifest was checked from `AUDIT` with exact argv
`["sha256sum","-c","SHA256SUMS"]`; exit 0 and every listed file reported OK.
The command was executed after `AUDIT_REPORT.md` and the old manifest existed.
The later corrected manifest is verified separately and does not alter the old
report or old manifest.
