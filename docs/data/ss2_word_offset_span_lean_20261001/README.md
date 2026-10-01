# Issue #82: all-k fixed-SS2 word offset span

E-367 proves the complete explicit E-365 family in Lean for every natural k.
The marked newest S is a word position, not a Hall owner. No recurrence,
periodicity, actual orbit realization or general capacity result is claimed.

## Provenance and reproduction

Execution base is in execution_base.txt: f6594be0bf04ea1baf6fb460a69c0c6b05dc1379.
The unchanged falsifier embeds its historical base cbe51b7 and protocol
H-20261001-05. The present protocol H-20261001-07 and source hashes were
frozen before rerunning it. Discovery k=0..10 and holdout k=11..80 are
explicitly reused ranges, not fresh holdout data or all-k proof.

Run from the repository root (Lean 4.33.1, Python 3):

```sh
shasum -a 256 -c docs/data/ss2_word_offset_span_lean_20261001/PRE_RUN_SHA256SUMS
python3 experiments/ss2_word_offset_span.py discovery
python3 experiments/ss2_word_offset_span.py holdout
lake env lean docs/data/ss2_word_offset_span_20261001/core_controls.lean
python3 docs/data/ss2_word_offset_span_lean_20261001/independent_entry.py
lake build Recaman.SS2WordOffsetSpan
lake env lean -t 0 docs/data/ss2_word_offset_span_lean_20261001/semantic_controls.lean
python3 scripts/harness_gate.py --lint-module Recaman/SS2WordOffsetSpan.lean
python3 scripts/report_vacuity.py --all Recaman/SS2WordOffsetSpan.lean
./scripts/check.sh
make test
```

The 81 words pass every family property and exact proper-prefix table.
The independent numeric-list checker inspects 26,811 proper prefixes and
9,963 mass-one visits over the same reused range. Wrong core at k=1 gives
P2 prefixes 7 and 19, breaking minimality; an extra AS gives final moment
-1 and earlier P2 at 19. These observations are COMPUTED and do not prove
the universal statement. The frozen protocol's phrase "an explicit k
exceeds C0" is clarified in the live card: the span exceeds C0, using k=C0.
The statement and witness never changed.

## Independent audit and kernel controls

The entry report is independent_entry.md. The original checker is preserved
as independent_entry_original.py; independent_entry.py changes only the
absolute repository path and output handling for portable reruns. The final report is
../../statement_audits/E-367-independent.md; original /tmp paths are retained
there. Saved local copies of its checks are semantic_controls.lean/log,
independent_axioms.lean/log, independent_commands.json, independent_source.log,
independent_vacuity.log and independent_lint.log. They directly apply the
general theorem at k=0,1,7, exercise both directions of prefix classification,
check actual oldest offsets and instantiate the unbounded theorem at 1000.
Both counterfactual words are kernel checked independently of that theorem.
The parent additionally rechecks the saved controls at trust level zero.

Manual R/W/C/T is 5/18/0/0; the prefix classification is the substantive
content, with E-122 padding identities and derived consequences explicitly
counted as reused/corollary work. Lint and vacuity logs are heuristic only.
No new unproved Prop premise, arithmetic-only substitution or owner claim
was introduced. Source SHA-256 is pinned in SHA256SUMS and both audits.

## Validation and next decision

full-check.log records 395 build jobs and 2648 permitted-axiom reports.
test.log records the complete Lean / empirical / viewer checks.
The first full all-k source pass was at 12:23 UTC, within the 90-minute
route gate starting 12:15 UTC. No conjecture repair or counterexample to
the fixed family occurred. Routine list/arithmetic elaboration corrections
preceded the successful source pass.

Stop word-only constant-span routes. To study actual owner delta, supply
a concrete owner-family condition under a new falsifiable research card.
General #73, Gate T6, all-lag tight avoidance and orbit realization remain
open. No additional finite-lag census is justified by this result.
