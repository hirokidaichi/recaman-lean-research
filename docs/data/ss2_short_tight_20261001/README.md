# Issue #81: arbitrary-length SS=2 donor / short tight B

Conclusion: E-366 is PROVED-LEAN for every donor length and positive period.
Only B's member windows have lag 3/7/11. See the hypothesis card and the
statement/independent audits for the exact assumptions and remaining scope.

## Reproduction and provenance

Run from the repository root, Lean 4.33.1 / Python 3:

```sh
shasum -a 256 -c docs/data/ss2_short_tight_20261001/PRE_RUN_SHA256SUMS
python3 experiments/ss2_short_tight.py discovery
python3 experiments/ss2_short_tight.py holdout
python3 scripts/harness_gate.py --lint-module Recaman/SS2ShortTight.lean
python3 scripts/report_vacuity.py --all Recaman/SS2ShortTight.lean
lake env lean -t 0 docs/data/ss2_short_tight_20261001/semantic_controls.lean
./scripts/check.sh
make test
```

The Python JSON records the exact executed source revision and script hash.
protocol.frozen.md and PRE_RUN_SHA256SUMS were frozen before those runs.
Discovery lengths 3/7/11/15/19 contain 3,021 P2 words and 269 minimal SS2
words. The claim-specific holdout length 23 has 30,554 P2 words and 647
minimal SS2 words. These are explicitly reused repository ranges, not
previously unexamined data. Four placements per donor give 3,664 checks
with no violation. Literal enumeration through length 11 independently
matches all 34 P2 words among 4,095 binary words. These are COMPUTED
observations, not the proof of the all-length statement.

The independent auditor reproduced the enumerations in absolute stream
coordinates, checked all premises of positive and negative controls, and
ran kernel-checked applications of the final theorem. Positive controls
include p26/d19/nonempty B and the p18 example with a w1 member. Negative
controls remove donor minimality (p16), SS=2 (p4), or tightness (p17).
Both zero- and one-A terminal tails are covered. See semantic_controls.lean
and the independent report for literal words and commands.

The selected September proof hints are identified by draft_provenance.json.
They were uncommitted files in another session, not accepted dependencies.
The card records which fragments were adapted and rechecked. Existing
owner-family helper extractions keep the prior hypotheses and conclusions.

## Validation

full-check.log records 394 jobs and 2625 allowed-axiom reports. Lint and
vacuity logs are heuristics only; independent semantic auditing separately
checks the binder scope, dependencies, true oldest offset and all w1 S
positions. test.log records the complete Lean / empirical / viewer checks.
The final-source SHA256SUMS records the proof sources and audit controls.

No conjecture repair was needed. Ordinary Lean elaboration corrections
were made before the successful final source build. The first full check
attempt stopped because the new registry row was not yet linked from the
frontier; after completing that documentation, the full check passed.

The next decision is a new falsifiable condition for long B members.
No general Hall, deletion theorem, Gate T6 or orbit result is claimed.

The independent report is preserved verbatim, with its original `/tmp`
paths. Local copies are semantic_controls.lean/log, independent_axioms.lean/log,
independent_commands.json, independent_source.log, independent_vacuity.log,
independent_lint.log and independent_entry_counts.json. The parent additionally
rechecked the saved controls with `-t 0` (controls-trust0.log).
