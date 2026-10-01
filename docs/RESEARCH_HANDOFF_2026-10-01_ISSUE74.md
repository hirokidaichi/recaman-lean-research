# Issue #74 handoff

Conclusion: the exact all-length minimal-P2-ending-S theorem and the
least-positive-P2-prefix corollary are `PROVED-LEAN` as E-362. Every prefix
has mass ≤2; no earlier moment sign, length cutoff, SS, periodicity, orbit,
or history hypothesis was added. Issue #74 remains OPEN because its
separate-session semantic review has not yet occurred.

Hypothesis card: H-20261001-02, status `PROVED-LEAN`, review pending.
Base: `65f457efdd36a2ec8f47283a9ddc36e173333d56`, the pushed paper branch
`codex/p2-terminal-tail-bound`, which was not merged into local main.
All work is isolated from the primary checkout's pre-existing dirty files.

## Changed files

- `Recaman/FirstP2EndingS.lean`: shifted-moment recurrence, positive
  invariant before P2, exact main theorem, least-index corollary.
- `Recaman.lean`, `Recaman/Audit.lean`: root integration and four axiom reports.
- `docs/HYPOTHESIS_CARD_2026-10-01_FIRST_P2_ENDING_S.md`,
  `docs/statement_audits/E-362.md`: frozen question and semantic decision.
- `experiments/first_p2_ending_s.py`,
  `docs/data/first_p2_ending_s_20261001/`: literal falsifier, frozen protocol,
  exact outputs, kernel negative controls, validation logs.
- `docs/EVIDENCE_REGISTRY.tsv`, `docs/CURRENT_FRONTIER.md`,
  `docs/PROOF_MAP.md`, `docs/TERMINAL_A_BUDGET_2026-10-01.md`: record
  the section-3 component without upgrading E-361's SS bounds/witnesses.
- `viewer/manifest.json`: regenerate required module metadata.

## Strongest evidence and commands

The Lean declarations quantify over actual arbitrary Bool words, not free
arithmetic parameters or a newly defined assumption. The final-sign
recursion derives D>0 for `D=moment-length*(mass-1)` before P2. A final A
in a minimal P2 word would increase D from a positive value, whereas P2
forces D=0. Strong induction constructs the least positive P2 index.

Commands (run from the worktree root):

```bash
python3 experiments/first_p2_ending_s.py discovery
python3 experiments/first_p2_ending_s.py holdout
shasum -a 256 -c docs/data/first_p2_ending_s_20261001/PRE_RUN_SHA256SUMS
lake build Recaman.LeadingRunSupply
lake env lean Recaman/FirstP2EndingS.lean
lake env lean docs/data/first_p2_ending_s_20261001/semantic_controls.lean
python3 scripts/harness_gate.py --lint-module Recaman/FirstP2EndingS.lean
python3 scripts/report_vacuity.py --all Recaman/FirstP2EndingS.lean
python3 scripts/harness_gate.py --audit-template E-362
python3 viewer/gen_manifest.py
./scripts/check.sh
```

Full validation: 391 jobs; 2,553 audited declarations within
`{propext, Classical.choice, Quot.sound}`. G1-G5, pinned central labels,
root closure/import contracts and prohibited-proof scan pass.
Lint: 3/4 substantive; vacuity report: 0/4 flagged. Discovery enumerated
4,095 words, holdout 126,976, with zero first-P2 or D-invariant violations.
Computation is finite evidence and is not used in the general proof.

## Failed attempts and counterexamples

No mathematical counterexample or hypothesis repair occurred. Instead of
formalizing excursion lists, the same claim was proved by the shifted-moment
recurrence, whose elementary induction path passed within the 90-minute gate.
Early Lean failures concerned standard-library recursor/tactic names,
`take length` simplification, and a local decidability instance for the
standalone controls. Their fixes changed no quantifiers or assumptions.

- `AASASSA`: P2, ceiling 2, A final sign, earlier P2 at 3. Removing
  minimality from the whole-word conclusion is false.
- `AAASSSASASA`: minimal P2, A final sign, ceiling 3. Replacing 2 by 3
  is false; the existing SS=2 obstruction is respected.
- Empty/A/ASSA: no P2 prefix; existence is not inferred from mass or
  moment separately.

Both weakened-statement controls are checked by Lean and literal computation.

## Remaining uncertainty and next decision

The same-session proposer, falsifier, formalizer, and auditor passes are
complete. An independent-session semantic review remains required by #74;
this handoff does not claim human or independent-agent review.

Review E-362's signatures and negative controls, then use the accepted
lemma in #75 to derive the prefix ceiling from suffix SS bounds. Stop this
unit here. Do not extend it to #76, owner delta, M1/M2, general Gate T6,
E-070/E-067, or surjectivity. E-361 remains `PROVED-PAPER`; all pinned
central labels remain unchanged.
