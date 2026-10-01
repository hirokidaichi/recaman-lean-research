# Issue #75 handoff

Conclusion: the exact all-length terminal-A SS bounds are `PROVED-LEAN`
as E-363. P2 gives t<=q; minimal P2 with t>0 gives t<q and hence
t<=q-1 with saturated Nat subtraction. SS=2 therefore gives t<=1.
Every P2 word has the terminal-S/A decomposition, whose t is proved to
be the maximal final A run. No prefix ceiling or cutoff was assumed.
Issue #75 remains OPEN: separate-session semantic review is pending.

Hypothesis card: H-20261001-03, `PROVED-LEAN`, review pending.
Base: `07d75dfdb733dfa5196f608e63bd23dd754940bf` (#74, draft PR #77).
Work was isolated from all pre-existing primary-checkout changes.

## Changed files

- `Recaman/TerminalASSBound.lean`: decomposition and maximum-run meaning,
  SS suffix budget, moment inequality, derived prefix ceiling, exact bounds.
- `Recaman.lean`, `Recaman/Audit.lean`: root import and 16 axiom reports.
- Hypothesis card, `docs/statement_audits/E-363.md`, and this handoff.
- `docs/data/terminal_a_ss_bound_20261001/`: frozen protocol/hashes,
  exact reproduction outputs, boundary controls, validation logs.
- Registry, current frontier, proof map, original paper follow-up and
  regenerated `viewer/manifest.json`.

## Commands and strongest evidence

Run from the worktree root:

```bash
shasum -a 256 -c docs/data/terminal_a_ss_bound_20261001/PRE_RUN_SHA256SUMS
python3 experiments/terminal_a_budget.py discovery
python3 experiments/terminal_a_budget.py holdout
lake env lean Recaman/TerminalASSBound.lean
lake build Recaman.TerminalASSBound
lake env lean docs/data/terminal_a_ss_bound_20261001/semantic_controls.lean
python3 scripts/harness_gate.py --lint-module Recaman/TerminalASSBound.lean
python3 scripts/report_vacuity.py --all Recaman/TerminalASSBound.lean
python3 scripts/harness_gate.py --audit-template E-363
python3 viewer/gen_manifest.py
./scripts/check.sh
```

Full check: 392 jobs; 2,569 audited declarations within
`{propext, Classical.choice, Quot.sound}`. Registry gates, module architecture,
pinned labels and prohibited-proof scan pass. Lint reports 16/16 substantive;
vacuity 0/16 flagged. Conservative manual R/W/C/T = 8/8/0/0.

The strongest evidence is the kernel-checked inequality on every suffix
of actual arbitrary words. It derives prefix mass<=2 under t>=q and
then uses E-362's proven first-P2-ending-S result. No new defined Prop
or arithmetic copy of the conclusion appears among the hypotheses.
Verbatim signatures and both-direction semantic audit are in E-363's audit.

Finite reproduction: discovery 3,021 P2 words; existing holdout 30,554,
zero weak/strict violations. These are repeats of the old protocol, not
a fresh holdout, and are not used as proof of the all-length inequalities.

## Failed attempts and counterexamples

No mathematical counterexample or quantifier repair occurred. Initial
Lean failures were a recursive simp rewrite of all-A words, an overly
broad mass_append rewrite, and reflexivity of inequalities. The intended
proof route compiled within six minutes of the 90-minute gate.

- AAS: q=t=0; strictness requires t>0.
- AASASSA: P2, q=t=1, earlier P2 at 3; dropping minimality is false.
- ASSA: moment zero but mass zero; A: mass one but moment one.
- AAASSSASASA: minimal P2, q=2,t=1, ceiling three; t=0 is too strong.

These controls were preserved in exact JSON and checked with Lean.

## Remaining uncertainty and next decision

Same-session proposer/falsifier/formalizer/auditor passes are complete;
independent-session review for #74/#75 remains pending. The all-q witnesses
of #76 remain `PROVED-PAPER` until their separate construction/minimality
proof is checked. Proceed to that bounded unit, independently of this upper
bound. Stop owner delta, M1/M2, general Gate T6 or surjectivity inferences
from this result. All protected central labels stay unchanged.
