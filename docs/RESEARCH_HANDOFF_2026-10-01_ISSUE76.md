# Issue #76 handoff

Conclusion: E-364 is `PROVED-LEAN`. The fixed explicit word for every Nat q
is minimal P2, has exactly q overlapping SS pairs, and maximum terminal
A-run q-1 (saturated Nat subtraction). Both directions of the all-proper
mass-one prefix classification are proved. The construction imports only
OneSSMultiplicity and does not depend on the upper bound E-363.
Issue #76 remains OPEN pending separate-session semantic review.

Hypothesis card: H-20261001-04, `PROVED-LEAN`, independent review pending.
Base: `cbe51b7b1216f9700f432eb14803277113c02af4` (#75, draft PR #78).
Primary checkout's other-session files were never changed or consumed.

## Changed files

- `Recaman/TerminalASharpWords.lean`: fixed words, run/SA arithmetic,
  complete prefix classification and converse, exact count/tail, all-q result.
- `Recaman.lean`, `Recaman/Audit.lean`: root integration, 31 axiom reports.
- Hypothesis card, verbatim statement audit E-364, this handoff.
- `experiments/terminal_a_sharp_words.py` and exact frozen/reproduction data
  in `docs/data/terminal_a_sharp_words_20261001/`.
- Registry/current frontier/proof map/original-paper follow-up, regenerated
  viewer manifest. E-361 retains its original paper artifact/label; all
  its mathematical components now have separate Lean rows E-362/E-363/E-364.

## Commands and strongest evidence

Run from the worktree root:

```bash
shasum -a 256 -c docs/data/terminal_a_sharp_words_20261001/PRE_RUN_SHA256SUMS
shasum -a 256 -c docs/data/terminal_a_sharp_words_20261001/RERUN_SHA256SUMS
python3 experiments/terminal_a_sharp_words.py
lake env lean Recaman/TerminalASharpWords.lean
lake build Recaman.TerminalASharpWords
lake env lean docs/data/terminal_a_sharp_words_20261001/semantic_controls.lean
python3 scripts/harness_gate.py --lint-module Recaman/TerminalASharpWords.lean
python3 scripts/report_vacuity.py --all Recaman/TerminalASharpWords.lean
python3 scripts/harness_gate.py --audit-template E-364
python3 viewer/gen_manifest.py
./scripts/check.sh
```

Full check passes 393 jobs and 2,600 permitted-axiom reports.
Harness lint: 25/31 substantive. Vacuity flags two acknowledged arithmetic
helpers (square_ge_twice_add_three, pairCount_int), neither cited in the
registry. Conservative manual R/W/C/T=11/20/0/0.

The strongest evidence is the all-length four-region prefix classification:
every proper mass-one prefix has moment 1, -i-2 or -n-3. The reverse
direction verifies that precisely those positions occur. Final-A-region
mass one forces the complete length, so no missing proper case remains.
The numeric insertion count is derived with justified Nat subtraction;
minimality is never an assumption of the construction theorem.

## Failed attempts and controls

No mathematical counterexample or quantifier repair occurred. The full
classification route compiled within three minutes of the 90-minute gate.
Initial Lean failures concerned simp order, associative multiplication,
inequality simplification, and a misplaced proof block; repairs changed
no statement or assumptions.

The general formula at q=0,1,2 fails P2; these cases are explicitly
separate. At q=3, n=1, length=11 and t=2. Its proper mass-one positions
are [1,5,7], with moments [1,-3,-4]. The q=2 word also has length 11 but
t=1 and is different. Replacing n=1 by n=0 at q=3 preserves mass, SS count
and tail but gives moment 1, exposing a false P2 shortcut. SSS counts two.
All of these controls are kernel checked.

The old q=0..10 discovery and q=11..40 holdout are reproduced; all word
properties and q=3..40 complete prefix classifications pass. The initial
classification probe was exploratory; the saved reproducibility script
was hashed before rerun. This is reused finite evidence, not a fresh
holdout and not the all-q proof.

## Remaining uncertainty and next decision

Same-session proposer/falsifier/formalizer/auditor passes are complete.
Separate-session semantic review for #74/#75/#76 remains distinct and
pending. Together E-363/E-364 prove the sharp bound for every abstract
word and attain it at every q; none asserts that the words occur in an
actual Recaman orbit. Owner delta, matching/Hall, general #73 and all
protected central claims remain unchanged.

Stop this construction unit at the proved all-q result. Review its exact
statements and controls independently, then decide a separate falsifiable
owner-offset unit. Do not reopen stopped finite-lag certificate extensions
or infer general Gate T6 from the terminal-A bound.
