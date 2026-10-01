# Hypothesis card: first P2 under prefix mass ceiling two

- ID: `H-20261001-02`
- Owner: Codex, separate proposer / falsifier / formalizer / auditor passes
- Created: 2026-10-01
- Status: `PROVED-LEAN` (E-362); independent semantic review PASS. See [E-362-independent](statement_audits/E-362-independent.md). Issue #74 remains OPEN awaiting PR incorporation.
- Research branch: isolated worktree `first-p2-ending-s`, based on
  `65f457efdd36a2ec8f47283a9ddc36e173333d56`; issue #74.

## Exact statement

For every `w : List Bool`, newest first, A=true and S=false:

```lean
theorem minimal_p2_ends_S (w : List Bool)
    (hp : LeadingRunSupply.P2 w)
    (hmin : ∀ j, 0 < j → j < w.length → ¬ LeadingRunSupply.P2 (w.take j))
    (hceil : ∀ j, j ≤ w.length → LeadingRunSupply.mass (w.take j) ≤ 2) :
    ∃ u, w = u ++ [false]
```

Also, every finite word with the same ceiling and at least one nonempty
P2 prefix has a least positive P2 prefix index, and that prefix ends S.
The corollary must return the least-index property, not just an arbitrary
S-ended P2 prefix. No length cutoff, earlier-moment sign hypothesis, SS,
NoSAAS, current-A, periodicity, orbit or history assumptions are permitted.

## Why it would matter

- Frontier obligation discharged: section 3 of E-361, required by #75.
- This excludes A-ended minimal P2 words under an independently stated
  prefix ceiling; it is neither coverage nor a wrapper around the conclusion.
- E-361 as a whole stays `PROVED-PAPER`; #75/#76 and general #73 remain separate.

## Provenance and dependencies

- Definitions: `LeadingRunSupply.mass`, `moment`, `P2`; standard list take/append.
- Existing theorems: `mass_append`, `moment_append`.
- Paper source: `docs/TERMINAL_A_BUDGET_2026-10-01.md`, section 3.
- Repository search: `LeadingRunSupply`, `LowSSEndpoint`, `OneSSMultiplicity`,
  glossary periodic P2 entries, proof map E-128/E-130/E-361, portfolio stopped
  charging/finite-lag routes. No ceiling-two first-P2 Lean theorem found.
- Unverified mathematical assumptions: none.
- Weakest useful new lemma and informal dependency chain (before Lean):
  set `D(w)=moment w - length w * (mass w - 1)`.
  Appending either sign changes D by `1-mass w`.
  Under ceiling two and no nonempty P2 prefix (including the full word),
  every nonempty word has D>0. Induct on the final sign: below height two
  D cannot decrease; at height two the next sign must be S, the decrease
  is exactly one, and equality would itself be P2. The first step gives D=1.
  For minimal P2, its proper predecessor has D>0; an A final sign forces
  predecessor mass zero, so full D>0, contradicting full P2 (D=0).
  Choose a least positive P2 index by finite induction and apply the main lemma.

## Falsification plan

- Small/boundary: empty, A, ASSA, AAS, AASASSA, AAASSSASASA.
- Weakened model: all abstract binary words, no actual-history restriction;
  remove minimality and increase ceiling to three in the negative controls.
- Discovery: literal words of lengths 0..11; evaluate both the issue claim
  and the stronger D invariant. This reuses a known small range.
- Frozen holdout: literal words of lengths 12..16; one run after discovery.
  Disjoint for this new invariant protocol, not untouched repository data.
- Reproduce old E-361 controls with its unchanged script; do not relabel
  their previously tested ranges as fresh holdout.
- Maximum permitted repair: none; fixed issue statement must be preserved.
- Stop: counterexample, new unproved hypothesis required, or no complete
  induction route within 90 minutes of beginning formalization. Do not
  expand to SS budgets or general capacity.

## Evidence log

| Date | Label | Revision / command | Result |
|---|---|---|---|
| 2026-10-01 | `PROVED-PAPER` | E-361 at base revision | Existing excursion proof, no Lean claim yet. |
| 2026-10-01 | `COMPUTED` | `python3 experiments/first_p2_ending_s.py discovery` | All 4,095 words at lengths 0..11; 2,638 have ceiling two; 298 contain P2; first-P2 and D violations 0. |
| 2026-10-01 | `COMPUTED` | `python3 experiments/first_p2_ending_s.py holdout` | All 126,976 words at lengths 12..16; 70,290 have ceiling two; 7,442 contain P2; first-P2 and D violations 0. |
| 2026-10-01 | `PROVED-LEAN` | `lake env lean Recaman/FirstP2EndingS.lean` | Both exact issue statements and derived D invariant, without extra assumptions. |
| 2026-10-01 | `PROVED-LEAN` | `lake env lean docs/data/first_p2_ending_s_20261001/semantic_controls.lean` | Negative controls: removing minimality / raising ceiling to three fails; the nonminimal word's first P2 still ends S. |
| 2026-10-01 | `PROVED-LEAN` | `./scripts/check.sh` | 391 build jobs, 2,553 declarations within permitted axioms; root closure, registry G1-G5, protected labels pass. |

Formalization began at 2026-10-01 15:37:35 JST and the complete route passed
well within the 90-minute gate. Source and pre-run hashes, exact JSON output,
lint/vacuity output and full validation output are in
`docs/data/first_p2_ending_s_20261001/`. The frozen initial card is retained
there, separately from this updated decision record.

## Semantic audit

- Informal and formal quantifiers: both concern all finite abstract words.
- Minimality excludes precisely positive proper prefix lengths, not arbitrary suffixes.
- Ceiling includes index zero and the complete length; there is no moment assumption.
- Counterfactual: AASASSA ends A with ceiling two and is nonminimal;
  AAASSSASASA is minimal and ends A but has ceiling three.
- D positivity is derived from word transitions; no defined unproved Prop
  or occurrence hypothesis will stand in for the mathematical claim.
- Independent semantic review is PASS in E-362-independent, on the unchanged
  source hash. This separate review does not reuse the same-session verdict.
- The formal conclusion matches both directions of the paper's section 3.
  The first-P2 corollary returns leastness for its actual index, not an
  arbitrary P2 witness. Same-session checks are in `statement_audits/E-362.md`.
- The auxiliary recurrence is classified as a wrapper, but the registered
  invariant, main theorem, and least-index corollary are all substantive.
- No mathematical repairs were made. Initial implementation errors were
  standard-library tactic/recursor names and simplification of `take length`;
  they were fixed without changing any mathematical statement.

## Decision

- Complete the bounded kernel-proof unit at `PROVED-LEAN`; submit for review.
- Reason: exact all-length statements, counterfactual controls, G5 audit,
  root integration and full repository check pass.
- Independent review is PASS; issue #74 remains OPEN awaiting PR #77 incorporation.
- E-363 derives the ceiling and E-364 supplies the sharp witnesses in separate
  proof units. Stop this unit; no owner/Hall or general #73 consequence follows.
