# Hypothesis card: first P2 under prefix mass ceiling two

- ID: `H-20261001-02`
- Owner: Codex, separate proposer / falsifier / formalizer / auditor passes
- Created: 2026-10-01
- Status: `CONJECTURED`
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

## Semantic audit

- Informal and formal quantifiers: both concern all finite abstract words.
- Minimality excludes precisely positive proper prefix lengths, not arbitrary suffixes.
- Ceiling includes index zero and the complete length; there is no moment assumption.
- Counterfactual: AASASSA ends A with ceiling two and is nonminimal;
  AAASSSASASA is minimal and ends A but has ceiling three.
- D positivity is derived from word transitions; no defined unproved Prop
  or occurrence hypothesis will stand in for the mathematical claim.
- Independent-session semantic review is a separate remaining acceptance
  condition from the same-session auditor pass; do not imply it occurred.

## Decision

- Continue: falsification, then exact Lean statement if checks pass.
- Reopen only if: a stopped implementation gets a complete missing lemma
  without changing the quantifiers or adding assumptions.
