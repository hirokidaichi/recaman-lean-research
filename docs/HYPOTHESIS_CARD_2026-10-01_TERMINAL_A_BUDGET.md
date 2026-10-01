# Hypothesis card: terminal A budget of a minimal P2 word

- ID: `H-20261001-01`
- Owner: Codex, separate proposer / falsifier / formalizer / auditor passes in one session
- Created: 2026-10-01 JST
- Status: `PROVED-PAPER` (final decision below; not Lean-checked)
- Initial status: `CONJECTURED` (frozen before computation)
- Research branch: `codex/p2-terminal-tail-bound`
- Base revision: `08c08565c743f39350c9b959e1df7d30aa1cae5d`

## Exact statement

Let W be ANY finite word in A=+1 and S=-1, ordered newest first. Write
`H(j)=sum_{i=1}^j W_i`, `M(j)=sum_{i=1}^j i W_i`. P2 means
`H(|W|)=1` and `M(|W|)=0`; minimal means no nonempty proper prefix is P2.
Let q be the number of adjacent SS pairs, counted with overlap, and t the
length of the maximal terminal A run (the old end of the backward window).

Question: does minimal P2 and t>0 imply **t<q**, at every length?
The acceptance target includes sharpness: for each q>=2 there is a minimal
P2 word with exactly q SS pairs and t=q-1. At q=0,1 the maximum should be t=0.
No periodicity, NoSAAS, current sign, owner map, Hall condition, or actual
Recaman reachability is assumed. There is no length or time cutoff.

## Why it would matter

This constrains the old A-tail coordinate that the 9/24 handoff identified
as necessary for a future owner-offset argument. It rules out discarding
that coordinate: its maximum grows with q even among minimal words.
It is a local word result, not the missing M1/M2 owner-offset inequality,
and does not reopen the stopped finite-lag certificate route or prove T6.
No new wrapper or equivalence of coverage is proposed.

## Provenance and dependencies

- Committed definitions: `LeadingRunSupply.mass`, `moment`, `P2`;
  `OneSSMultiplicity.ssCount`; `TwoSSEndpoint.hasP2Prefix`.
- Existing suffix bound: `LowSSEndpoint.mass_ending_A`.
- E-128 permits shortening low-SS windows; E-130 forbids extending that
  normalization to all SS<=2 windows. E-169 bounds the *new* A end instead.
- Searched `Recaman/`, hypothesis cards, glossary, proof map, portfolio,
  and the 9/24 handoff for terminal/trailing A, prefix mass, and owner offsets.
- Uncommitted H-05 code and its unreviewed downstream assertions are not
  dependencies. No existing uncommitted files will be included in this commit.
- No unverified mathematical assumptions or external literature inputs.

## Falsification plan (frozen)

- Small cases: independent literal binary enumeration for all lengths 0..11;
  compare the complete P2 sets with the mass/moment-filtered generator.
- Discovery: all P2 words of lengths 3,7,11,15,19, including nonminimal ones.
- Holdout: all P2 words of length 23; disjoint from discovery **for this
  terminal-tail claim**, not asserted to be unseen by all past repository work.
- Test the proposed intermediary: if every prefix mass is at most 2,
  a P2 word has an S-ended P2 prefix. For A-ended words it must be proper.
- Weakened-history model: arbitrary words; no actual-orbit conditions at all.
- Negative controls: remove minimality (`AASASSA`), mass=1 (`ASSA`), or
  moment=0 (`A`). The first should violate the strict bound while satisfying P2.
- Proposed sharp witnesses, fixed before running: q=0 `AAS`, q=1 `SAAAASS`,
  q=2 `AAASSSASASA`; for q>=3, with n=q*q-2*q-2,
  `W_q = AAA S (SA)^n S^q A^(q-1)`.
- Witness discovery q=0..10; witness holdout q=11..40.
- Persist source/card hashes before the first run. Save exact JSON output.
- Repairs: none to the mathematical claim. A counterexample ends it;
  implementation defects must be reported, not hidden by replacing logs.
- Stop after this one unit: no longer-lag census, owner-family reconstruction,
  or new general-capacity assertion. If a complete proof is unavailable,
  retain `CONJECTURED` plus finite evidence and identify the missing lemma.

## Informal dependency chain (before implementation)

Suffix S/A pairing bounds suffix mass below by t-1-q. With total mass=1,
t>=q and t>0 bound all prefix masses by 2. At consecutive visits to mass 1,
the moment decreases by exactly 1 on an upper AS excursion, and strictly
increases on a lower excursion. Therefore the first zero moment at mass 1
must end S. This excludes a minimal A-ended word when t>=q.
The weakest new edge is the prefix-mass-ceiling-2 / first-P2-ending-S lemma.

## Evidence log

Pending the frozen runs and paper audit. No Lean file has been created.

## Semantic audit

Pending. Explicitly check both directions of the old-tail coordinate
interpretation, t=0, overlapping SSS, nonminimal controls, and whether sharp
witnesses are only abstract words. No claim about actual orbits is intended.

## Decision

Pending the bounded unit. Exact commands, final status, limits, and next
decision will be recorded below without changing the frozen protocol above.


## Final decision — 2026-10-01

- Status: **PROVED-PAPER**, registered as E-361. No Lean formalization or
  independent-agent/human review is claimed.
- Full proof and semantic audit: [terminal A budget](TERMINAL_A_BUDGET_2026-10-01.md).
- COMPUTED discovery: 3,021 P2 words, 1,811 minimal, 729 minimal A-ended;
  COMPUTED holdout L=23: 30,554 P2 words, 18,556 minimal, 7,895 minimal A-ended.
  Strict bound, non-strict bound, and ceiling-two prefix lemma violations: all 0.
- Literal enumeration of all 4,095 words at L<=11 agrees on all 34 P2 words.
  Sharp witnesses q=0..40 pass; the universal family is proved algebraically,
  not inferred from these 41 tests. The three weakened controls fail as planned.
- Exact commands/logs, source revision and pre-run hashes are in the proof
  document and data directory. The original card is preserved as protocol.frozen.md.
- Informal/formal word conventions agree: t=L-r at the true oldest S. q=0 and
  t=0 are handled; SS pairs overlap. No reachability assumption was silently
  dropped: arbitrary words were the domain from the start.
- Accepted: all-length proof plus all-q sharpness. There were no repairs.
  Stop this unit here. The next distinct unit may formalize the first-P2 lemma;
  owner-offset delta remains uncontrolled. Do not treat this as reopening or
  solving the general-lag tight-family/T6 route.
