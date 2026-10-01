# Hypothesis card: explicit terminal-A sharp words

- ID: `H-20261001-04`
- Owner: Codex, separate proposer / falsifier / formalizer / auditor passes
- Created: 2026-10-01
- Status: `PROVED-LEAN` (E-364); independent semantic review PASS. See [E-364-independent](statement_audits/E-364-independent.md). Issue #76 remains OPEN awaiting PR incorporation.
- Base: `cbe51b7`, isolated worktree; E-364 checked free against primary dirty registry.
- Bounded question: issue #76, E-361 section 5's fixed construction, all q.

## Exact statement and acceptance

For every natural q the explicit newest-first true/false word Wq is
minimal P2, has overlapping ssCount q, and
`(Wq.reverse.takeWhile id).length = q-1` (saturated Nat subtraction).

```text
W0=AAS, W1=SAAAASS, W2=AAASSSASASA.
For q>=3, n=q*q-2*q-2 >=1,
Wq = [A,A,A,S] ++ alt false n ++ replicate q S ++ replicate (q-1) A.
```

Acceptance: exact construction theorem for all q; explicit proper-prefix
mass-one classification for q>=3; all-q existence corollary; semantic
audit, root/axiom integration, harness lint and full check. No cutoff or
minimality assumption supplied by another theorem.

## Dependency chain before implementation

- Reuse LeadingRunSupply mass/moment/P2 and append/replicate identities;
  SSFreeSupply.alt false n is exactly (SA)^n; OneSSMultiplicity.alt_length,
  ssCount_pre_alt, alt_mass, alt_S_moment.
- Search covered these modules, current registry, paper and stopped portfolio.
  No new invariant or orbit definition is proposed.
- Prove mass and moment formulas for constant runs and partial SA blocks.
- Weakest useful new lemma: all proper mass-one prefixes of the explicit
  word occur only at j=1 (moment 1), j=2*i+3 with 1<=i<=n
  (moment -i-2), or j=2*n+5 (moment -n-3).
- Split take into AAA S, SA block, S^q, A^(q-1). In the last run mass
  returns to one only at the complete length. Prove the classification
  directly and infer minimality from each listed nonzero moment.
- Compute mass=1 and twice moment; enforce n+2q+2=q*q using q>=3
  with a justified Nat subtraction/cast. SS junctions: one at initial
  S|SA, q-1 inside S^q, none elsewhere. Maximum A suffix=q-1.
- Construct q=0,1,2 separately with kernel finite controls.
- This module must not import TerminalASSBound or FirstP2EndingS. The
  upper bound is not used to prove minimality; no circularity.

## Falsifier before formalization

- Reproduce the unchanged old witness protocol q=0..10 discovery and
  q=11..40 holdout. These are reused holdout, not new discovery-free data.
- Independently classify every proper mass-one prefix of these words;
  check the exact positions and moments, including q=3,n=1,length11,t=2.
- Test invalid extension q=0,1,2 of the general formula separately;
  check n=0 does not have the intended initial SS junction.
- Abstract words have no history condition to weaken. No canonical or
  seeded orbit occurrence is claimed.
- Freeze this card and script digest before runs, recording base and output.

## Stop and scope

Stop on a counterexample or added unproved hypothesis. If the all-proper-
prefix classification route is not confirmed within the first 90 minutes
of formalization, retain only the partial obligation and mark STOPPED;
mass/moment arithmetic alone is not registered as a research result.
No replacement-construction search, orbit realization, owner delta,
Hall, general #73, or protected label change is authorized by this unit.

## Evidence / audit / decision

E-361 is PROVED-PAPER for this component. The prior upper bound E-363 is
available but is intentionally not a dependency. Same-session review must
check both directions of the explicit word and maximum-tail meaning, and
exclude every proper P2 prefix, not just selected positions. Separate-session
semantic review is now PASS in E-364-independent; issue #76 remains OPEN
awaiting PR incorporation.
The exact construction is formalized without a quantifier repair.
Formalization began by 08:50:30 UTC. The complete classification and its
reverse direction compiled by 08:53:30 UTC, within the 90-minute gate.
All-q P2/count/tail/minimality and existence now compile.
Initial Lean failures were rewrite ordering, Nat multiplication association,
and simp normalization; no mathematical counterexample occurred.

Frozen protocol/source: data/terminal_a_sharp_words_20261001.
The initial classification probe was OBSERVED. The saved
experiments/terminal_a_sharp_words.py was hashed before a reproducibility
rerun; falsification.json is COMPUTED. q=0..10/q=11..40 reuse the E-361
discovery/holdout. q=3..40 proper mass-one classification matches exactly;
q=3 positions [1,5,7] have moments [1,-3,-4]. Pushing the general formula
into q=0/1/2 fails P2, so those cases remain separate.

Audit: exact signatures in statement_audits/E-364.md, no defined Prop or
minimality hypothesis. Independent construction imports only
OneSSMultiplicity. Same-session R/W/C/T=11/20/0/0. Lint 25/31 substantive;
vacuity flags the two acknowledged arithmetic helpers, neither registered.
Independent review is PASS on the unchanged source hash, including trust-0
controls and full check (393 jobs / 2600 axiom reports). The auditor corrected
an n=0 count guess: merged S runs keep SS=q, while wrong n fails P2 by moment.
Stop this construction unit here; await PR #80 incorporation.
No owner-family or orbit consequence is inferred.
