# Hypothesis card: all-parameter fixed-SS2 word offset span

- ID: `H-20261001-07`; issue #82.
- Owner: Codex proposer, falsifier and formalizer; separate read-only auditor.
- Created: 2026-10-01; route gate begins 12:15 UTC.
- Status: `PROVED-LEAN` (E-367); E-365 retains its historical paper label.
- Branch: `codex/ss2-word-offset-span-lean`.
- Base: `f6594be0bf04ea1baf6fb460a69c0c6b05dc1379`.

## Exact statement and acceptance

For every k : Nat, C=SAAASSAAASS and V_k=(SA)^k C (AS)^(3*k), with
newest-first A=true=+1 and S=false=-1: P2(V_k); every positive proper
prefix is not P2; ssCount(V_k)=2 (overlapping pairs); NoSAAS(A::V_k);
length(V_k)=8*k+11; its newest S is at one-based offset 1; its true oldest
S, using the existing oldestOffset definition, is at 8*k+11; its maximal
terminal A run, measured by reverse.takeWhile id, has length zero.
Thus oldestOffset(V_k)-1=8*k+10 and for every C0 : Nat an explicit k
has span exceeding C0 while retaining every word property. No cutoff on k or prefixes.

Planned central Lean signatures (namespace SS2WordOffsetSpan):

```lean
theorem word_minimum (k d : Nat) (hd : d < (word k).length) :
    ¬ P2 ((word k).take d)
theorem history_noSAAS (k : Nat) : NoSAAS (true :: word k)
theorem word_oldestOffset (k : Nat) : oldestOffset (word k) = 8*k+11
```

Also classify all proper mass-one prefixes, with moments, and prove the
converse position classification. Acceptance requires substantive all-k
Lean proofs, root/Audit integration, full check, G5 statement quotations,
independent semantic audit and kernel-checked positive/negative controls.

## Why it matters; scope

This closes the Lean obligation for E-365 and stops constant bounds on
marked-to-oldest S span from these word premises alone. The marked newest
S is not an owner. There is no tight Hall family, onto map, periodicity,
Recaman orbit realization or general #73/T6/capacity claim. Protected
E-001/E-067/E-070/E-179 remain unchanged. This is E-122 padding with the
fixed SS2 core, not a new general padding method.

## Provenance and dependency chain

Read repository instructions, README, status/roadmap, current frontier,
glossary/proof map and stopped portfolio; searched the registry and existing
SS2/OneSS modules. Paper: SS2_WORD_OFFSET_SPAN_2026-10-01.md, E-365.
Definitions: LeadingRunSupply.mass/moment/P2; SSFreeSupply.alt/NoSAAS;
OneSSMultiplicity.ssCount; LagSevenDonorCoverage.oldestOffset.
No unverified Prop hypotheses or literature assumptions are imported.

1. Existing append and alternating mass/moment lemmas give P2 and length.
2. Initial SA prefixes have mass <= 0. Core proper mass-one offsets
   3,5,7 have moments 4,3,4, shifted by 3k. Complete-core plus i AS pairs
   gives offset 2k+11+2i and moment 3k-i; odd AS prefixes have mass 2.
3. The weakest new edge is the exhaustive prefix classification for
   arbitrary k and prefix index; positivity before i=3k gives minimality.
4. Existing saasCount_pre_alt/post_alt check all joins; the fixed core
   scan gives NoSAAS, and ssCount padding lemmas give exactly two SS.
5. Actual first/last bits are S, including k=0; connect the last S to the
   existing recursive oldestOffset and maximal terminal-run definition.
6. Choose k=C0 for the unbounded witness, retaining the full conjunction.

## Falsification plan (frozen before implementation)

- Boundary cases k=0 and k=1, both joins, one-based offsets and all prefixes.
- Weakened-history model: abstract words with explicit current A; no
  recurrence or owner-family condition is smuggled in.
- Reuse discovery k=0..10 and holdout k=11..80 from H-20261001-05.
  These are previously used ranges, not fresh or untouched data.
- Rerun the unchanged frozen script and core kernel controls. Its embedded
  historical base remains cbe51b7; record the execution base separately.
- Wrong core AAASSSASASA at k=1 must have earlier P2 at 7; an extra AS
  at k=1 must give final moment -1 and earlier P2 at 19.
- No core search, finite census extension or claim repair. Stop on any
  concrete failure. By 13:45 UTC (90 minutes), either establish the all-k
  prefix and join proof route or record the missing edge and stop. Finite
  certificates, bare arithmetic or wrapper-only proofs cannot pass.

## Evidence log

Frozen execution protocol and exact outputs will be saved under
`data/ss2_word_offset_span_lean_20261001/`. Computation remains COMPUTED.

## Semantic audit and decision

Both directions must preserve the exact prefix ranges and moments.
Check actual oldest S and current A, not an unconstrained marker.
Counterfactual core/padding controls must fail their expected properties.
The construction has no unproved antecedent. General orbit and owner
claims are intentionally outside the formal and informal statements.

Decision: formalize only after the falsifier passes; accept only after
independent audit and repository checks. Stop word-only constant-span
routes; any subsequent owner bound needs a separately falsifiable owner
condition. No issue is described as CLOSED before GitHub closes it.

## Completed evidence and decision (12:23 UTC onward)

- The frozen original script passed discovery k=0..10 and reused holdout
  k=11..80, with exact tables and both expected negative-control failures.
  Original hashes verified; no source/range/claim repair occurred.
- The independent entry audit PASS recomputed 26,811 proper prefixes and
  9,963 mass-one visits. The live wording clarifies that the span exceeds
  C0 at k=C0; the original frozen protocol is preserved.
- Complete all-k source compiled at 12:23 UTC, before the 13:45 route gate:
  exhaustive/converse prefix classification, minimality, both NoSAAS joins,
  true oldest bit, maximal terminal run and full-conjunction witness.
- Final independent source/semantic audit PASS: manual R/W/C/T=5/18/0/0,
  no added assumption, cutoff, vacuous antecedent or owner interpretation.
  Source hash 96c943898e01037fab88dc9df6a65c3966b46e30555995ae2060972bdbc773c2.
- Full repository check: 395 jobs / 2648 permitted-axiom declarations.
  Kernel applications and counterfactual controls are saved alongside the
  reproduction commands. The strongest evidence is the audited all-k proof.
- Decision: accept E-367 and integrate #82. Stop word-only constant-span
  routes. Do not infer actual owner bounds, Hall, T6 or orbit realization;
  a new unit needs a concrete additional owner-family condition.
