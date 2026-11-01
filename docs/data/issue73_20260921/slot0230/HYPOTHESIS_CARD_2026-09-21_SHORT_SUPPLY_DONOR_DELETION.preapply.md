# Hypothesis card: short-supply donor deletion is a meaningful restricted corollary

- ID: `H-20260921-01`
- Owner: Sol, slot 2026-09-21 02:30 JST
- Created: 2026-09-21
- Status: `CONJECTURED`
- Research branch: semantic audit of existing unregistered candidate; no new exploration or Lean

## Exact statement

At frozen source hash
`bb12f35acc8e48c584cead52d675e36b034afda22f0f28ecfd245031f70fee85`, audit the
following existing declaration without changing it. The block below is a normalized ASCII rendering,
not a verbatim quote; the actual Unicode source and proof are frozen verbatim in
`docs/data/issue73_20260921/slot0230/raw/target_signature.log`.

```lean
theorem short_supply_donor_deletion (e : Int -> Bool) (p : Nat) (hp : 0 < p)
    (hper : forall x : Int, e (x + p) = e x)
    (U : List Nat) (lag : Nat -> Nat) (hUn : U.Nodup)
    (hUp : forall u in U, u < p)
    (hU_A : forall u in U, e (u : Int) = true)
    (hU_lag : forall u in U, lag u = 3 \/ lag u = 7 \/ lag u = 11)
    (hU_P2 : forall u in U, P2 (past e (u : Int) (lag u)))
    (hU_min : forall u in U, forall d, d < lag u -> 0 < d ->
      not (P2 ((past e (u : Int) (lag u)).take d)))
    (u0 : Nat) (hPdon : P2 (past e (u0 : Int) 11))
    (hmindon : forall d, d < 11 -> 0 < d ->
      not (P2 ((past e (u0 : Int) 11).take d)))
    (hss : Recaman.OneSSMultiplicity.ssCount (past e (u0 : Int) 11) = 2)
    (B : List Nat) (hBU : List.Sublist B U) :
    B.length <= (Recaman.TwoSSTightDisjoint.deletedNeighborhood e p B lag
      (Recaman.TrueOldestGateT6.trueOldestPhase e p u0 11)).length
```

All quantifiers and restrictions are literal. In particular:

- every member of ambient `U`, not merely `B`, is a distinct phase below `p`, is current A,
  and has a minimal P2 window whose lag is exactly 3, 7, or 11;
- `B` is an arbitrary list sublist of that restricted `U`;
- the donor at `u0` is a minimal lag-11 P2 window with `ssCount = 2`;
- neither `u0 in U`, completeness of `U`, positive period mass, actual-orbit provenance, nor a
  full all-lag supply condition is assumed.

`P2 w` unfolds to `mass w = 1 /\ moment w = 0`. `past` is the explicit backward Boolean
window. `ssCount` recursively counts adjacent `SS`. `deletedNeighborhood` is
`(neighborhood ...).filter (fun y => decide (y != s))`; `trueOldestPhase` is the endpoint phase
at `oldestOffset (past e u0 11)`. There is no unproved defined `Prop` hypothesis.

## Why it would matter

- Frontier obligation discharged: none unless the independent audit accepts the exact restricted
  deletion statement as a useful corollary. It does not discharge general Gate T6.
- Stronger than an existing identity or equivalent reformulation because: as a statement it packages
  a Hall-after-deletion inequality for every sublist `B` of a short-only `U`; however its proof is a
  direct composition of the registered tight noncoverage result Q, short Hall, and generic deletion
  lemmas. Under this card's acceptance rule, that composition is not new mathematical input.
- Smallest useful consequence: within the short-only class, deleting the donor's true-oldest phase
  preserves Hall simultaneously for all sublists, including proper sublists and slack sublists.

## Provenance and dependencies

- Definitions used: `LeadingRunSupply.past`, `LeadingRunSupply.P2`,
  `OneSSMultiplicity.ssCount`, `TwoSSTightDisjoint.neighborhood`,
  `TwoSSTightDisjoint.deletedNeighborhood`, `TrueOldestGateT6.trueOldestPhase`.
- Lean theorems used: `ShortTightDonorAvoidance.short_window_hall`,
  `ShortTightDonorAvoidance.short_tight_avoids_ss2_donor` (registered Q in E-360),
  `TwoSSAvoidTight.deleted_hall_of_not_mem`, and
  `TwoSSAvoidTight.deleted_hall_of_slack`.
- Informal dependency chain: restrict all `U` hypotheses to `B`; obtain short Hall on `B`; if
  `|N(B)| = |B|`, Q gives true-oldest nonmembership and generic nonmembership deletion gives the
  conclusion; otherwise Hall plus disequality gives strict slack, and generic slack deletion gives
  the conclusion.
- Unverified mathematical assumptions: none hidden in a defined `Prop`; the independent semantic
  audit of this exact candidate is still pending.
- Literature source or analogy: Hall deletion under tight-set avoidance; no new external source.

## Falsification plan

- Small and boundary cases: empty `B`; p8 `SSAASAAA` tight witness; the same p8 word with full short
  `U = [3,7]` and donor-containing slack `B = [3]` / `[3,7]`; p11 `AAAASASASSS`
  slack witness; proper-sublist quantification; phase wrapping; duplicate `U` rejected by `hUn`.
- Adversarial or weakened-history model: E-240 pure-AAS countermodel; p12 SS=3 control; false fixed
  offset-11 control; omit all-U short restriction; distinguish arbitrary periodic words from actual
  Recaman orbits.
- Discovery range: none. Only fixed known controls are replayed.
- Frozen holdout range: none. The p32/33 seed-2026091801 data are already used and are excluded.
- Maximum one permitted repair: no repair. The theorem source is frozen for this audit.
- Stop condition: stop and return `CONJECTURED`/unregistered if the exact statement is false,
  vacuous, assumes its conclusion, needs a source edit, or is described as general T6/new mathematical
  input. A direct Q-plus-deletion composition is recorded as a restricted corollary, not a new input.

## Evidence log

| Date | Label | Revision / command | Result |
|---|---|---|---|
| 2026-09-21 | `OBSERVED` | HEAD `08c08565c743f39350c9b959e1df7d30aa1cae5d`; `python3 scripts/report_vacuity.py --all Recaman/ShortTightDonorAvoidance.lean` | 0/21 flagged; heuristic only |
| 2026-09-21 | `OBSERVED` | same source; `python3 scripts/harness_gate.py --lint-module Recaman/ShortTightDonorAvoidance.lean` | candidate reported substantive; heuristic only |
| 2026-09-21 | `OBSERVED` | frozen replay and raw output in `docs/data/issue73_20260921/slot0230/control_replay.py` and `raw/control_replay.stdout.log` | nonempty tight and slack antecedents exist; SS=3 weakening fails as expected |
| 2026-09-21 | `OBSERVED` | line-by-line proof inspection at source lines 363-391 | exact direct composition chain identified; no new mathematical input |

## Semantic audit

- Informal statement implies formal statement: yes only when "short supply list" explicitly means all
  of `U` consists of minimal P2 lag-3/7/11 current-A phases and `B` ranges over list sublists.
- Formal statement implies intended consequence: it implies Hall survival after deleting the true
  oldest phase for every such `B`. It does not imply deletability from an unrestricted complete
  all-lag supply set; a complete U would be covered only if every member met the all-short hypotheses.
- Counterfactual examples that should make the statement false: dropping donor `ssCount = 2` is
  refuted by p12 `AAAASAAASSSS`, `B = [2,5,7]`, where the true-oldest phase 4 is in the tight
  neighborhood and deletion leaves size 2 for a size-3 set.
- Could the theorem be proved from weaker or vacuous assumptions?: some presentation hypotheses may
  be stronger than logically necessary, but the exact proof is not `H -> H` and the conclusion is not
  an input. The result is nevertheless a direct corollary: Q is the only donor-specific mathematical
  input; generic tight/slack deletion completes it.
- Are reachability, freshness, time order, or actual-orbit provenance accidentally omitted?: they are
  absent by design. Therefore no actual-orbit, E-070, E-067, full-supply, arbitrary-lag, or general
  Gate T6 conclusion is licensed.

## Decision

- Continue / formalize / refute / stop: stop new formalization. Send the frozen packet for independent
  audit. Keep status `CONJECTURED` during review; the final evidence label must be decided after the
  independent auditor confirms whether this already checked exact corollary should be recorded as
  `PROVED-LEAN` without a new registry row or new mathematical-input claim.
- Reason: the candidate is meaningful and nonvacuous within its severe short-only scope, but it is a
  direct corollary of Q plus existing deletion lemmas and is not new mathematical input.
- Reopen only if: the independent auditor identifies a mismatch in the exact quantifiers, definition
  expansion, fixed-control replay, or dependency reduction.
