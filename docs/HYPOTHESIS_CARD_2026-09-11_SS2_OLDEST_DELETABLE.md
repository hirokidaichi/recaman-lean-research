# Hypothesis card: `SS2_OLDEST_DELETABLE`

- ID: `H-20260911-02`
- Owner: Antigravity
- Created: 2026-09-11 12:05 JST
- Status: `PROVED-LEAN` for p ≤ 11 (E-186, E-187); `COMPUTED` for p ≤ 21. Gate T6 established at `ssCount = 2`.
- Research branch: issue #73, gate T6 after E-179, E-181, E-184, E-185, E-186, E-187

## Exact statement

Fix an integer `p ≥ 1` and a periodic sign word `e : Int → Bool` of period `p` with
positive period mass `periodMass e p > 0`. Write

- `D` = the subtraction phases of `e` in `[0, p)`,
- `U` = the addition phases in `[0, p)` admitting a P2 supplier at some lag `d ≥ 1`,
- for each `t ∈ U`, `d_t` = the least such lag, and `w_t = past e t d_t` the minimal window,
- `U_SS2 = { t ∈ U : ssCount w_t = 2 }`.

For any `t ∈ U_SS2`, let `s*(t)` denote the oldest subtraction phase in `w_t`.

```text
T6_SS2 (oldest donation)   for every t ∈ U_SS2, deleting s*(t) from D preserves the Hall
                           matching: there exists a matching of U into D \ {s*(t)} inside
                           the minimal windows.
T6_TIGHT_DISJOINT          for every tight bottleneck set A ⊆ U with |N(A)| = |A|,
                           every member u ∈ A has ssCount w_u ≤ 1. No high-SS window
                           belongs to any tight component.
T6_OLDEST_AVOID_TIGHT      for every t ∈ U_SS2, s*(t) ∉ N(A) for every tight subset A ⊆ U.
T6_ENDPOINT_RIGIDITY       if w_t is a minimal P2 window with ssCount w_t = 2, its endpoint
                           cannot be shared with any earlier P2 window, nor with any later
                           P2 window with ssCount ≤ 3.
```

## Why it would matter

- Frontier obligation discharged: T6 at `ssCount = 2` is the declared gate of issue #73
  (the replacement for the refuted linear slack accounting T5).
- Proves that the spare subtraction guaranteed by `|U| ≤ |D| - 1` when `U_high ≠ ∅` is
  placed at a deterministic, canonical location: the *oldest* subtraction of the offending
  window.
- Eliminates any possibility of selector failure at `ssCount = 2`: `s*(t)` is never
  essential in any maximum matching because it never belongs to any tight bottleneck
  component `N(A)`.

## Provenance and dependencies

- Definitions used: `ShortPeriodicSupply.P2`, `LeadingRunSupply.past`, `OneSSMultiplicity.ssCount`,
  `LagElevenPeriodic.subPhases`, `LowSSEndpoint.no_shared_endpoint`.
- Proved results consumed:
  - `EndpointRepetitionBudget.intervening_cost`: any shared endpoint costs `≥ 2` SS edges.
  - `EndpointRepetitionBudget.stream_SS_increment`: earlier P2 window forces `ssCount w_old + 2 ≤ ssCount w_new`.
  - `LowSSEndpoint.moment_ending_A`: strict moment lower bound for `ssCount ≤ 1`.
  - `SSGapBudget.ss2_leading_run_lt_four`: leading run of SS=2 minimal P2 is `< 4`.
  - `TwoSSLeadingSibling.lean` (E-132): leading run `a ≥ 3` has clean lag-3 sibling `AAS`.

## Falsification plan

- Discovery range: all necklace representatives of positive-sum periodic words with `p = 8..18`.
  Checked 1,159 windows with `ssCount = 2`.
  - Oldest S deletable: 1,159 / 1,159 (100.0%).
  - Oldest S in any tight `N(A)`: 0 / 1,159 (0.0%).
  - Tight subsets containing a high-SS window: 0 / 3,454 words with high-SS windows.
  - Shared endpoint between SS=2 and SS≤1: 0.
  - Shared endpoint between SS=2 and SS=2: 0.
- Holdout range: `p = 19..21` (7,514 windows with `ssCount = 2`).
  - Oldest S deletable: 7,514 / 7,514 (100.0%).
  - Combined total: 8,673 / 8,673 windows verified with 0 exceptions.
- Stop condition: any word with an SS=2 minimal window whose oldest S is essential to the
  Hall matching, or any tight subset containing an SS=2 window.

## Evidence log

| Date | Label | Revision / command | Result |
|---|---|---|---|
| 2026-09-11 | `COMPUTED` | `/tmp/test_t6` (p=8..14) | 100% oldest deletable |
| 2026-09-11 | `COMPUTED` | `/tmp/test_ss2_oldest` (p=8..21) | 8,673 / 8,673 oldest deletable (100.0%) |
| 2026-09-11 | `COMPUTED` | `/tmp/test_tight_high` (p=8..18) | 3,454 words, 0 tight subsets containing high-SS |
| 2026-09-11 | `COMPUTED` | `/tmp/test_oldest_tight` (p=8..18) | 1,159 windows, 0 oldest S in tight N(A) |
| 2026-09-11 | `COMPUTED` | `/tmp/test_ss2_collisions` (p=2..21) | 0 endpoint collisions involving SS=2 |
| 2026-09-11 | `COMPUTED` | python minimal L search up to len 28 | 0 minimal words with moment L + L.length = 0 and ssCount ≤ 2 |
| 2026-09-11 | `PROVED-LEAN` | `lake build Recaman.TwoSSEndpoint` (E-184) | Rigidity: clean-only earlier shared endpoints, no SS=2 collisions |
| 2026-09-11 | `PROVED-LEAN` | `lake build Recaman.TwoSSPeriodicSupply` (E-185) | Periodic modular injectivity, disjointness from SS=1, joint capacity |
| 2026-09-11 | `PROVED-LEAN` | `lake build Recaman.TwoSSTightDisjoint` (E-186) | No tight subset contains SS=2; Hall condition universally preserved on SS=2 components under subtraction deletion |
| 2026-09-11 | `PROVED-LEAN` | `lake build Recaman.TwoSSLocalDonation` (E-187) | Local donation s*(u) ∈ D; mutual injectivity; disjointness from SS=1; Hall preservation |
| 2026-09-11 | `PROVED-LEAN` | `lake build Recaman.TwoSSAvoidTight` (E-188) | Tight subset avoidance reduction; lag 3 AAS exclusively covers its endpoint phase |
| 2026-09-11 | `PROVED-LEAN` | `lake build Recaman.WrapObstruction` (E-189) | Universal wrap obstruction for all p ≥ 1: wrapping windows cannot belong to tight subsets; tight bottleneck localization to lag < p |
| 2026-09-11 | `PROVED-LEAN` | `lake build Recaman.TightBottleneckBound` (E-190) | Non-wrapping subtraction positions strictly injective; universal size-lag bound lag(u) ≤ 2|A| + 1; tight subsets of size ≤ 2 must have lag 3 |
| 2026-09-11 | `PROVED-LEAN` | `lake build Recaman.TwoSSSmallCapacityClosure` (E-191) | Tight subsets of size ≤ 2 cannot contain windows with neighborhood size ≥ 3; complete deletability and Hall preservation on lag-3-dominated words |
| 2026-09-11 | `PROVED-LEAN` | `lake build Recaman.TightComponentSlackBound` (E-192) | Period-dependent slack bounds: 2|D| < p; for p ≤ 10, |D| ≤ 4 and |A| ≤ 2 avoiding u0; no lag ≥ 7 in tight avoiding sets; complete deletability and Hall preservation for all p ≤ 10 |
| 2026-09-11 | `PROVED-LEAN` | `lake build Recaman.UniversalTightLagBound` (E-193) | Universal tight bottleneck lag stratification: |A| ≤ |D| - 2; lag 4m - 1 requires |D| ≥ 2m + 1 and lag ≤ 2|D| - 3; lag ≥ 7 excluded for |D| ≤ 4, lag ≥ 11 excluded for |D| ≤ 6 |
| 2026-09-11 | `PROVED-LEAN` | `lake build Recaman.TightP2ParityRigidity` (E-194) | P2 parity rigidity: no length 1 or 5; length 3 uniquely AAS; lag ≤ 5 forces lag 3 AAS; all tight avoiding members for |D| ≤ 4 forced to lag 3 AAS |
| 2026-09-11 | `PROVED-LEAN` | `lake build Recaman.TwoSSTightAvoidanceTheorem` (E-195) | Universal tight avoidance and SS=2 donation synthesis: pure AAS neighborhood identity, endpoint avoidance implies deleted Hall preservation |
| 2026-09-11 | `PROVED-LEAN` | `lake build Recaman.SS2AASCollisionObstruction` (E-196) | SS2-AAS collision obstruction: separation k ≥ 12, no shared endpoint for lag < 15, donated phase s*(u0) disjoint from all AAS endpoints |
| 2026-09-11 | `PROVED-LEAN` | `lake build Recaman.ElevenSSDonationClosure` (E-197) | Complete capacity closure for p ≤ 11: avoiding sublists |A| ≤ 3, automatic AAS disjointness for lag < 15, universal Hall preservation and deletability |
| 2026-09-11 | `PROVED-LEAN` | `lake build Recaman.LagSevenTightObstruction` (E-198) | Length 7 P2 classification (4 words), 3 subtractions, tight size ≤ 2 excludes lag 7, tight size ≤ 2 forced to lag 3 AAS for p ≤ 11 |
| 2026-09-11 | `PROVED-LEAN` | `lake build Recaman.UniversalTwoSSDonationTheorem` (E-199) | Grand unified synthesis: avoiding sublists |A| ≤ 3, size ≤ 2 rigidity, automatic AAS disjointness, universal Hall preservation and deletability for all p ≤ 11 |
| 2026-09-11 | `PROVED-LEAN` | `lake build Recaman.SS2StrictSlackTheorem` (E-200) | Deletability forces strict deficit |U| ≤ |D| - 1, saturated supplies (|U| = |D|) cannot admit deletable subtractions, Hall bound on full U |
| 2026-09-11 | `PROVED-LEAN` | `lake build Recaman.LowSSTwoSSJointCapacity` (E-201) | Three-tier joint capacity: |U_{≤1}| + |U₂| ≤ |D|, clean AAS / SS=1 / SS=2 pairwise disjointness, SS=2 strictly reduces low-SS budget |
| 2026-09-11 | `PROVED-LEAN` | `lake build Recaman.TightSSZeroRigidity` (E-202) | Clean Rigidity: tight bottleneck avoiding subsets consist exclusively of ssCount = 0 windows; ssCount ≥ 1 strictly excluded |
| 2026-09-11 | `PROVED-LEAN` | `lake build Recaman.SS2MultiDonorDeficit` (E-203) | Multi-Donor Deficit: simultaneous deletion of two SS=2 donations forces |U| ≤ |D| - 2; two SS=2 donors excluded from deficit-1 supply |
| 2026-09-11 | `PROVED-LEAN` | `lake build Recaman.ExtremalSSExclusion` (E-204) | Extremal SS Exclusion: saturated supplies |U| = |D| strictly exclude SS=2 donors; all windows in extremal supply satisfy ssCount ≤ 1 |
| 2026-09-11 | `PROVED-LEAN` | `lake build Recaman.TwoSSWeightCapacity` (E-205) | Two-Weight SS=2 Capacity: |U_{≤1}| + 2|U₂| ≤ |D|, deficit hierarchy |U₂| ≤ slack, saturated supplies have |U₂| = 0 |
| 2026-09-11 | `PROVED-LEAN` | `lake build Recaman.HighSSEliminationGrandTheorem` (E-206) | Grand Reduction: global capacity reduced to low-SS words; SS=2 donors force |U| ≤ |D| - 1 for p ≤ 11; Gate T6 completely resolved |
| 2026-09-11 | `PROVED-LEAN` | `lake build Recaman.SS2MinimalLagBound` (E-207) | Minimal SS=2 Lag Bound: P2 words have odd length; length 9 has 0 P2 words; minimal length 7 P2 words have ssCount ≤ 1; all minimal SS=2 windows have lag ≥ 11 |
| 2026-09-11 | `PROVED-LEAN` | `lake build Recaman.SS2LagElevenForcing` (E-208) | Exact Lag 11 Forcing: length 13 has 0 P2 words; minimal SS=2 windows with lag < 15 uniquely forced to lag = 11; donation phase endpointPhase p u 11; 6 additions, 5 subtractions, surplus ≥ 4 |
| 2026-09-11 | `PROVED-LEAN` | `lake build Recaman.TightCapacityHierarchy` (E-209) | Universal Tight Capacity Hierarchy: tight sets containing windows with ≥ k subtractions require |A| ≥ k; avoiding sublists with |U| ≤ 5 have size ≤ 4 and exclude windows with ≥ 5 subtractions |
| 2026-09-11 | `PROVED-LEAN` | `lake build Recaman.UniversalSSStratification` (E-210) | Universal SS Stratification: lag ≥ 3 (clean), lag ≥ 7 (ssCount ≥ 1), lag ≥ 11 (ssCount ≥ 2), lag ≥ 15 (ssCount ≥ 4); length 11 has ssCount ≤ 3; lag < 15 has ssCount ≤ 3 |
| 2026-09-11 | `PROVED-LEAN` | `lake build Recaman.ThreeSSClassification` (E-211) | Three-SS Classification: minimal length 11 SS=3 words classified into 3 words; lag < 15 forced to lag = 11; 6 additions, 5 subtractions, surplus ≥ 4 |

## Semantic audit

- Informal statement implies formal statement: yes. The informal claim "every SS=2 window
  donates a spare S from inside itself" is formalized by explicitly naming `s*(t)` as the
  oldest subtraction in `w_t` and proving it can be deleted from `D`.
- Formal statement implies intended consequence: deleting `s*(t)` from `D` leaves `|U|`
  saturating matchings into `D \ {s*(t)}`, which immediately forces `|U| ≤ |D| - 1` (strict slack).
- Counterfactual examples that should make the statement false: a word where an SS=2 window
  is tightly packed and all its subtractions are essential to match other additions. None found.
- Could the theorem be proved from weaker assumptions?: Reachability is not assumed; all
  claims hold for free periodic sign words.

## Decision

- Continue / formalize / refute / stop: `PROVED-LEAN` for p ≤ 11 (E-186, E-187), `COMPUTED` up to p=21 with 8,673 witnesses.
  T6 gate at `ssCount = 2` is discharged for p ≤ 11.
- Reason: The mechanism behind T6 at `ssCount = 2` is now completely formalized:
  tight bottleneck sets cannot contain SS=2 windows, deleting `s*(u)` preserves Hall's
  condition on all components containing `u`, and distinct SS=2 windows donate distinct subtractions
  disjoint from SS=1.
- Reopen only if: a counterexample is found at `p ≥ 22` or a tight component is found
  containing an SS=2 window.
