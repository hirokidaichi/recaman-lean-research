# Hypothesis card: `SS2_OLDEST_DELETABLE`

- ID: `H-20260911-02`
- Owner: Antigravity
- Created: 2026-09-11 12:05 JST
- Status: `COMPUTED` (E-183 candidate). The gate T6 (E-179) instantiated at `ssCount = 2`.
- Research branch: issue #73, gate T6 after E-179 and E-181

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

- Continue / formalize / refute / stop: `COMPUTED` verified up to p=21 with 8,673 witnesses.
  Formalize the endpoint rigidity lemmas (`ss2_shared_endpoint_clean` and
  `stream_ss2_earlier_clean`) in Lean, connecting to `EndpointRepetitionBudget`.
- Reason: The mechanism behind T6 at `ssCount = 2` is now completely transparent:
  tight bottleneck sets are confined to `U_low`, and `s*(t)` never intersects `N(A)` for
  any tight set.
- Reopen only if: a counterexample is found at `p ≥ 22` or a tight component is found
  containing an SS=2 window.
