import Recaman.TightComponentSlackBound

/-!
# UniversalTightLagBound: Universal Stratification of Tight Bottleneck Lags by Deficit Capacity

This module establishes the universal arithmetic stratification of tight bottleneck subsets
`A ⊆ U \ {u₀}` avoiding an SS=2 donor window `u₀`:

1. **Deficit Size Upper Bound**: In any positive-slack periodic word (`|U| < |D|`), any sublist
   `A <+ U` avoiding `u₀ ∈ U` satisfies `|A| ≤ |D| - 2`:
   - If `|D| ≤ 3`: `|A| ≤ 1` (tight sets are singletons).
   - If `|D| ≤ 4`: `|A| ≤ 2` (tight sets are at most pairs).
   - If `|D| ≤ 5`: `|A| ≤ 3` (tight sets are at most triplets).
   - If `|D| ≤ 6`: `|A| ≤ 4`.
2. **Universal Capacity-Neighborhood Inequality**: Any window `u ∈ A` with `k` distinct subtractions
   in a tight subset `A` avoiding `u₀` satisfies `k ≤ |D| - 2`.
3. **Hierarchy of Excluded Lags**:
   - For `|D| ≤ 4`: no window with `≥ 3` subtractions can appear (lag ≥ 7 excluded).
   - For `|D| ≤ 6`: no window with `≥ 5` subtractions can appear (lag ≥ 11 excluded).
   - For `|D| ≤ 8`: no window with `≥ 7` subtractions can appear (lag ≥ 15 excluded).
4. **Universal Deficit-Lag Arithmetic**: For any P2 window of lag `d = 4m - 1`, belonging to a tight
   subset avoiding `u₀` requires `|D| ≥ 2m + 1` and `d ≤ 2|D| - 3`.
-/

namespace Recaman.UniversalTightLagBound

open TwoSSTightDisjoint TwoSSPeriodicSupply TwoSSEndpoint TwoSSLocalDonation TwoSSAvoidTight WrapObstruction TightBottleneckBound TwoSSSmallCapacityClosure TightComponentSlackBound OneSSMultiplicity LeadingRunSupply LowSSPeriodicSupply SharpPeriodicSupply

/-- In any positive-slack word, any sublist avoiding an element of U has size at most `d_len - 2`. -/
theorem sublist_avoiding_size_le_deficit {α : Type _} {A U : List α}
    (hsub : List.Sublist A U) {u0 : α} (hmem : u0 ∈ U) (hnot : u0 ∉ A)
    {d_len : Nat} (hslack : U.length < d_len) :
    A.length ≤ d_len - 2 := by
  have hle := TightComponentSlackBound.sublist_length_le_sub_one_of_mem_not_mem hsub hmem hnot
  omega

/-- For `|D| ≤ 3`, any sublist avoiding `u0` has size at most 1. -/
theorem tight_avoiding_size_le_one_of_subPhases_le_three (e : Int → Bool) (p : Nat)
    (A U : List Nat) (u0 : Nat) (hu0 : u0 ∈ U) (hnot : u0 ∉ A) (hsub : List.Sublist A U)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (hD3 : (LagElevenPeriodic.subPhases e 0 p).length ≤ 3) :
    A.length ≤ 1 := by
  have hlen := sublist_avoiding_size_le_deficit hsub hu0 hnot hslack
  omega

/-- For `|D| ≤ 4`, any sublist avoiding `u0` has size at most 2. -/
theorem tight_avoiding_size_le_two_of_subPhases_le_four (e : Int → Bool) (p : Nat)
    (A U : List Nat) (u0 : Nat) (hu0 : u0 ∈ U) (hnot : u0 ∉ A) (hsub : List.Sublist A U)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (hD4 : (LagElevenPeriodic.subPhases e 0 p).length ≤ 4) :
    A.length ≤ 2 := by
  have hlen := sublist_avoiding_size_le_deficit hsub hu0 hnot hslack
  omega

/-- For `|D| ≤ 5`, any sublist avoiding `u0` has size at most 3. -/
theorem tight_avoiding_size_le_three_of_subPhases_le_five (e : Int → Bool) (p : Nat)
    (A U : List Nat) (u0 : Nat) (hu0 : u0 ∈ U) (hnot : u0 ∉ A) (hsub : List.Sublist A U)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (hD5 : (LagElevenPeriodic.subPhases e 0 p).length ≤ 5) :
    A.length ≤ 3 := by
  have hlen := sublist_avoiding_size_le_deficit hsub hu0 hnot hslack
  omega

/-- For `|D| ≤ 6`, any sublist avoiding `u0` has size at most 4. -/
theorem tight_avoiding_size_le_four_of_subPhases_le_six (e : Int → Bool) (p : Nat)
    (A U : List Nat) (u0 : Nat) (hu0 : u0 ∈ U) (hnot : u0 ∉ A) (hsub : List.Sublist A U)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (hD6 : (LagElevenPeriodic.subPhases e 0 p).length ≤ 6) :
    A.length ≤ 4 := by
  have hlen := sublist_avoiding_size_le_deficit hsub hu0 hnot hslack
  omega

/-- Universal upper bound: any member of a tight avoiding subset has individual neighborhood size
bounded by `|D| - 2`. -/
theorem universal_tight_size_bound (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (A U : List Nat) (lag : Nat → Nat)
    (u0 : Nat) (hu0 : u0 ∈ U) (hnot : u0 ∉ A) (hsub : List.Sublist A U)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (htight : (TwoSSTightDisjoint.neighborhood e p A lag).length = A.length)
    (u : Nat) (hu : u ∈ A) (k : Nat)
    (hNk : k ≤ (TwoSSTightDisjoint.neighborhood e p [u] lag).length) :
    k ≤ (LagElevenPeriodic.subPhases e 0 p).length - 2 := by
  have hlen := sublist_avoiding_size_le_deficit hsub hu0 hnot hslack
  have hbound := tight_size_lower_bound p hp A lag u hu k hNk htight
  omega

/-- For `|D| ≤ 4`, no window with at least 3 subtractions can belong to any tight avoiding subset. -/
theorem no_k_ge_three_of_subPhases_le_four (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (A U : List Nat) (lag : Nat → Nat)
    (u0 : Nat) (hu0 : u0 ∈ U) (hnot : u0 ∉ A) (hsub : List.Sublist A U)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (hD4 : (LagElevenPeriodic.subPhases e 0 p).length ≤ 4)
    (htight : (TwoSSTightDisjoint.neighborhood e p A lag).length = A.length)
    (u : Nat) (hu : u ∈ A)
    (hN3 : 3 ≤ (TwoSSTightDisjoint.neighborhood e p [u] lag).length) : False := by
  have hbound := universal_tight_size_bound e p hp A U lag u0 hu0 hnot hsub hslack htight u hu 3 hN3
  omega

/-- For `|D| ≤ 6`, no window with at least 5 subtractions can belong to any tight avoiding subset. -/
theorem no_k_ge_five_of_subPhases_le_six (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (A U : List Nat) (lag : Nat → Nat)
    (u0 : Nat) (hu0 : u0 ∈ U) (hnot : u0 ∉ A) (hsub : List.Sublist A U)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (hD6 : (LagElevenPeriodic.subPhases e 0 p).length ≤ 6)
    (htight : (TwoSSTightDisjoint.neighborhood e p A lag).length = A.length)
    (u : Nat) (hu : u ∈ A)
    (hN5 : 5 ≤ (TwoSSTightDisjoint.neighborhood e p [u] lag).length) : False := by
  have hbound := universal_tight_size_bound e p hp A U lag u0 hu0 hnot hsub hslack htight u hu 5 hN5
  omega

/-- For `|D| ≤ 8`, no window with at least 7 subtractions can belong to any tight avoiding subset. -/
theorem no_k_ge_seven_of_subPhases_le_eight (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (A U : List Nat) (lag : Nat → Nat)
    (u0 : Nat) (hu0 : u0 ∈ U) (hnot : u0 ∉ A) (hsub : List.Sublist A U)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (hD8 : (LagElevenPeriodic.subPhases e 0 p).length ≤ 8)
    (htight : (TwoSSTightDisjoint.neighborhood e p A lag).length = A.length)
    (u : Nat) (hu : u ∈ A)
    (hN7 : 7 ≤ (TwoSSTightDisjoint.neighborhood e p [u] lag).length) : False := by
  have hbound := universal_tight_size_bound e p hp A U lag u0 hu0 hnot hsub hslack htight u hu 7 hN7
  omega

/-- Linear arithmetic equivalence: having `2m - 1 ≤ d_len - 2` is equivalent to `2m + 1 ≤ d_len`. -/
theorem arithmetic_deficit_lag_bound (m d_len : Nat) (hm : 1 ≤ m) (hd : 2 ≤ d_len) :
    2 * m - 1 ≤ d_len - 2 ↔ 2 * m + 1 ≤ d_len := by
  omega

/-- The universal lag bound: if `2m + 1 ≤ d_len`, then `4m - 1 ≤ 2 * d_len - 3`. -/
theorem arithmetic_lag_le_of_m (m d_len : Nat) (hm : 1 ≤ m) (hd : 2 ≤ d_len) (h : 2 * m + 1 ≤ d_len) :
    4 * m - 1 ≤ 2 * d_len - 3 := by
  omega

end Recaman.UniversalTightLagBound
