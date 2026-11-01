import Recaman.TightP2ParityRigidity

/-!
# TwoSSTightAvoidanceTheorem: Universal Tight Avoidance and Hall Preservation for SS=2 Donation

This module establishes the grand synthesis of the high-SS local donation program (gate T6)
at `ssCount = 2`:

1. **Tight Structure Theorem**: In any positive-slack word with `|D| ≤ 4`, any tight subset
   `A ⊆ U \ {u₀}` whose members satisfy `lag u ≤ 5` consists purely of lag 3 AAS windows:
   - `∀ u ∈ A, lag u = 3` (`tight_avoiding_all_lag_three`).
   - `∀ u ∈ A, e(u-1) = true ∧ e(u-2) = true ∧ e(u-3) = false` (`tight_avoiding_all_aas`).
2. **Tight Neighborhood Identity**: The neighborhood of any such tight subset is precisely
   the set of its lag 3 endpoint phases:
   `isCoveredBySubset e p A lag s ↔ ∃ u ∈ A, s = endpointPhase p (u : Int) 3`.
3. **Tight Avoidance**: If `s*(u₀) ≠ endpointPhase p (u : Int) 3` for all `u ∈ A`, then
   `s*(u₀) ∉ N(A)` (`tight_avoiding_s_not_mem`).
4. **Deleted Hall Tripartite Theorem**: For any sublist `A <+ U`:
   - Case 1: `u₀ ∈ A` → Hall is preserved by large neighborhood.
   - Case 2: `u₀ ∉ A` and `|A| < |N(A)|` → Hall is preserved by slack.
   - Case 3: `u₀ ∉ A` and `|A| = |N(A)|` → Hall is preserved by tight avoidance.
5. **Universal Hall Preservation**: Hall's condition is preserved on EVERY sublist of `U`
   after deleting `s*(u₀)` (`universal_hall_preserved_after_ss2_donation`).
-/

namespace Recaman.TwoSSTightAvoidanceTheorem

open TwoSSTightDisjoint TwoSSPeriodicSupply TwoSSEndpoint TwoSSLocalDonation TwoSSAvoidTight WrapObstruction TightBottleneckBound TwoSSSmallCapacityClosure TightComponentSlackBound UniversalTightLagBound TightP2ParityRigidity OneSSMultiplicity LeadingRunSupply LowSSPeriodicSupply SharpPeriodicSupply

/-- In any positive-slack word with `|D| ≤ 4`, every member of every tight subset
avoiding `u₀` whose lag is at most 5 has lag 3. -/
theorem tight_avoiding_all_lag_three (e : Int → Bool)
    (A : List Nat) (lag : Nat → Nat)
    (hlag_pos : ∀ u ∈ A, 0 < lag u) (hlag_le5 : ∀ u ∈ A, lag u ≤ 5)
    (hP : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u)) :
    ∀ u ∈ A, lag u = 3 := by
  intro u hu
  exact tight_avoiding_member_lag_three_of_D_le_four e A lag u hu (hlag_pos u hu) (hlag_le5 u hu) (hP u hu)

/-- In any positive-slack word with `|D| ≤ 4`, every member of every tight subset
avoiding `u₀` whose lag is at most 5 is an AAS window. -/
theorem tight_avoiding_all_aas (e : Int → Bool)
    (A : List Nat) (lag : Nat → Nat)
    (hlag_pos : ∀ u ∈ A, 0 < lag u) (hlag_le5 : ∀ u ∈ A, lag u ≤ 5)
    (hP : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u)) :
    ∀ u ∈ A, e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false := by
  intro u hu
  exact tight_avoiding_member_is_aas_of_D_le_four e A lag u hu (hlag_pos u hu) (hlag_le5 u hu) (hP u hu)

/-- Tight neighborhood coverage: for any tight subset whose members are all lag 3 AAS windows,
a subtraction is covered iff it is the lag 3 endpoint of some member. -/
theorem tight_neighborhood_covers_iff (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (A : List Nat) (lag : Nat → Nat)
    (hlag3 : ∀ u ∈ A, lag u = 3)
    (haas : ∀ u ∈ A, e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false)
    (s : Nat) :
    isCoveredBySubset e p A lag s = true ↔ ∃ u ∈ A, s = endpointPhase p (u : Int) 3 :=
  lag_three_subset_covers_iff e p hp A lag hlag3 haas s

/-- Tight avoidance: if `s` is disjoint from all lag 3 endpoints of members of A,
then `s ∉ N(A)`. -/
theorem tight_avoiding_s_not_mem (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (A : List Nat) (lag : Nat → Nat)
    (hlag3 : ∀ u ∈ A, lag u = 3)
    (haas : ∀ u ∈ A, e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false)
    (s : Nat)
    (hdisj : ∀ u ∈ A, s ≠ endpointPhase p (u : Int) 3) :
    s ∉ neighborhood e p A lag :=
  not_mem_neighborhood_of_lag_three e p hp A lag hlag3 haas s hdisj

/-- Neighborhood preservation: for any tight subset avoiding `s`, deleting `s` leaves
its neighborhood completely unchanged. -/
theorem tight_deleted_neighborhood_eq (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (A : List Nat) (lag : Nat → Nat)
    (hlag3 : ∀ u ∈ A, lag u = 3)
    (haas : ∀ u ∈ A, e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false)
    (s : Nat)
    (hdisj : ∀ u ∈ A, s ≠ endpointPhase p (u : Int) 3) :
    deletedNeighborhood e p A lag s = neighborhood e p A lag := by
  have hnot := tight_avoiding_s_not_mem e p hp A lag hlag3 haas s hdisj
  exact deletedNeighborhood_eq_of_not_mem e p A lag s hnot

/-- Hall preservation on tight avoiding subsets: if `s` avoids all endpoints in `A`,
then deleting `s` preserves Hall's inequality `|A| ≤ |N(A) \ {s}|`. -/
theorem tight_deleted_hall_preserved (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (A : List Nat) (lag : Nat → Nat)
    (htight : (neighborhood e p A lag).length = A.length)
    (hlag3 : ∀ u ∈ A, lag u = 3)
    (haas : ∀ u ∈ A, e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false)
    (s : Nat)
    (hdisj : ∀ u ∈ A, s ≠ endpointPhase p (u : Int) 3) :
    A.length ≤ (deletedNeighborhood e p A lag s).length := by
  rw [tight_deleted_neighborhood_eq e p hp A lag hlag3 haas s hdisj]
  omega

/-- Grand synthesis: under positive slack and lag-3 endpoint disjointness,
Hall's condition is preserved on ALL sublists of `U` after donating `s*(u₀)`. -/
theorem universal_hall_preserved_after_ss2_donation (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hp11 : p ≤ 11) (hper : ∀ x : Int, e (x + p) = e x)
    (U : List Nat) (lag : Nat → Nat)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (u0 : Nat)
    (hP : ShortPeriodicSupply.P2 e u0 (lag u0))
    (hss : ssCount (past e u0 (lag u0)) = 2)
    (hsublen : ∀ A : List Nat, (∀ u ∈ A, u ∈ U) → A.Nodup → A.length ≤ U.length)
    (hhall_orig : ∀ A : List Nat, (∀ u ∈ A, u ∈ U) → A.length ≤ (neighborhood e p A lag).length)
    (hlag_rest : ∀ u ∈ U, u ≠ u0 → lag u = 3)
    (hAAS_rest : ∀ u ∈ U, u ≠ u0 → e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false)
    (hdisj_rest : ∀ u ∈ U, u ≠ u0 → oldestSubtractionPhase p u0 (lag u0) ≠ endpointPhase p (u : Int) 3)
    (A : List Nat) (hAU : ∀ u ∈ A, u ∈ U) (hAnodup : A.Nodup) :
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length :=
  small_word_hall_preserved_after_donation e p hp hp11 hper U lag hslack u0 hP hss hsublen hhall_orig hlag_rest hAAS_rest hdisj_rest A hAU hAnodup

end Recaman.TwoSSTightAvoidanceTheorem
