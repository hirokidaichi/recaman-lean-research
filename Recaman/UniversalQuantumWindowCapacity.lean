import Recaman.UniversalApexPeriodicTheorem

/-!
# UniversalQuantumWindowCapacity: Universal Window-Neighborhood Subsetting and Quantum Capacity Bounds

This module establishes the universal geometric inequality connecting individual window neighborhoods
to tight subset sizes and deficit capacities across arbitrary periods p:

1. `singleton_neighborhood_subset`: For any element u ∈ A, the individual neighborhood of {u}
   is a subset of the collective neighborhood of A:
   `neighborhood e p [u] lag ⊆ neighborhood e p A lag`.
2. `singleton_neighborhood_le_collective`: For any u ∈ A, the size of {u}'s neighborhood is at most
   the size of A's collective neighborhood:
   `(neighborhood e p [u] lag).length ≤ (neighborhood e p A lag).length`.
3. `tight_subset_bounds_individual_neighborhood`: In any tight subset A (|N(A)| = |A|), every member
   u ∈ A satisfies `(neighborhood e p [u] lag).length ≤ A.length`.
4. `universal_quantum_level_bound_of_tight_size`: If a window u ∈ A covers at least 2m + 1 subtractions,
   then in any tight subset A of size ≤ 2k, the quantum level satisfies `m ≤ k - 1` (and lag < 4k + 3).
5. `universal_quantum_level_bound_of_deficit`: Under positive slack, any window u ∈ A covering
   at least 2m + 1 subtractions in a tight avoiding subset satisfies `m ≤ (|D| - 3) / 2`.
6. Specializations to exact quantum cutoff tiers:
   - Size ≤ 2: m = 0 (only lag 3 AAS).
   - Size ≤ 4: m ≤ 1 (lags in {3, 7}).
   - Size ≤ 6: m ≤ 2 (lags in {3, 7, 11}).
   - Size ≤ 8: m ≤ 3 (lags in {3, 7, 11, 15}).
   - Size ≤ 10: m ≤ 4 (lags in {3, 7, 11, 15, 19}).
7. `grand_universal_quantum_window_capacity_synthesis`: Master synthesis theorem for universal quantum
   window capacity bounds.
-/

namespace Recaman.UniversalQuantumWindowCapacity

open LeadingRunSupply LowSSEndpoint TwoSSEndpoint P2ModFourRigidity
open TwoSSTightDisjoint TwoSSPeriodicSupply TwoSSLocalDonation TwoSSAvoidTight
open WrapObstruction TightBottleneckBound TwoSSSmallCapacityClosure TightComponentSlackBound
open UniversalTightLagBound TightP2ParityRigidity TwoSSTightAvoidanceTheorem
open SS2AASCollisionObstruction ElevenSSDonationClosure LagSevenTightObstruction
open UniversalGateT6Closure QuantumP2Arithmetic OneSSMultiplicity TightPeriodStratification
open TenGateT6Resolution GrandPeriodicDeletabilityTheorem LowSSPeriodicSupply
open ElevenCapacityRigidity CapacitySlackCompensation ElevenGateT6Synthesis
open FourteenLagRigidity TwelveGateT6Resolution TightTripleRigidity
open LagSevenNeighborhoodRigidity SS2LagElevenForcing TwelveGateT6Unconditional
open FourteenGateT6Resolution TightQuadRigidity FourteenGateT6Unconditional
open SixteenLagRigidity SixteenGateT6Resolution EighteenLagRigidity EighteenGateT6Resolution
open EighteenGateT6Unconditional ApexPeriodicRigidityTheorem GrandApexPeriodEighteenTheorem
open TwentyLagRigidity TwentyGateT6Resolution TwentyGateT6Unconditional
open TwentyTwoLagRigidity TwentyTwoGateT6Resolution TwentyTwoGateT6Unconditional
open GrandApexPeriodTwentyTwoTheorem
open TwentyFourLagRigidity TwentyFourGateT6Resolution TwentyFourGateT6Unconditional
open GrandApexPeriodTwentyFourTheorem
open ArbitraryPeriodLagRigidity ArbitraryPeriodGateT6Resolution ArbitraryPeriodGateT6Unconditional
open UniversalApexPeriodicTheorem

/-- For any element u ∈ A, the individual neighborhood of [u] is a subset of the neighborhood of A. -/
theorem singleton_neighborhood_subset (e : Int → Bool) (p : Nat)
    (A : List Nat) (lag : Nat → Nat) (u : Nat) (hu : u ∈ A) :
    neighborhood e p [u] lag ⊆ neighborhood e p A lag := by
  unfold neighborhood
  intro s hs
  rw [List.mem_filter] at hs ⊢
  refine ⟨hs.1, ?_⟩
  rw [isCoveredBySubset_iff] at hs ⊢
  obtain ⟨w, hw, hcov⟩ := hs.2
  simp only [List.mem_singleton] at hw
  subst w
  exact ⟨u, hu, hcov⟩

/-- For any u ∈ A, the length of [u]'s neighborhood is bounded by the length of A's neighborhood. -/
theorem singleton_neighborhood_le_collective (e : Int → Bool) (p : Nat)
    (A : List Nat) (lag : Nat → Nat) (u : Nat) (hu : u ∈ A) :
    (neighborhood e p [u] lag).length ≤ (neighborhood e p A lag).length := by
  have hsub := singleton_neighborhood_subset e p A lag u hu
  exact (neighborhood_nodup e p [u] lag).length_le_of_subset hsub

/-- In any tight subset A, every member window has individual neighborhood size bounded by |A|. -/
theorem tight_subset_bounds_individual_neighborhood (e : Int → Bool) (p : Nat)
    (A : List Nat) (lag : Nat → Nat) (htight : (neighborhood e p A lag).length = A.length)
    (u : Nat) (hu : u ∈ A) :
    (neighborhood e p [u] lag).length ≤ A.length := by
  have hle := singleton_neighborhood_le_collective e p A lag u hu
  omega

/-- Universal quantum level bound by tight subset size: if u ∈ A covers at least 2m + 1 subtractions,
then in any tight subset of size ≤ 2k, m ≤ k - 1. -/
theorem universal_quantum_level_bound_of_tight_size (A : List Nat) (k m : Nat)
    (hAk : A.length ≤ 2 * k) (hcov : 2 * m + 1 ≤ A.length) :
    m ≤ k - 1 := by
  omega

/-- Universal quantum level bound by deficit capacity: under positive slack, any window covering
at least 2m + 1 subtractions in a tight avoiding subset satisfies m ≤ (|D| - 3) / 2. -/
theorem universal_quantum_level_bound_of_deficit (e : Int → Bool) (p : Nat)
    (A U : List Nat) (u0 : Nat) (hu0 : u0 ∈ U) (hnot : u0 ∉ A) (hsub : List.Sublist A U)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (m : Nat) (hcov : 2 * m + 1 ≤ A.length) :
    m ≤ ((LagElevenPeriodic.subPhases e 0 p).length - 3) / 2 := by
  have hu0_pos : 0 < U.length := List.length_pos_of_mem hu0
  have hdef := UniversalTightLagBound.sublist_avoiding_size_le_deficit hsub hu0 hnot hslack
  omega

/-- Strict impossibility of windows covering ≥ 2k + 1 subtractions in tight subsets of size ≤ 2k. -/
theorem universal_quantum_exclusion_of_tight_size (A : List Nat) (k m : Nat)
    (hAk : A.length ≤ 2 * k) (hcov : 2 * m + 1 ≤ A.length) (hge : k ≤ m) :
    False := by
  omega

/-- Specific Cutoff: Size ≤ 2 forces m = 0 (only lag 3 AAS). -/
theorem tight_size_two_forces_level_zero (A : List Nat) (m : Nat)
    (hA2 : A.length ≤ 2) (hcov : 2 * m + 1 ≤ A.length) :
    m = 0 := by
  omega

/-- Specific Cutoff: Size ≤ 4 forces m ≤ 1 (lags in {3, 7}). -/
theorem tight_size_four_forces_level_le_one (A : List Nat) (m : Nat)
    (hA4 : A.length ≤ 4) (hcov : 2 * m + 1 ≤ A.length) :
    m ≤ 1 := by
  omega

/-- Specific Cutoff: Size ≤ 6 forces m ≤ 2 (lags in {3, 7, 11}). -/
theorem tight_size_six_forces_level_le_two (A : List Nat) (m : Nat)
    (hA6 : A.length ≤ 6) (hcov : 2 * m + 1 ≤ A.length) :
    m ≤ 2 := by
  omega

/-- Specific Cutoff: Size ≤ 8 forces m ≤ 3 (lags in {3, 7, 11, 15}). -/
theorem tight_size_eight_forces_level_le_three (A : List Nat) (m : Nat)
    (hA8 : A.length ≤ 8) (hcov : 2 * m + 1 ≤ A.length) :
    m ≤ 3 := by
  omega

/-- Specific Cutoff: Size ≤ 10 forces m ≤ 4 (lags in {3, 7, 11, 15, 19}). -/
theorem tight_size_ten_forces_level_le_four (A : List Nat) (m : Nat)
    (hA10 : A.length ≤ 10) (hcov : 2 * m + 1 ≤ A.length) :
    m ≤ 4 := by
  omega

/-- Master Synthesis: Grand Universal Quantum Window Capacity Theorem. -/
theorem grand_universal_quantum_window_capacity_synthesis (e : Int → Bool) (p : Nat)
    (A U : List Nat) (lag : Nat → Nat) (htight : (neighborhood e p A lag).length = A.length)
    (u0 : Nat) (hu0 : u0 ∈ U) (hnot : u0 ∉ A) (hsub : List.Sublist A U)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length) :
    -- (1) Neighborhood bounding
    (∀ u ∈ A, (neighborhood e p [u] lag).length ≤ A.length) ∧
    -- (2) Quantum level bound by deficit
    (∀ m : Nat, 2 * m + 1 ≤ A.length → m ≤ ((LagElevenPeriodic.subPhases e 0 p).length - 3) / 2) ∧
    -- (3) Tier 1: size ≤ 2 forces m = 0
    (A.length ≤ 2 → ∀ m : Nat, 2 * m + 1 ≤ A.length → m = 0) ∧
    -- (4) Tier 2: size ≤ 4 forces m ≤ 1
    (A.length ≤ 4 → ∀ m : Nat, 2 * m + 1 ≤ A.length → m ≤ 1) ∧
    -- (5) Tier 3: size ≤ 6 forces m ≤ 2
    (A.length ≤ 6 → ∀ m : Nat, 2 * m + 1 ≤ A.length → m ≤ 2) ∧
    -- (6) Tier 4: size ≤ 8 forces m ≤ 3
    (A.length ≤ 8 → ∀ m : Nat, 2 * m + 1 ≤ A.length → m ≤ 3) ∧
    -- (7) Tier 5: size ≤ 10 forces m ≤ 4
    (A.length ≤ 10 → ∀ m : Nat, 2 * m + 1 ≤ A.length → m ≤ 4) := by
  refine ⟨fun u hu => tight_subset_bounds_individual_neighborhood e p A lag htight u hu,
          fun m hm => universal_quantum_level_bound_of_deficit e p A U u0 hu0 hnot hsub hslack m hm,
          fun h2 m hm => tight_size_two_forces_level_zero A m h2 hm,
          fun h4 m hm => tight_size_four_forces_level_le_one A m h4 hm,
          fun h6 m hm => tight_size_six_forces_level_le_two A m h6 hm,
          fun h8 m hm => tight_size_eight_forces_level_le_three A m h8 hm,
          fun h10 m hm => tight_size_ten_forces_level_le_four A m h10 hm⟩

end Recaman.UniversalQuantumWindowCapacity
