import Recaman.UniversalQuantumWindowCapacity

/-!
# TightSubsetLagStructure: Exact Structural Bounds on Window Neighborhoods in Tight Subsets

This module establishes the exact structural theorems governing individual window neighborhoods
and quantum lag exclusions inside tight bottleneck subsets:

1. `tight_subset_member_neighborhood_le`: In any tight subset A (|N(A)| = |A|),
   every member u ∈ A satisfies `(neighborhood e p [u] lag).length ≤ A.length`.
2. `no_ge_three_in_tight_le_two`: No window with individual neighborhood size ≥ 3 can belong
   to any tight subset of size ≤ 2.
3. `no_ge_five_in_tight_le_four`: No window with individual neighborhood size ≥ 5 can belong
   to any tight subset of size ≤ 4.
4. `no_ge_seven_in_tight_le_six`: No window with individual neighborhood size ≥ 7 can belong
   to any tight subset of size ≤ 6.
5. `no_ge_nine_in_tight_le_eight`: No window with individual neighborhood size ≥ 9 can belong
   to any tight subset of size ≤ 8.
6. `no_ge_two_k_plus_one_in_tight_le_two_k`: Universal law: for any k, no window with individual
   neighborhood size ≥ 2k + 1 can belong to any tight subset of size ≤ 2k.
7. `two_disjoint_ge_two_exceeds_tight_three`: If two windows in a tight subset have disjoint
   neighborhoods of size ≥ 2, their collective neighborhood has size ≥ 4, which is impossible in size ≤ 3.
8. `two_disjoint_ge_three_exceeds_tight_five`: If two windows in a tight subset have disjoint
   neighborhoods of size ≥ 3, their collective neighborhood has size ≥ 6, impossible in size ≤ 5.
9. `grand_tight_subset_lag_structure_synthesis`: Master synthesis theorem for tight subset lag structure.
-/

namespace Recaman.TightSubsetLagStructure

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
open UniversalApexPeriodicTheorem UniversalQuantumWindowCapacity

/-- In any tight subset A, every member window u ∈ A has individual neighborhood size bounded by |A|. -/
theorem tight_subset_member_neighborhood_le (e : Int → Bool) (p : Nat)
    (A : List Nat) (lag : Nat → Nat)
    (htight : (neighborhood e p A lag).length = A.length)
    (u : Nat) (hu : u ∈ A) :
    (neighborhood e p [u] lag).length ≤ A.length :=
  tight_subset_bounds_individual_neighborhood e p A lag htight u hu

/-- No window with individual neighborhood size ≥ 3 can belong to any tight subset of size ≤ 2. -/
theorem no_ge_three_in_tight_le_two (e : Int → Bool) (p : Nat)
    (A : List Nat) (lag : Nat → Nat)
    (hle2 : A.length ≤ 2)
    (htight : (neighborhood e p A lag).length = A.length)
    (u : Nat) (hu : u ∈ A)
    (hN3 : 3 ≤ (neighborhood e p [u] lag).length) : False := by
  have hle := tight_subset_member_neighborhood_le e p A lag htight u hu
  omega

/-- No window with individual neighborhood size ≥ 5 can belong to any tight subset of size ≤ 4. -/
theorem no_ge_five_in_tight_le_four (e : Int → Bool) (p : Nat)
    (A : List Nat) (lag : Nat → Nat)
    (hle4 : A.length ≤ 4)
    (htight : (neighborhood e p A lag).length = A.length)
    (u : Nat) (hu : u ∈ A)
    (hN5 : 5 ≤ (neighborhood e p [u] lag).length) : False := by
  have hle := tight_subset_member_neighborhood_le e p A lag htight u hu
  omega

/-- No window with individual neighborhood size ≥ 7 can belong to any tight subset of size ≤ 6. -/
theorem no_ge_seven_in_tight_le_six (e : Int → Bool) (p : Nat)
    (A : List Nat) (lag : Nat → Nat)
    (hle6 : A.length ≤ 6)
    (htight : (neighborhood e p A lag).length = A.length)
    (u : Nat) (hu : u ∈ A)
    (hN7 : 7 ≤ (neighborhood e p [u] lag).length) : False := by
  have hle := tight_subset_member_neighborhood_le e p A lag htight u hu
  omega

/-- No window with individual neighborhood size ≥ 9 can belong to any tight subset of size ≤ 8. -/
theorem no_ge_nine_in_tight_le_eight (e : Int → Bool) (p : Nat)
    (A : List Nat) (lag : Nat → Nat)
    (hle8 : A.length ≤ 8)
    (htight : (neighborhood e p A lag).length = A.length)
    (u : Nat) (hu : u ∈ A)
    (hN9 : 9 ≤ (neighborhood e p [u] lag).length) : False := by
  have hle := tight_subset_member_neighborhood_le e p A lag htight u hu
  omega

/-- Universal Law: for any k, no window with individual neighborhood size ≥ 2k + 1 can belong
to any tight subset of size ≤ 2k. -/
theorem no_ge_two_k_plus_one_in_tight_le_two_k (e : Int → Bool) (p : Nat)
    (A : List Nat) (lag : Nat → Nat) (k : Nat)
    (hle : A.length ≤ 2 * k)
    (htight : (neighborhood e p A lag).length = A.length)
    (u : Nat) (hu : u ∈ A)
    (hN : 2 * k + 1 ≤ (neighborhood e p [u] lag).length) : False := by
  have hle_u := tight_subset_member_neighborhood_le e p A lag htight u hu
  omega

/-- Two distinct windows with disjoint neighborhoods of size ≥ 2 cannot both belong to a tight subset
of size ≤ 3. -/
theorem two_disjoint_ge_two_exceeds_tight_three (e : Int → Bool) (p : Nat)
    (A : List Nat) (lag : Nat → Nat)
    (hle3 : A.length ≤ 3)
    (htight : (neighborhood e p A lag).length = A.length)
    (u v : Nat) (hu : u ∈ A) (hv : v ∈ A)
    (hdisj : ∀ s, s ∈ neighborhood e p [u] lag → s ∉ neighborhood e p [v] lag)
    (hNu : 2 ≤ (neighborhood e p [u] lag).length)
    (hNv : 2 ≤ (neighborhood e p [v] lag).length) : False := by
  have hsub_u : neighborhood e p [u] lag ⊆ neighborhood e p A lag :=
    singleton_neighborhood_subset e p A lag u hu
  have hsub_v : neighborhood e p [v] lag ⊆ neighborhood e p A lag :=
    singleton_neighborhood_subset e p A lag v hv
  have hsub_both : (neighborhood e p [u] lag ++ neighborhood e p [v] lag) ⊆ neighborhood e p A lag := by
    intro s hs
    rw [List.mem_append] at hs
    rcases hs with hsu | hsv
    · exact hsub_u hsu
    · exact hsub_v hsv
  have hnodup : (neighborhood e p [u] lag ++ neighborhood e p [v] lag).Nodup := by
    rw [List.nodup_append]
    refine ⟨neighborhood_nodup e p [u] lag, neighborhood_nodup e p [v] lag, ?_⟩
    intro a ha b hb
    intro heq
    subst heq
    exact hdisj a ha hb
  have hlen := hnodup.length_le_of_subset hsub_both
  rw [List.length_append] at hlen
  omega

/-- Two distinct windows with disjoint neighborhoods of size ≥ 3 cannot both belong to a tight subset
of size ≤ 5. -/
theorem two_disjoint_ge_three_exceeds_tight_five (e : Int → Bool) (p : Nat)
    (A : List Nat) (lag : Nat → Nat)
    (hle5 : A.length ≤ 5)
    (htight : (neighborhood e p A lag).length = A.length)
    (u v : Nat) (hu : u ∈ A) (hv : v ∈ A)
    (hdisj : ∀ s, s ∈ neighborhood e p [u] lag → s ∉ neighborhood e p [v] lag)
    (hNu : 3 ≤ (neighborhood e p [u] lag).length)
    (hNv : 3 ≤ (neighborhood e p [v] lag).length) : False := by
  have hsub_u : neighborhood e p [u] lag ⊆ neighborhood e p A lag :=
    singleton_neighborhood_subset e p A lag u hu
  have hsub_v : neighborhood e p [v] lag ⊆ neighborhood e p A lag :=
    singleton_neighborhood_subset e p A lag v hv
  have hsub_both : (neighborhood e p [u] lag ++ neighborhood e p [v] lag) ⊆ neighborhood e p A lag := by
    intro s hs
    rw [List.mem_append] at hs
    rcases hs with hsu | hsv
    · exact hsub_u hsu
    · exact hsub_v hsv
  have hnodup : (neighborhood e p [u] lag ++ neighborhood e p [v] lag).Nodup := by
    rw [List.nodup_append]
    refine ⟨neighborhood_nodup e p [u] lag, neighborhood_nodup e p [v] lag, ?_⟩
    intro a ha b hb
    intro heq
    subst heq
    exact hdisj a ha hb
  have hlen := hnodup.length_le_of_subset hsub_both
  rw [List.length_append] at hlen
  omega

/-- Master Synthesis: Grand Tight Subset Lag Structure Theorem. -/
theorem grand_tight_subset_lag_structure_synthesis (e : Int → Bool) (p : Nat)
    (A : List Nat) (lag : Nat → Nat)
    (htight : (neighborhood e p A lag).length = A.length) :
    -- (1) General bounding by |A|
    (∀ u ∈ A, (neighborhood e p [u] lag).length ≤ A.length) ∧
    -- (2) Cutoff for size ≤ 2
    (A.length ≤ 2 → ∀ u ∈ A, 3 ≤ (neighborhood e p [u] lag).length → False) ∧
    -- (3) Cutoff for size ≤ 4
    (A.length ≤ 4 → ∀ u ∈ A, 5 ≤ (neighborhood e p [u] lag).length → False) ∧
    -- (4) Cutoff for size ≤ 6
    (A.length ≤ 6 → ∀ u ∈ A, 7 ≤ (neighborhood e p [u] lag).length → False) ∧
    -- (5) Cutoff for size ≤ 8
    (A.length ≤ 8 → ∀ u ∈ A, 9 ≤ (neighborhood e p [u] lag).length → False) := by
  refine ⟨fun u hu => tight_subset_member_neighborhood_le e p A lag htight u hu,
          fun h2 u hu h3 => no_ge_three_in_tight_le_two e p A lag h2 htight u hu h3,
          fun h4 u hu h5 => no_ge_five_in_tight_le_four e p A lag h4 htight u hu h5,
          fun h6 u hu h7 => no_ge_seven_in_tight_le_six e p A lag h6 htight u hu h7,
          fun h8 u hu h9 => no_ge_nine_in_tight_le_eight e p A lag h8 htight u hu h9⟩

end Recaman.TightSubsetLagStructure
