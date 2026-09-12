import Recaman.GrandApexPeriodTwentyFourTheorem

/-!
# ArbitraryPeriodLagRigidity: Universal Parametric Capacity and Quantum Lag Rigidity for All Periods p

This module establishes the universal closed-form capacity bounds and quantum lag bounds for
arbitrary periods p (fully parametric over all p ∈ ℕ):

1. `arbitrary_period_subtractions_bound`: In any periodic word of arbitrary period p with positive signSum,
   the number of subtractions is bounded by |D| ≤ (p - 1) / 2.
2. `arbitrary_period_avoiding_size_bound`: In any periodic word of arbitrary period p with positive signSum
   and positive slack, any avoiding sublist satisfies |A| ≤ |D| - 2 ≤ (p - 1) / 2 - 2.
3. `arbitrary_period_tight_quantum_bound`: In any periodic word of arbitrary period p with positive signSum
   and positive slack, any window in a tight avoiding subset A covering at least 2m + 1 subtractions
   satisfies 2m + 1 ≤ A.length ≤ |D| - 2.
4. `arbitrary_period_tight_quantum_level_bound`: Under positive signSum and slack, any window covering
   at least 2m + 1 subtractions in a tight avoiding subset satisfies m ≤ (|D| - 3) / 2.
5. `arbitrary_period_no_large_window_in_tight`: Any window covering k subtractions with k ≥ |D| - 1
   cannot belong to any tight avoiding subset.
6. `arbitrary_period_quantum_exclusion`: If 2m + 1 > |D| - 2, quantum level m is universally excluded
   from all tight avoiding subsets.
7. `arbitrary_period_capacity_specialization`: General evaluation of the capacity bound for any p.
8. `grand_arbitrary_period_lag_rigidity_synthesis`: Master synthesis theorem for arbitrary-period
   parametric capacity and quantum lag bounds.
-/

namespace Recaman.ArbitraryPeriodLagRigidity

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

/-- In any periodic word of arbitrary period p with positive signSum, |D| ≤ (p - 1) / 2. -/
theorem arbitrary_period_subtractions_bound (e : Int → Bool) (p : Nat)
    (hpos : 0 < ShortPeriodicSupply.signSum e 0 p) :
    (LagElevenPeriodic.subPhases e 0 p).length ≤ (p - 1) / 2 := by
  have hbound := TightComponentSlackBound.subPhases_bound_of_pos_signSum e p hpos
  omega

/-- In any periodic word of arbitrary period p with positive signSum and positive slack,
any avoiding sublist satisfies |A| ≤ |D| - 2 ≤ (p - 1) / 2 - 2. -/
theorem arbitrary_period_avoiding_size_bound (e : Int → Bool) (p : Nat)
    (hpos : 0 < ShortPeriodicSupply.signSum e 0 p)
    (A U : List Nat) (u0 : Nat) (hu0 : u0 ∈ U) (hnot : u0 ∉ A) (hsub : List.Sublist A U)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length) :
    A.length ≤ (LagElevenPeriodic.subPhases e 0 p).length - 2 ∧
    A.length ≤ (p - 1) / 2 - 2 := by
  have hD := arbitrary_period_subtractions_bound e p hpos
  have hdef := UniversalTightLagBound.sublist_avoiding_size_le_deficit hsub hu0 hnot hslack
  refine ⟨hdef, by omega⟩

/-- In any periodic word of arbitrary period p with positive signSum and positive slack,
any window in a tight avoiding subset A covering at least 2m + 1 subtractions satisfies
2m + 1 ≤ A.length ≤ |D| - 2. -/
theorem arbitrary_period_tight_quantum_bound (e : Int → Bool) (p : Nat)
    (_hpos : 0 < ShortPeriodicSupply.signSum e 0 p)
    (A U : List Nat) (u0 : Nat) (hu0 : u0 ∈ U) (hnot : u0 ∉ A) (hsub : List.Sublist A U)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (m : Nat) (hsub_cov : 2 * m + 1 ≤ A.length) :
    2 * m + 1 ≤ (LagElevenPeriodic.subPhases e 0 p).length - 2 := by
  have hdef := UniversalTightLagBound.sublist_avoiding_size_le_deficit hsub hu0 hnot hslack
  omega

/-- Under positive signSum and slack, any window covering at least 2m + 1 subtractions
in a tight avoiding subset satisfies m ≤ (|D| - 3) / 2. -/
theorem arbitrary_period_tight_quantum_level_bound (e : Int → Bool) (p : Nat)
    (hpos : 0 < ShortPeriodicSupply.signSum e 0 p)
    (A U : List Nat) (u0 : Nat) (hu0 : u0 ∈ U) (hnot : u0 ∉ A) (hsub : List.Sublist A U)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (m : Nat) (hsub_cov : 2 * m + 1 ≤ A.length) :
    m ≤ ((LagElevenPeriodic.subPhases e 0 p).length - 3) / 2 := by
  have hq := arbitrary_period_tight_quantum_bound e p hpos A U u0 hu0 hnot hsub hslack m hsub_cov
  omega

/-- Any window covering k subtractions with k ≥ |D| - 1 cannot belong to any tight
avoiding subset. -/
theorem arbitrary_period_no_large_window_in_tight (e : Int → Bool) (p : Nat)
    (A U : List Nat) (u0 : Nat) (hu0 : u0 ∈ U) (hnot : u0 ∉ A) (hsub : List.Sublist A U)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (k : Nat) (hkA : k ≤ A.length)
    (hge : (LagElevenPeriodic.subPhases e 0 p).length - 1 ≤ k) :
    False := by
  have hu0_pos : 0 < U.length := List.length_pos_of_mem hu0
  have hdef := UniversalTightLagBound.sublist_avoiding_size_le_deficit hsub hu0 hnot hslack
  omega

/-- If 2m + 1 > |D| - 2, quantum level m is universally excluded from all tight avoiding subsets. -/
theorem arbitrary_period_quantum_exclusion (e : Int → Bool) (p : Nat)
    (A U : List Nat) (u0 : Nat) (hu0 : u0 ∈ U) (hnot : u0 ∉ A) (hsub : List.Sublist A U)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (m : Nat) (hkA : 2 * m + 1 ≤ A.length)
    (hexcl : (LagElevenPeriodic.subPhases e 0 p).length - 2 < 2 * m + 1) :
    False := by
  have hu0_pos : 0 < U.length := List.length_pos_of_mem hu0
  have hdef := UniversalTightLagBound.sublist_avoiding_size_le_deficit hsub hu0 hnot hslack
  omega

/-- Specialization of the general capacity bound to any upper bound P on period p. -/
theorem arbitrary_period_capacity_specialization (e : Int → Bool) (p P : Nat)
    (hle : p ≤ P) (hpos : 0 < ShortPeriodicSupply.signSum e 0 p) :
    (LagElevenPeriodic.subPhases e 0 p).length ≤ (P - 1) / 2 := by
  have hbound := arbitrary_period_subtractions_bound e p hpos
  omega

/-- Master Synthesis: Grand Arbitrary-Period Lag Rigidity Theorem. -/
theorem grand_arbitrary_period_lag_rigidity_synthesis (e : Int → Bool) (p : Nat)
    (hpos : 0 < ShortPeriodicSupply.signSum e 0 p)
    (A U : List Nat) (u0 : Nat) (hu0 : u0 ∈ U) (hnot : u0 ∉ A) (hsub : List.Sublist A U)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length) :
    -- (1) Parametric subtractions upper bound
    (LagElevenPeriodic.subPhases e 0 p).length ≤ (p - 1) / 2 ∧
    -- (2) Parametric avoiding size upper bound
    A.length ≤ (LagElevenPeriodic.subPhases e 0 p).length - 2 ∧
    -- (3) Combined parametric avoiding size bound
    A.length ≤ (p - 1) / 2 - 2 ∧
    -- (4) Quantum level bound for any window in A
    (∀ m : Nat, 2 * m + 1 ≤ A.length → m ≤ ((LagElevenPeriodic.subPhases e 0 p).length - 3) / 2) ∧
    -- (5) Impossibility of windows covering ≥ |D| - 1 subtractions
    (∀ k : Nat, k ≤ A.length → (LagElevenPeriodic.subPhases e 0 p).length - 1 ≤ k → False) := by
  refine ⟨arbitrary_period_subtractions_bound e p hpos,
          (arbitrary_period_avoiding_size_bound e p hpos A U u0 hu0 hnot hsub hslack).1,
          (arbitrary_period_avoiding_size_bound e p hpos A U u0 hu0 hnot hsub hslack).2,
          fun m hm => arbitrary_period_tight_quantum_level_bound e p hpos A U u0 hu0 hnot hsub hslack m hm,
          fun k hk hge => arbitrary_period_no_large_window_in_tight e p A U u0 hu0 hnot hsub hslack k hk hge⟩

end Recaman.ArbitraryPeriodLagRigidity
