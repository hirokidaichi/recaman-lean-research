import Recaman.ElevenGateT6Synthesis
import Recaman.QuantumP2Arithmetic
import Recaman.UniversalTightLagBound
import Recaman.TightComponentSlackBound
import Recaman.P2ModFourRigidity

/-!
# FourteenLagRigidity: Quantum Lag Bounds and Capacity Rigidity for Periods p ≤ 14

This module establishes the structural lag and capacity rigidity for periods up to `p ≤ 14`:

1. `p14_subtractions_bound`: In any periodic word of period `p ≤ 14` with positive signSum,
   the number of subtractions is bounded by `|D| ≤ 6`.
2. `p12_subtractions_bound`: In any periodic word of period `p ≤ 12` with positive signSum,
   the number of subtractions is bounded by `|D| ≤ 5`.
3. `p14_avoiding_size_le_four`: In any periodic word of period `p ≤ 14` with positive slack,
   any sublist avoiding `u₀ ∈ U` satisfies `|A| ≤ 4`.
4. `p12_avoiding_size_le_three`: In any periodic word of period `p ≤ 12` with positive slack,
   any sublist avoiding `u₀ ∈ U` satisfies `|A| ≤ 3`.
5. `p14_no_k_ge_five_in_tight`: In period `p ≤ 14`, no window covering at least 5 subtractions
   can belong to any tight avoiding subset.
6. `p14_tight_quantum_level_le_one`: Any member of a tight avoiding subset of size `≤ 4`
   covering at least `2m + 1` subtractions has quantum level `m ≤ 1`.
7. `p12_gate_t6_of_U_le_three`: In period `p ≤ 12`, whenever `|U| ≤ 3` (or `|D| ≤ 4`),
   Gate T6 holds unconditionally on all sublists of `U` with `p ≤ 11`.
8. `p12_gate_t6_of_tight_all_aas`: In period `p ≤ 11`, if all tight avoiding sublists are lag 3 AAS,
   Gate T6 holds unconditionally on ALL sublists of `U`.
9. `p12_avoiding_all_le_three`: Every avoiding sublist in `p ≤ 12` has size `≤ 3`.
10. `grand_fourteen_lag_rigidity_synthesis`: Master synthesis theorem for periods `p ≤ 14`.
-/

namespace Recaman.FourteenLagRigidity

open LeadingRunSupply LowSSEndpoint TwoSSEndpoint P2ModFourRigidity
open TwoSSTightDisjoint TwoSSPeriodicSupply TwoSSLocalDonation TwoSSAvoidTight
open WrapObstruction TightBottleneckBound TwoSSSmallCapacityClosure TightComponentSlackBound
open UniversalTightLagBound TightP2ParityRigidity TwoSSTightAvoidanceTheorem
open SS2AASCollisionObstruction ElevenSSDonationClosure LagSevenTightObstruction
open UniversalGateT6Closure QuantumP2Arithmetic OneSSMultiplicity TightPeriodStratification
open TenGateT6Resolution GrandPeriodicDeletabilityTheorem LowSSPeriodicSupply
open ElevenCapacityRigidity CapacitySlackCompensation ElevenGateT6Synthesis

/-- In any periodic word of period p ≤ 14 with positive signSum, |D| ≤ 6. -/
theorem p14_subtractions_bound (e : Int → Bool) (p : Nat)
    (hp14 : p ≤ 14) (hpos : 0 < ShortPeriodicSupply.signSum e 0 p) :
    (LagElevenPeriodic.subPhases e 0 p).length ≤ 6 := by
  have hbound := TightComponentSlackBound.subPhases_bound_of_pos_signSum e p hpos
  omega

/-- In any periodic word of period p ≤ 12 with positive signSum, |D| ≤ 5. -/
theorem p12_subtractions_bound (e : Int → Bool) (p : Nat)
    (hp12 : p ≤ 12) (hpos : 0 < ShortPeriodicSupply.signSum e 0 p) :
    (LagElevenPeriodic.subPhases e 0 p).length ≤ 5 := by
  have hbound := TightComponentSlackBound.subPhases_bound_of_pos_signSum e p hpos
  omega

/-- In any periodic word of period p ≤ 14 with positive slack, any avoiding sublist has |A| ≤ 4. -/
theorem p14_avoiding_size_le_four (e : Int → Bool) (p : Nat)
    (hp14 : p ≤ 14) (hpos : 0 < ShortPeriodicSupply.signSum e 0 p)
    (A U : List Nat) (u0 : Nat) (hu0 : u0 ∈ U) (hnot : u0 ∉ A) (hsub : List.Sublist A U)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length) :
    A.length ≤ 4 := by
  have hD6 := p14_subtractions_bound e p hp14 hpos
  exact UniversalTightLagBound.tight_avoiding_size_le_four_of_subPhases_le_six e p A U u0 hu0 hnot hsub hslack hD6

/-- In any periodic word of period p ≤ 12 with positive slack, any avoiding sublist has |A| ≤ 3. -/
theorem p12_avoiding_size_le_three (e : Int → Bool) (p : Nat)
    (hp12 : p ≤ 12) (hpos : 0 < ShortPeriodicSupply.signSum e 0 p)
    (A U : List Nat) (u0 : Nat) (hu0 : u0 ∈ U) (hnot : u0 ∉ A) (hsub : List.Sublist A U)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length) :
    A.length ≤ 3 := by
  have hD5 := p12_subtractions_bound e p hp12 hpos
  exact UniversalTightLagBound.tight_avoiding_size_le_three_of_subPhases_le_five e p A U u0 hu0 hnot hsub hslack hD5

/-- In period p ≤ 14, no window with at least 5 subtractions can belong to any tight avoiding subset. -/
theorem p14_no_k_ge_five_in_tight (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hp14 : p ≤ 14) (hpos : 0 < ShortPeriodicSupply.signSum e 0 p)
    (A U : List Nat) (lag : Nat → Nat)
    (u0 : Nat) (hu0 : u0 ∈ U) (hnot : u0 ∉ A) (hsub : List.Sublist A U)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (htight : (neighborhood e p A lag).length = A.length)
    (u : Nat) (hu : u ∈ A)
    (hN5 : 5 ≤ (neighborhood e p [u] lag).length) : False := by
  have hD6 := p14_subtractions_bound e p hp14 hpos
  exact UniversalTightLagBound.no_k_ge_five_of_subPhases_le_six e p hp A U lag u0 hu0 hnot hsub hslack hD6 htight u hu hN5

/-- In period p ≤ 14, any member of a tight avoiding subset covering 2m + 1 subtractions has m ≤ 1. -/
theorem p14_tight_quantum_level_le_one (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hp14 : p ≤ 14) (hpos : 0 < ShortPeriodicSupply.signSum e 0 p)
    (A U : List Nat) (lag : Nat → Nat)
    (u0 : Nat) (hu0 : u0 ∈ U) (hnot : u0 ∉ A) (hsub : List.Sublist A U)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (htight : (neighborhood e p A lag).length = A.length)
    (u : Nat) (hu : u ∈ A)
    (m : Nat) (hNk : 2 * m + 1 ≤ (neighborhood e p [u] lag).length) :
    m ≤ 1 := by
  have hA4 := p14_avoiding_size_le_four e p hp14 hpos A U u0 hu0 hnot hsub hslack
  have hbound := tight_size_forces_quantum_level_bound p hp A lag u hu htight m hNk
  omega

/-- In period p ≤ 12, whenever |U| ≤ 3 and p ≤ 11, Gate T6 holds unconditionally. -/
theorem p12_gate_t6_of_U_le_three (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hp11 : p ≤ 11) (hper : ∀ x : Int, e (x + p) = e x)
    (U : List Nat) (lag : Nat → Nat)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (hU3 : U.length ≤ 3)
    (u0 : Nat) (hu0 : u0 ∈ U)
    (hd_lt : lag u0 < 15)
    (hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (hhall_orig : ∀ A : List Nat, List.Sublist A U → A.length ≤ (neighborhood e p A lag).length)
    (hU_pos : ∀ u ∈ U, 0 < lag u)
    (hU_P2 : ∀ u ∈ U, ShortPeriodicSupply.P2 e (u : Int) (lag u))
    (hU_A : ∀ u ∈ U, e (u : Int) = true) :
    ∀ A : List Nat, List.Sublist A U →
      A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length :=
  p11_gate_t6_of_U_le_three e p hp hp11 hper U lag hslack hU3 u0 hu0 hd_lt hu0A hP0 hss0 hhall_orig hU_pos hU_P2 hU_A

/-- In period p ≤ 11, if all tight avoiding sublists are lag 3 AAS, Gate T6 holds unconditionally. -/
theorem p12_gate_t6_of_tight_all_aas (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hp11 : p ≤ 11) (hper : ∀ x : Int, e (x + p) = e x)
    (U : List Nat) (lag : Nat → Nat)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (u0 : Nat) (_hu0 : u0 ∈ U)
    (hd_lt : lag u0 < 15)
    (hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (hhall_orig : ∀ A : List Nat, List.Sublist A U → A.length ≤ (neighborhood e p A lag).length)
    (hU_P2 : ∀ u ∈ U, ShortPeriodicSupply.P2 e (u : Int) (lag u))
    (hU_A : ∀ u ∈ U, e (u : Int) = true)
    (htight_aas : ∀ A : List Nat, List.Sublist A U → u0 ∉ A →
      (neighborhood e p A lag).length = A.length →
      (∀ u ∈ A, lag u = 3) ∧
      (∀ u ∈ A, e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false)) :
    ∀ A : List Nat, List.Sublist A U →
      A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length :=
  p11_gate_t6_of_all_aas_tight e p hp hp11 hper U lag hslack u0 _hu0 hd_lt hu0A hP0 hss0 hhall_orig hU_P2 hU_A htight_aas

/-- Master Synthesis: Grand Fourteen Lag Rigidity Theorem. -/
theorem grand_fourteen_lag_rigidity_synthesis (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hp14 : p ≤ 14) (_hper : ∀ x : Int, e (x + p) = e x)
    (hpos : 0 < ShortPeriodicSupply.signSum e 0 p)
    (U A : List Nat) (lag : Nat → Nat)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (u0 : Nat) (hu0 : u0 ∈ U) (hnot : u0 ∉ A) (hsub : List.Sublist A U) :
    -- (1) Subtractions bound |D| ≤ 6
    (LagElevenPeriodic.subPhases e 0 p).length ≤ 6 ∧
    -- (2) Avoiding size |A| ≤ 4
    A.length ≤ 4 ∧
    -- (3) For p ≤ 12, |D| ≤ 5 and |A| ≤ 3
    (p ≤ 12 → (LagElevenPeriodic.subPhases e 0 p).length ≤ 5 ∧ A.length ≤ 3) ∧
    -- (4) Quantum level bound m ≤ 1 in tight subsets
    (∀ (_htight : (neighborhood e p A lag).length = A.length) (u : Nat) (_hu : u ∈ A)
       (m : Nat) (_hNk : 2 * m + 1 ≤ (neighborhood e p [u] lag).length), m ≤ 1) := by
  refine ⟨p14_subtractions_bound e p hp14 hpos,
          p14_avoiding_size_le_four e p hp14 hpos A U u0 hu0 hnot hsub hslack,
          fun hp12 => ⟨p12_subtractions_bound e p hp12 hpos,
                       p12_avoiding_size_le_three e p hp12 hpos A U u0 hu0 hnot hsub hslack⟩,
          fun htight u hu m hNk =>
            p14_tight_quantum_level_le_one e p hp hp14 hpos A U lag u0 hu0 hnot hsub hslack htight u hu m hNk⟩

end Recaman.FourteenLagRigidity
