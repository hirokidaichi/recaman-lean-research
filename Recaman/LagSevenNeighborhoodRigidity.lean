import Recaman.TwelveGateT6Resolution
import Recaman.FourteenLagRigidity
import Recaman.TightTripleRigidity
import Recaman.LagSevenTightObstruction
import Recaman.TwoSSEndpoint

/-!
# LagSevenNeighborhoodRigidity: Lag 7 Neighborhood Uniqueness and Tight Triple Quantum Rigidity

This module establishes the quantum moment invariants and neighborhood rigidity of lag 7 windows:

1. `lag7_p2_offset_sum_fourteen`: Every length 7 P2 word has the sum of its subtraction offsets
   equal to 14: `∀ w ∈ (bitWords 7).filter (fun w => decide (P2 w)), subOffsetSum w = 14`.
2. `subOffsetSum_eq_fourteen_of_p2`: For any word `w` of length 7 with `P2 w`, its subtraction
   offset sum is identically 14.
3. `lag7_past_offset_sum_fourteen`: For any lag 7 P2 window at addition `u`, the sum of subtraction
   offsets in `past e u 7` is identically 14.
4. `coprime_three_injective_p11`: Residue injectivity of multiplication by 3 modulo 11.
5. `coprime_three_injective_p13`: Residue injectivity of multiplication by 3 modulo 13.
6. `coprime_three_injective_p14`: Residue injectivity of multiplication by 3 modulo 14.
7. `tight_triple_at_most_one_lag_seven_of_no_shared`: In any tight subset `A` of size 3,
   if no two distinct elements share identical lag 7 neighborhoods, then at most one member
   can have lag 7.
8. `tight_triple_lag_three_count_ge_two`: In any tight triple `A` with distinct elements where
   quantum lags are in `{3, 7}` and at most one has lag 7, at least two distinct elements have lag 3.
9. `tight_triple_retains_two_phases`: Any tight triple containing two distinct lag 3 AAS
   windows retains at least 2 subtraction phases after deleting the donated subtraction `s*(u₀)`.
10. `grand_lag_seven_neighborhood_rigidity_synthesis`: Master synthesis theorem for lag 7
    neighborhood rigidity and tight triple quantum bounds.
-/

namespace Recaman.LagSevenNeighborhoodRigidity

open LeadingRunSupply LowSSEndpoint TwoSSEndpoint P2ModFourRigidity
open TwoSSTightDisjoint TwoSSPeriodicSupply TwoSSLocalDonation TwoSSAvoidTight
open WrapObstruction TightBottleneckBound TwoSSSmallCapacityClosure TightComponentSlackBound
open UniversalTightLagBound TightP2ParityRigidity TwoSSTightAvoidanceTheorem
open SS2AASCollisionObstruction ElevenSSDonationClosure LagSevenTightObstruction
open UniversalGateT6Closure QuantumP2Arithmetic OneSSMultiplicity TightPeriodStratification
open TenGateT6Resolution GrandPeriodicDeletabilityTheorem LowSSPeriodicSupply
open ElevenCapacityRigidity CapacitySlackCompensation ElevenGateT6Synthesis
open FourteenLagRigidity TwelveGateT6Resolution TightTripleRigidity

def subOffsets (w : List Bool) : List Nat :=
  ((List.range w.length).filter (fun i => !(w.getD i true))).map (· + 1)

def subOffsetSum (w : List Bool) : Nat :=
  (subOffsets w).sum

/-- Discrete quantum moment invariant: every length 7 P2 word has subtraction offset sum equal to 14. -/
theorem lag7_p2_offset_sum_fourteen :
    ∀ w ∈ (bitWords 7).filter (fun w => decide (P2 w)), subOffsetSum w = 14 := by
  decide

/-- For any word w of length 7 satisfying P2, its subtraction offset sum is 14. -/
theorem subOffsetSum_eq_fourteen_of_p2 (w : List Bool) (hlen : w.length = 7) (hP : P2 w) :
    subOffsetSum w = 14 := by
  have hmem : w ∈ bitWords 7 := by
    have hm := mem_bitWords w
    rw [hlen] at hm
    exact hm
  have hfilt : w ∈ (bitWords 7).filter (fun w => decide (P2 w)) := by
    rw [List.mem_filter]
    exact ⟨hmem, by simp [hP]⟩
  exact lag7_p2_offset_sum_fourteen w hfilt

/-- For any lag 7 P2 window in a stream e, the subtraction offset sum in past e u 7 is 14. -/
theorem lag7_past_offset_sum_fourteen (e : Int → Bool) (u : Int)
    (hP : ShortPeriodicSupply.P2 e u 7) :
    subOffsetSum (past e u 7) = 14 :=
  subOffsetSum_eq_fourteen_of_p2 (past e u 7) (past_length e u 7) ((past_p2_iff e u 7).mpr hP)

/-- Residue injectivity of multiplication by 3 modulo 11. -/
theorem coprime_three_injective_p11 (u1 u2 : Nat) (hu1 : u1 < 11) (hu2 : u2 < 11)
    (hcong : (3 * ((u1 : Int) - (u2 : Int))) % 11 = 0) :
    u1 = u2 := by
  omega

/-- Residue injectivity of multiplication by 3 modulo 13. -/
theorem coprime_three_injective_p13 (u1 u2 : Nat) (hu1 : u1 < 13) (hu2 : u2 < 13)
    (hcong : (3 * ((u1 : Int) - (u2 : Int))) % 13 = 0) :
    u1 = u2 := by
  omega

/-- Residue injectivity of multiplication by 3 modulo 14. -/
theorem coprime_three_injective_p14 (u1 u2 : Nat) (hu1 : u1 < 14) (hu2 : u2 < 14)
    (hcong : (3 * ((u1 : Int) - (u2 : Int))) % 14 = 0) :
    u1 = u2 := by
  omega

/-- In any tight subset A of size 3, if no two distinct elements can both achieve
maximal lag 7 neighborhood size 3, then at most one member can have lag 7. -/
theorem tight_triple_at_most_one_lag_seven_of_no_both_three (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (A : List Nat) (lag : Nat → Nat)
    (hA3 : A.length = 3)
    (htight : (neighborhood e p A lag).length = 3)
    (hp_gt : 7 < p)
    (hP : ∀ u ∈ A, lag u = 7 → ShortPeriodicSupply.P2 e (u : Int) 7)
    (hno_both_three : ∀ u v, u ∈ A → v ∈ A → u ≠ v → lag u = 7 → lag v = 7 →
      ¬ ((neighborhood e p [u] lag).length = 3 ∧ (neighborhood e p [v] lag).length = 3)) :
    ∀ u v, u ∈ A → v ∈ A → u ≠ v → lag u = 7 → lag v ≠ 7 := by
  intro u v hu hv hne hlu hlv
  have hPu := hP u hu hlu
  have hPv := hP v hv hlv
  have h_shared := tight_triple_two_lag_seven_identical_neighborhoods e p hp hper A lag hA3 htight u v hu hv hlu hlv hp_gt hPu hPv
  exact (hno_both_three u v hu hv hne hlu hlv h_shared).elim

theorem list_len_three_cases {α : Type} (l : List α) (hlen : l.length = 3) :
    ∃ x y z : α, l = [x, y, z] := by
  rcases l with _ | ⟨x, _ | ⟨y, _ | ⟨z, _ | _⟩⟩⟩ <;> revert hlen <;> simp

/-- In any tight triple A with distinct elements where quantum lags are in {3, 7}
and at most one has lag 7, at least two distinct elements must have lag 3. -/
theorem tight_triple_lag_three_count_ge_two (A : List Nat) (hlen : A.length = 3) (hnodup : A.Nodup)
    (lag : Nat → Nat)
    (hlags : ∀ u ∈ A, lag u = 3 ∨ lag u = 7)
    (h_at_most_one_7 : ∀ u v, u ∈ A → v ∈ A → u ≠ v → lag u = 7 → lag v ≠ 7) :
    ∃ u v, u ∈ A ∧ v ∈ A ∧ u ≠ v ∧ lag u = 3 ∧ lag v = 3 := by
  obtain ⟨x, y, z, rfl⟩ := list_len_three_cases A hlen
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or] at hnodup
  rcases hnodup with ⟨⟨hxy, hxz⟩, hyz, _⟩
  have hx := hlags x (by simp)
  have hy := hlags y (by simp)
  have hz := hlags z (by simp)
  rcases hx with hx3 | hx7
  · rcases hy with hy3 | hy7
    · refine ⟨x, y, by simp, by simp, hxy, hx3, hy3⟩
    · rcases hz with hz3 | hz7
      · refine ⟨x, z, by simp, by simp, hxz, hx3, hz3⟩
      · exfalso
        have := h_at_most_one_7 y z (by simp) (by simp) hyz hy7
        exact this hz7
  · rcases hy with hy3 | hy7
    · rcases hz with hz3 | hz7
      · refine ⟨y, z, by simp, by simp, hyz, hy3, hz3⟩
      · exfalso
        have := h_at_most_one_7 x z (by simp) (by simp) hxz hx7
        exact this hz7
    · exfalso
      have := h_at_most_one_7 x y (by simp) (by simp) hxy hx7
      exact this hy7

/-- In any tight triple containing two distinct lag 3 AAS additions, both of their endpoint
phases belong to N(A) and are strictly avoided by s*(u₀). -/
theorem tight_triple_retains_two_phases (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (A : List Nat) (lag : Nat → Nat)
    (u0 : Nat) (hd_lt : lag u0 < 15)
    (hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (v1 v2 : Nat) (hv1 : v1 ∈ A) (hv2 : v2 ∈ A)
    (hl1 : lag v1 = 3) (hl2 : lag v2 = 3)
    (haas1 : e ((v1 : Int) - 1) = true ∧ e ((v1 : Int) - 2) = true ∧ e ((v1 : Int) - 3) = false)
    (haas2 : e ((v2 : Int) - 1) = true ∧ e ((v2 : Int) - 2) = true ∧ e ((v2 : Int) - 3) = false)
    (hP1 : ShortPeriodicSupply.P2 e (v1 : Int) 3)
    (hP2 : ShortPeriodicSupply.P2 e (v2 : Int) 3)
    (hv1A : e (v1 : Int) = true) (hv2A : e (v2 : Int) = true) :
    endpointPhase p (v1 : Int) 3 ∈ neighborhood e p A lag ∧
    endpointPhase p (v2 : Int) 3 ∈ neighborhood e p A lag ∧
    oldestSubtractionPhase p u0 (lag u0) ≠ endpointPhase p (v1 : Int) 3 ∧
    oldestSubtractionPhase p u0 (lag u0) ≠ endpointPhase p (v2 : Int) 3 := by
  have he1 := aas_endpoint_mem_neighborhood e p hp hper A lag v1 hv1 hl1 haas1
  have he2 := aas_endpoint_mem_neighborhood e p hp hper A lag v2 hv2 hl2 haas2
  have hd1 := ss2_donor_disjoint_from_aas_endpoint e p hp hper u0 v1 lag hd_lt hu0A hv1A hP0 hss0 hP1 haas1
  have hd2 := ss2_donor_disjoint_from_aas_endpoint e p hp hper u0 v2 lag hd_lt hu0A hv2A hP0 hss0 hP2 haas2
  exact ⟨he1, he2, hd1, hd2⟩

/-- Master Synthesis: Lag 7 Neighborhood Rigidity and Tight Triple Quantum Bounds. -/
theorem grand_lag_seven_neighborhood_rigidity_synthesis
    (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (A : List Nat) (lag : Nat → Nat)
    (hA3 : A.length = 3) (hnodup : A.Nodup)
    (htight : (neighborhood e p A lag).length = 3)
    (hp_gt : 7 < p)
    (hP_A : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u))
    (hlags : ∀ u ∈ A, lag u = 3 ∨ lag u = 7)
    (hno_both_three : ∀ u v, u ∈ A → v ∈ A → u ≠ v → lag u = 7 → lag v = 7 →
      ¬ ((neighborhood e p [u] lag).length = 3 ∧ (neighborhood e p [v] lag).length = 3)) :
    -- (1) At most one lag 7 element in A
    (∀ u v, u ∈ A → v ∈ A → u ≠ v → lag u = 7 → lag v ≠ 7) ∧
    -- (2) Existence of at least two distinct lag 3 elements in A
    (∃ u v, u ∈ A ∧ v ∈ A ∧ u ≠ v ∧ lag u = 3 ∧ lag v = 3) := by
  have h_at_most_one := tight_triple_at_most_one_lag_seven_of_no_both_three e p hp hper A lag hA3 htight hp_gt
    (fun u hu hlu => by have := hP_A u hu; rwa [hlu] at this) hno_both_three
  have h_two_lag3 := tight_triple_lag_three_count_ge_two A hA3 hnodup lag hlags h_at_most_one
  exact ⟨h_at_most_one, h_two_lag3⟩

end Recaman.LagSevenNeighborhoodRigidity

