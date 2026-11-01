import Recaman.FourRunSupplyBudget

namespace Recaman.FourRunTargetArea

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.SourceFamilyFreeCount Recaman.ASourceReuse Recaman.RunClockClassifier
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

private theorem cntF_A (k : Nat) : cntF (List.replicate k true)=0 := by
  have hc := cntF_int (List.replicate k true)
  rw [List.length_replicate,ones_replicate_A] at hc
  omega

theorem runKey_seven_runs (h M m L s U v : Nat) :
    runKey (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false)=
    4*((M : Int)*((m : Int)+(s : Int)+(v : Int))+(L : Int)*((s : Int)+(v : Int))+
      (U : Int)*(v : Int))-2*((h : Int)+(m : Int)+(s : Int)+(v : Int))^2 := by
  rw [runKey_append_S,runKey_append_A,runKey_five_runs]
  simp only [mass_append,mass_rep_false,mass_replicate_A]
  grind

/-- The same old suffix retains its mass and area in the four-run
identity. No mass cap or independent old signatures are used. -/
theorem old_target_area_identity (u : List Bool) (h M m L s U v T j : Nat)
    (hmass : mass (u++List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false++
      List.replicate T true++List.replicate j false)=1)
    (harea : areaW (u++List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false++
      List.replicate T true++List.replicate j false)=0) :
    2*areaW u+mass u*(mass u-1)=
      2*((M : Int)+(L : Int)+(U : Int)+(T : Int))*
        ((M : Int)+(L : Int)+(U : Int)+(T : Int)-2*((j : Int)+1))-
      4*((M : Int)*((m : Int)+(s : Int)+(v : Int))+
        (L : Int)*((s : Int)+(v : Int))+(U : Int)*(v : Int)) := by
  let b := List.replicate h false++List.replicate M true++List.replicate m false++
    List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false
  have hk := source_key_before_gap (u++b) T j
    (by simpa only [b,List.append_assoc] using hmass)
    (by simpa only [b,List.append_assoc] using harea)
  have hb := runKey_seven_runs h M m L s U v
  have hc : (cntF b : Int)=(h : Int)+(m : Int)+(s : Int)+(v : Int) := by
    simp only [b,cntF_append,cntF_replicate_S,cntF_A,Nat.add_zero,Int.natCast_add]
  rw [runKey_append,hc] at hk
  change runKey b=_ at hb
  rw [hb] at hk
  simp only [mass_append,mass_rep_false,mass_replicate_A] at hmass
  unfold runKey at hk
  grind

/-- A short last ray (forced by a final-S local clock in the final band)
requires two more A signs than twice R=j+1. This strengthens the source
A cut but does not itself prove an actual free-count bound. -/
theorem old_target_short_last_A_budget (u : List Bool) (hu : BlockWord u) (hne : u≠[])
    (h M m L s U v T j : Nat) (hM : 1≤M) (hm : 1≤m) (hL : 1≤L)
    (hs : 1≤s) (hU : 1≤U) (hv : 1≤v) (hshort : T≤j+2)
    (hmass : mass (u++List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false++
      List.replicate T true++List.replicate j false)=1)
    (harea : areaW (u++List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false++
      List.replicate T true++List.replicate j false)=0) :
    2*(j+1)+2≤M+L+U+T := by
  let A : Int := (M : Int)+(L : Int)+(U : Int)+(T : Int)
  let H : Int := (M : Int)+(L : Int)+(U : Int)
  let R : Int := (j : Int)+1
  let I : Int := (M : Int)*((m : Int)+(s : Int)+(v : Int))+
    (L : Int)*((s : Int)+(v : Int))+(U : Int)*(v : Int)
  have he := old_target_area_identity u h M m L s U v T j hmass harea
  have hl := block_area_quadratic_lower hu
  have hC : 1≤mass u := (sufPos_block hu [] u rfl hne).1
  have hb : (mass u)^2+2*I≤A*(A-2*R)+1 := by dsimp [I,A,R]; grind
  have hmprod := Int.mul_nonneg (show 0≤(M : Int) by omega)
    (show 0≤(m : Int)+(s : Int)+(v : Int)-3 by omega)
  have hlprod := Int.mul_nonneg (show 0≤(L : Int) by omega)
    (show 0≤(s : Int)+(v : Int)-2 by omega)
  have huprod := Int.mul_nonneg (show 0≤(U : Int) by omega) (show 0≤(v : Int)-1 by omega)
  have hI : H+3≤I := by dsimp [H,I]; grind
  have hC2 := Int.mul_nonneg (show 0≤mass u-1 by omega) (show 0≤mass u+1 by omega)
  have hA : 0≤A := by dsimp [A]; omega
  have hlarge : 2*R<A := by
    by_cases hh : 2*R<A
    · exact hh
    · have hp := Int.mul_nonpos_of_nonneg_of_nonpos hA (show A-2*R≤0 by omega)
      grind
  by_cases hh : 2*R+2≤A
  · dsimp [A,R] at hh; omega
  · have hAe : A=2*R+1 := by omega
    have hH : R≤H := by dsimp [A,H,R] at *; omega
    rw [hAe] at hb
    grind

/-- A P2 source lying in the immediately preceding S run is clock2. -/
theorem final_S_source_clock (q i : Nat)
    (hm : mass (List.replicate q false++List.replicate i true)=1)
    (ha : areaW (List.replicate q false++List.replicate i true)=0) : q=1 ∧ i=2 := by
  have hk := source_key_before_gap (List.replicate q false) i 0
    (by simpa only [List.replicate_zero,List.append_nil] using hm)
    (by simpa only [List.replicate_zero,List.append_nil] using ha)
  rw [runKey_S] at hk
  have hq : q=1 := by
    by_cases h : q=0
    · rw [h] at hk; simp at hk
    · have hp := Int.mul_nonneg (show 0≤(q : Int)-1 by omega) (show 0≤(q : Int)+1 by omega)
      grind
  simp only [mass_append,mass_rep_false,mass_replicate_A] at hm
  exact ⟨hq,by omega⟩

/-- Sharp raw P2 control for the +2 budget, not a free-gap counterexample. -/
theorem short_last_raw_boundary :
    mass ([true,true]++List.replicate 5 false++[true,false,true,false]++
      List.replicate 3 true++[false]++List.replicate 5 true++List.replicate 3 false)=1 ∧
    areaW ([true,true]++List.replicate 5 false++[true,false,true,false]++
      List.replicate 3 true++[false]++List.replicate 5 true++List.replicate 3 false)=0 ∧
    (1+1+3+5 : Nat)=2*(3+1)+2 := by decide

end Recaman.FourRunTargetArea
