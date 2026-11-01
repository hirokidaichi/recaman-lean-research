import Recaman.OldTargetClockCollision

namespace Recaman.OldTargetMiddleCharge

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.ASourceReuse
open Recaman.RunClockClassifier Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.SourceFamilyFreeCount Recaman.OldTargetLocalTail Recaman.OldTargetClockCollision
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- A middle-S source supplying the final band of the last A ray charges
at least j+1 A signs to the first run. All word lengths are unrestricted. -/
theorem middle_S_tail_first_run (u : List Bool) (hu : BlockWord u)
    (h M m L s i T j q : Nat) (hq : q≤m) (hj : 2≤j) (hband : T≤i+j)
    (hm1 : mass (List.replicate q false++List.replicate L true++List.replicate s false)+(i : Int)=1)
    (hk1 : runKey (List.replicate q false++List.replicate L true++List.replicate s false)= -2)
    (hm2 : mass (u++List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate T true++List.replicate j false)=1)
    (ha2 : areaW (u++List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate T true++List.replicate j false)=0) : j+1≤M := by
  let a := m-q
  let U := u++List.replicate h false++List.replicate M true++List.replicate a false
  let v := List.replicate q false++List.replicate L true++List.replicate s false
  let C := mass u
  let H : Int := (h : Int)+(a : Int)
  let R : Int := (j : Int)+1
  have ha : a+q=m := by dsimp [a]; omega
  have hsplit : U++v++List.replicate T true++List.replicate j false=
      u++List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate T true++List.replicate j false := by
    simp only [U,v,List.append_assoc]
    rw [←List.append_assoc (List.replicate a false) (List.replicate q false),
      List.replicate_append_replicate,ha]
  have hk := source_key_before_gap (U++v) T j (by simpa only [hsplit] using hm2)
    (by simpa only [hsplit] using ha2)
  have hv : runKey v= -2 := hk1
  have hmU : 0≤mass U := by
    simp only [mass_append,mass_rep_false,mass_replicate_A] at hm1 hm2
    simp only [U,mass_append,mass_rep_false,mass_replicate_A]
    have hcast : (a : Int)+(q : Int)=(m : Int) := by omega
    omega
  have hC := block_mass_nonnegative hu
  change 0≤C at hC
  have hlow := block_area_quadratic_lower hu
  have hku : -2≤runKey u := by unfold runKey; omega
  have hmassU : mass U=C+(M : Int)-H := by
    simp only [U,mass_append,mass_rep_false,mass_replicate_A]
    dsimp [C,H]
    omega
  have hkeyU : runKey U=runKey u+2*C^2-2*(H-C)^2+4*(M : Int)*(a : Int) := by
    dsimp [U]
    rw [runKey_append_S,runKey_append_A,runKey_append_S]
    simp only [mass_append,mass_rep_false,mass_replicate_A]
    dsimp [C,H]
    grind
  have hsq : (H-C)^2≤C^2+(M : Int)^2 := by
    by_cases hh : H≤C
    · have hp := Int.mul_nonneg (show 0≤H by dsimp [H]; omega) (show 0≤2*C-H by omega)
      have hMM := Int.mul_self_nonneg (M : Int)
      grind
    · have hp := Int.mul_nonneg (show 0≤(M : Int)-(H-C) by omega)
        (show 0≤(M : Int)+(H-C) by omega)
      have hCC := Int.mul_self_nonneg C
      grind
  have hMa := Int.mul_nonneg (show 0≤(M : Int) by omega) (show 0≤(a : Int) by omega)
  have hUlow : -2-2*(M : Int)^2≤runKey U := by grind
  rw [runKey_append,hv] at hk
  have hcross := Int.mul_nonneg hmU (show 0≤(cntF v : Int) by omega)
  have hquad : R^2≤(M : Int)^2+2 := by dsimp [R]; grind
  have hR : 3≤R := by dsimp [R]; omega
  by_cases hh : j+1≤M
  · exact hh
  · exfalso
    have hp := Int.mul_nonneg (show 0≤R-1-(M : Int) by dsimp [R]; omega)
      (show 0≤R-1+(M : Int) by omega)
    grind

end Recaman.OldTargetMiddleCharge
