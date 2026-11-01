import Recaman.OldTargetLocalTail

namespace Recaman.OldTargetClockCollision

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.ASourceReuse
open Recaman.RunClockClassifier Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.SourceFamilyFreeCount Recaman.OldTargetLocalTail
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

private theorem cntF_A (k : Nat) : cntF (List.replicate k true)=0 := by
  have hc := cntF_int (List.replicate k true)
  rw [List.length_replicate,ones_replicate_A] at hc
  omega

/-- A first-A local source in the final band forces an extra m+s
A signs in the same old target's total A budget. No finite cutoff. -/
theorem first_A_tail_A_budget (u : List Bool) (hu : BlockWord u) (hne : u≠[])
    (h M m L s i T j e : Nat) (hj : 2≤j) (hband : T≤i+j)
    (hm1 : mass (List.replicate e true++List.replicate m false++List.replicate L true++
      List.replicate s false)+(i : Int)=1)
    (hk1 : runKey (List.replicate e true++List.replicate m false++List.replicate L true++
      List.replicate s false)= -2)
    (hm2 : mass (u++List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate T true++List.replicate j false)=1)
    (ha2 : areaW (u++List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate T true++List.replicate j false)=0) :
    2*(j+1)+(m+s)≤M+L+T := by
  let C := mass u
  let R : Int := (j : Int)+1
  let K : Int := (m : Int)+(s : Int)
  let v := List.replicate m false++List.replicate L true++List.replicate s false
  have hC : 1≤C := (sufPos_block hu [] u rfl hne).1
  have hlow := block_area_quadratic_lower hu
  have hku : -2≤runKey u := by unfold runKey; omega
  have hp : 0≤C-(h : Int)+(M : Int)-(e : Int) := by
    simp only [mass_append,mass_rep_false,mass_replicate_A] at hm1 hm2
    dsimp [C]
    omega
  have hcnt : (cntF v : Int)=K := by
    simp only [v,cntF_append,cntF_replicate_S,cntF_A,Int.natCast_add]
    dsimp [K]
    omega
  have hk := source_key_before_gap
    (u++List.replicate h false++List.replicate M true++v) T j
    (by simpa only [v,List.append_assoc] using hm2)
    (by simpa only [v,List.append_assoc] using ha2)
  have hl : runKey (List.replicate e true++v)= -2 := by
    simpa only [v,List.append_assoc] using hk1
  rw [runKey_prepend_A,hcnt] at hl
  rw [runKey_append,runKey_append_A,runKey_append_S,hcnt] at hk
  simp only [mass_append,mass_rep_false,mass_replicate_A] at hk
  have hnonneg := Int.mul_nonneg hp (show 0≤K by dsimp [K]; omega)
  have hquad : R^2-2≤(h : Int)*((h : Int)-2*C) := by
    dsimp [R,C] at *
    grind
  have hR : 3≤R := by dsimp [R]; omega
  have hhC : C≤(h : Int) := by
    by_cases hh : C≤(h : Int)
    · exact hh
    · have hn := Int.mul_nonpos_of_nonneg_of_nonpos (show 0≤(h : Int) by omega)
        (show (h : Int)-2*C≤0 by omega)
      have hrr := Int.mul_nonneg (show 0≤R-3 by omega) (show 0≤R+3 by omega)
      grind
  have hhR : C+R≤(h : Int) := by
    by_cases hh : C+R≤(h : Int)
    · exact hh
    · have hp1 := Int.mul_nonneg (show 0≤R-1-((h : Int)-C) by omega)
        (show 0≤R-1+((h : Int)-C) by omega)
      have hp2 := Int.mul_nonneg (show 0≤C-1 by omega) (show 0≤C+1 by omega)
      grind
  simp only [mass_append,mass_rep_false,mass_replicate_A] at hm2
  dsimp [C,R] at hhR
  omega

theorem first_A_tail_clock_two (u : List Bool) (hu : BlockWord u) (hne : u≠[])
    (h M m L s i T j e : Nat) (hj : 4≤j) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s)
    (he : 1≤e) (hband : T≤i+j) (hbudget : M+L+T≤j+10)
    (hm1 : mass (List.replicate e true++List.replicate m false++List.replicate L true++
      List.replicate s false)+(i : Int)=1)
    (hk1 : runKey (List.replicate e true++List.replicate m false++List.replicate L true++
      List.replicate s false)= -2)
    (hm2 : mass (u++List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate T true++List.replicate j false)=1)
    (ha2 : areaW (u++List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate T true++List.replicate j false)=0) : i=2 := by
  have hb := first_A_tail_A_budget u hu hne h M m L s i T j e (by omega) hband hm1 hk1 hm2 ha2
  have hK : m+s=2 ∨ m+s=3 ∨ m+s=4 := by omega
  have hkey := runKey_five_runs 0 e m L s
  simp only [List.replicate_zero,List.nil_append] at hkey
  rw [hkey] at hk1
  have hLs := Int.mul_pos (show 0<(L : Int) by omega) (show 0<(s : Int) by omega)
  have heK := Int.mul_nonneg (show 0≤(e : Int)-1 by omega)
    (show 0≤(m : Int)+(s : Int) by omega)
  have heq : 2*(e : Int)*((m : Int)+(s : Int))+2*(L : Int)*(s : Int)=
      ((m : Int)+(s : Int))^2-1 := by grind
  rcases hK with hK|hK|hK
  · have hc : (m : Int)+(s : Int)=2 := by omega
    rw [hc] at heq
    simp only [Int.reducePow,Int.reduceSub] at heq
    omega
  · have hc : (m : Int)+(s : Int)=3 := by omega
    rw [hc] at heq
    simp only [Int.reducePow,Int.reduceSub] at heq
    have he1 : e=1 := by omega
    have hLs1 : (L : Int)*(s : Int)=1 := by subst e; omega
    have hL1 : L=1 := by
      have hp := Int.mul_nonneg (show 0≤(L : Int) by omega) (show 0≤(s : Int)-1 by omega)
      grind
    have hs1 : s=1 := by rw [hL1] at hLs1; simp at hLs1; omega
    simp only [mass_append,mass_rep_false,mass_replicate_A] at hm1
    omega
  · have hc : (m : Int)+(s : Int)=4 := by omega
    rw [hc] at heq
    simp only [Int.reducePow,Int.reduceSub] at heq
    omega

end Recaman.OldTargetClockCollision
