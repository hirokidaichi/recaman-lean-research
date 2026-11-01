import Recaman.ASourceReuse
import Recaman.SourceFamilyFreeCount

namespace Recaman.ThreeRunSourceShape

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.RunSupplyKeys Recaman.TwoRunSupply Recaman.RunSupplyBudget
open Recaman.BlockOldRay Recaman.ThreeRunSupplyBudget Recaman.SourceFamilyFreeCount
open Recaman.ASourceReuse
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- A target window starting in the first A run has a strictly larger
    internal S sum than j+1. All run lengths are quantified. -/
theorem first_A_target_equations (d m L s T j : Nat) (hd : 1≤d) (hm : 1≤m)
    (hmass : mass (List.replicate d true++List.replicate m false++List.replicate L true++
      List.replicate s false++List.replicate T true++List.replicate j false)=1)
    (harea : areaW (List.replicate d true++List.replicate m false++List.replicate L true++
      List.replicate s false++List.replicate T true++List.replicate j false)=0) :
    d+L+T=m+s+j+1 ∧
      2*(d : Int)*((m : Int)+(s : Int))+2*(L : Int)*(s : Int)=
        ((m : Int)+(s : Int))^2-((j : Int)+1)^2 ∧ j+1<m+s := by
  have hkey := source_key_before_gap
    (List.replicate d true++List.replicate m false++List.replicate L true++List.replicate s false)
    T j hmass harea
  have he := runKey_five_runs 0 d m L s
  simp only [List.replicate_zero,List.nil_append] at he
  rw [he] at hkey
  simp only [mass_append,mass_replicate_A,mass_rep_false] at hmass
  have hpos := Int.mul_pos (show 0<2*(d : Int) by omega)
    (show 0<(m : Int)+(s : Int) by omega)
  have hnonneg := Int.mul_nonneg (show 0≤2*(L : Int) by omega) (show 0≤(s : Int) by omega)
  have hs : j+1<m+s := by
    by_cases h : j+1<m+s
    · exact h
    · have hp := Int.mul_nonneg (show 0≤(j : Int)+1-((m : Int)+(s : Int)) by omega)
        (show 0≤(j : Int)+1+((m : Int)+(s : Int)) by omega)
      grind
  refine ⟨by omega,by grind,hs⟩

theorem first_A_target_residual (M d m L s T j : Nat) (hd : 1≤d) (hdM : d≤M)
    (hm : 1≤m) (hbudget : M+L+T≤20)
    (hmass : mass (List.replicate d true++List.replicate m false++List.replicate L true++
      List.replicate s false++List.replicate T true++List.replicate j false)=1)
    (harea : areaW (List.replicate d true++List.replicate m false++List.replicate L true++
      List.replicate s false++List.replicate T true++List.replicate j false)=0) :
    j+2≤m+s ∧ m+s+j+1≤20 ∧ j≤8 := by
  have he := first_A_target_equations d m L s T j hd hm hmass harea
  omega

/-- This is the same actual P2 window from the same sign sequence;
    the whole first block M may include signs before its source. -/
theorem actual_first_A_target_residual (f : Nat → Bool) (t M d m L s T j : Nat)
    (hd : 1≤d) (hdM : d≤M) (hm : 1≤m) (hbudget : M+L+T≤20)
    (hword : seg f t (d+m+L+s+T+j)=
      List.replicate d true++List.replicate m false++List.replicate L true++
      List.replicate s false++List.replicate T true++List.replicate j false)
    (hwin : Win f t (d+m+L+s+T+j)) :
    j+2≤m+s ∧ m+s+j+1≤20 ∧ j≤8 := by
  have hmass := seg_mass f t (d+m+L+s+T+j)
  have harea := Ar_areaW f t (d+m+L+s+T+j)
  rw [hword] at hmass harea
  exact first_A_target_residual M d m L s T j hd hdM hm hbudget
    (by rw [hmass]; exact hwin.2.1) (by rw [←harea]; exact hwin.2.2)

/-- The second-S source has an even smaller A-free preceding context.
    Its target square and balance share exactly the same suffix. -/
theorem middle_S_target_equations (q L s T j : Nat) (hL : 1≤L) (hs : 1≤s)
    (hmass : mass (List.replicate q false++List.replicate L true++
      List.replicate s false++List.replicate T true++List.replicate j false)=1)
    (harea : areaW (List.replicate q false++List.replicate L true++
      List.replicate s false++List.replicate T true++List.replicate j false)=0) :
    L+T=q+s+j+1 ∧
      ((q : Int)+(s : Int))^2-((j : Int)+1)^2=2*(L : Int)*(s : Int) ∧ j+1<q+s := by
  have hkey := source_key_before_gap
    (List.replicate q false++List.replicate L true++List.replicate s false) T j hmass harea
  rw [runKey_S_A_S] at hkey
  simp only [mass_append,mass_rep_false,mass_replicate_A] at hmass
  have hpos := Int.mul_pos (show 0<2*(L : Int) by omega) (show 0<(s : Int) by omega)
  have hqs : j+1<q+s := by
    by_cases h : j+1<q+s
    · exact h
    · have hp := Int.mul_nonneg (show 0≤(j : Int)+1-((q : Int)+(s : Int)) by omega)
        (show 0≤(j : Int)+1+((q : Int)+(s : Int)) by omega)
      grind
  exact ⟨by omega,by grind,hqs⟩

end Recaman.ThreeRunSourceShape
