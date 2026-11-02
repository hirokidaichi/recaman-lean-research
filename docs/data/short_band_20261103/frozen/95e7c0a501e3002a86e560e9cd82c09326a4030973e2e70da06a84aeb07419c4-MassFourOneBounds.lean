import Recaman.ShortCounterWeightedCounts
import Recaman.ShortCounterJointQuadratic
import Recaman.MassFourOneArithmetic
import Recaman.S15SecondExclusion
import Recaman.SecondRaySmallShapes
import Recaman.FirstTwoActualBounds
import Recaman.ShortCounterSourceCounts
import Recaman.ShortCounterJointCuts

namespace Recaman.MassFourOneBounds

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- Same original-history source charging strictly reduces the remaining C4/S1 counter parameters. -/
theorem mass_four_one_bounds (f : Nat → Bool) (n t h M m L s U v T j C : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w) (ht : t<n)
    (hh : 1≤h) (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hU : 1≤U)
    (hv : v=1) (hC4 : C=4)
    (hzeroMass : M+L+U=h+m+s)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ k, k<M → f (n+h+k)=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → f x=false)
    (hA2 : ∀ k, k<L → f (n+h+M+m+k)=true)
    (hS3 : ∀ x, n+h+M+m+L≤x → x<n+h+M+m+L+s → f x=false)
    (hA3 : ∀ k, k<U → f (n+h+M+m+L+s+k)=true)
    (hS4 : ∀ x, n+h+M+m+L+s+U≤x → x<n+h+M+m+L+s+U+v → f x=false)
    (hA4 : ∀ k, k<T → f (n+h+M+m+L+s+U+v+k)=true)
    (hgap : ∀ x, n+h+M+m+L+s+U+v+T≤x → x<n+h+M+m+L+s+U+v+T+j → f x=false)
    (htarget : Win f t (n+h+M+m+L+s+U+v+T+j-t))
    (hC : mass (w.drop t)=(C : Int))
    (hpos : ∀ k, 0<k → k≤h+M+m+L+s+U+v+T →
      cN (EndN f 0) n k+1≤cN (fun x=>f x=false) n k)
    (hbad : cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)<j+1) :
    j+1≤7 ∧ h+m+s≤14 := by
  subst C
  subst v
  have hb:=Recaman.ShortTargetCounter.short_target_counter f n t h M m L s U 1 T j 4 w hw hpre ht
    hh hM hm hL hs hU (by omega) (by omega) (by omega) hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad
  have hj:=Recaman.ShortCounterJointCounts.short_counter_joint_counts f n t h M m L s U 1 T j 4 w hw hpre ht
    hh hM hm hL hs hU (by omega) (by omega) (by omega) hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad
  have hwc:=Recaman.ShortCounterWeightedCounts.short_counter_weighted_counts f n t h M m L s U 1 T j 4 w hw hpre ht
    hh hM hm hL hs hU (by omega) (by omega) (by omega) hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad
  have hcuts:=Recaman.ShortCounterParameterCuts.short_counter_parameter_cuts f n t h M m L s U 1 T j 4 w hw hpre ht
    hh hM hm hL hs hU (by omega) (by omega) (by omega) hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad
  have hq:=Recaman.ShortCounterJointQuadratic.short_counter_joint_quadratic f n t h M m L s U 1 T j 4 w hw hpre ht
    hh hM hm hL hs hU (by omega) (by omega) (by omega) hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad
  let K: Int:=(M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int)
  have hWM : (M : Int)+(L : Int)+(M : Int)≤K := by
    have h1:=Int.mul_nonneg (show 0≤(M : Int) by omega) (show 0≤(m : Int)+(s : Int)-2 by omega)
    have h2:=Int.mul_nonneg (show 0≤(L : Int) by omega) (show 0≤(s : Int)-1 by omega)
    have he : K-(2*(M : Int)+(L : Int))=
        (M : Int)*((m : Int)+(s : Int)-2)+(L : Int)*((s : Int)-1) := by dsimp [K]; grind only
    omega
  have hraw:=Recaman.ShortCounterJointQuadratic.short_counter_cross_circle f n t h M m L s U 1 T j 4 w hw hpre ht
    hh hM hm hL hs hU (by omega) (by omega) (by omega) hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad
  change ((j : Int)+1)^2+(4 : Int)^2+2*4*1-1^2-1+2*K≤
    (((h : Int)+(m : Int)+(s : Int))-4)^2 at hraw
  have hcircle : ((j : Int)+1)^2+22+2*K≤(((h : Int)+(m : Int)+(s : Int))-4)^2 := by omega
  have hsrc : 1+2≤4 ∨ M≠j+2 := Or.inl (by omega)
  have hjoint:=Recaman.ShortCounterSourceCounts.short_counter_source_weighted_count f n t h M m L s U 1 T j 4 w hw hpre ht
    hh hM hm hL hs hU (by omega) (by omega) (by omega) hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad hsrc
  have hS15 : h+m+s≤15 := by
    have hx:=Recaman.ShortCounterSourceCounts.short_counter_source_head_count f n t h M m L s U 1 T j 4 w hw hpre ht
      hh hM hm hL hs hU (by omega) (by omega) (by omega) hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad hsrc
    omega
  have hbudget (hcond : M≤3 ∨ 2*M≤h+3) : h+m+s≤14 := by
    have hhead9 : cN (EndN f 0) n (h+M+m+L+s+U)≤9 := by
      rcases hcond with hM3 | hlong
      · exact Recaman.OldTargetFirstRun.three_run_count_small_first f n h M m L s U w hw hpre hM3 hs
          (by omega) hS hA hS2 hA2 hS3 hA3 (fun k hk hkB=>hpos k hk (by omega))
      · exact Recaman.HeadRunCountBounds.head_long_first_nine f n h M m L s U w hw hpre hM hm hL hs hU
          (by omega) hS hA hS2 hA2 hS3 hA3 (fun k hk hkB=>hpos k hk (by omega)) hlong
    have hx:=Recaman.ShortCounterSourceCounts.short_counter_source_head_budget f n t h M m L s U 1 T j 4 w hw hpre ht
      hh hM hm hL hs hU (by omega) (by omega) (by omega) hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad hsrc 9 hhead9
    omega
  have hR7 : j+1≤7 := by
    have hx:=Recaman.MassFourOneArithmetic.large_R_excluded
      ((h : Int)+(m : Int)+(s : Int)) ((j : Int)+1) (M : Int) (h : Int) (m : Int) (s : Int) (L : Int) ((M : Int)+(L : Int)) K
      (by have hx:=hcuts.1; omega) (by omega) (by have hx:=hb.2.1; omega)
      (by omega) (by omega) (by omega) (by omega) rfl rfl (by have hx:=hjoint.1; omega) hWM rfl
      (by intro hc; have hx:=hbudget (by omega); omega) hcircle
    omega
  refine ⟨hR7,?_⟩
  by_cases hS14 : h+m+s≤14
  · exact hS14
  have hSeq : h+m+s=15 := by omega
  have hres:=Recaman.MassFourOneArithmetic.S15_residual
    ((h : Int)+(m : Int)+(s : Int)) ((j : Int)+1) (M : Int) (h : Int) (m : Int) (s : Int) (L : Int) ((M : Int)+(L : Int)) K
    (by omega) (by have hx:=hb.2.1; omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by have hx:=hb.2.2.1; omega) rfl rfl rfl
    (by intro hc; have hx:=hbudget (by omega); omega) hcircle
  have hsecond:=Recaman.S15SecondExclusion.S15_second_actual_zero f n h M m L w hw hpre hS hA hS2 hA2
    (by omega) (by omega) (by omega) (by omega)
  have hp1 : seg f 0 (n+h)=w++List.replicate h false := by
    rw [seg_add,Nat.zero_add,hpre,seg_false f n h hS]
  have hefirst:=endable_A_run_count f (n+h) M _ hp1 hA
  have hf2:=block_rayCount_after_S hw h M
  have heprefix:=Recaman.HeadRunSupplyBudgets.two_prefix_count f n h M m L hS hS2
  let J:=h+M+m+L
  let P:=fun x=>f x=true ∧ ¬EndN f 0 x
  have hprefix : cN (EndN f 0) n J≤2 := by dsimp [J]; omega
  have hAcount : cN (fun x=>f x=true) n J=M+L := by
    have hc:=ones_seg_eq_count f n (h+M+m+L)
    have hw2:=Recaman.SeparatorSupplyReset.three_run_word f n h M m L 0 0 hS hA hS2 hA2
      (by intro x hx hxB; omega) (by intro i hi; omega)
    simp only [Nat.add_zero,List.replicate_zero,List.append_nil] at hw2
    rw [hw2] at hc
    simp only [ones_append,ones_replicate_A,ones_replicate_S] at hc
    dsimp [J]
    omega
  have hpart:=addition_endable_partition f n J
  rw [hAcount] at hpart
  change M+L=cN (EndN f 0) n J+cN P n J at hpart
  have hfree:=cN_add P n J (s+U+1+T)
  change cN P n (h+M+m+L+s+U+1+T)<j+1 at hbad
  simp only [J,Nat.add_assoc] at hfree hpart hprefix hbad
  omega
end Recaman.MassFourOneBounds
