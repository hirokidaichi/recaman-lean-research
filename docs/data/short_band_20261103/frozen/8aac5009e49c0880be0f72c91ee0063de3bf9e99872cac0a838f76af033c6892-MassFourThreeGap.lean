import Recaman.ShortCounterWeightedCounts
import Recaman.ShortCounterJointQuadratic
import Recaman.MassFourThreeArithmetic
import Recaman.HeadSixSevenCount
import Recaman.ShortCounterSourceCounts
import Recaman.ShortCounterJointCuts

namespace Recaman.MassFourThreeGap

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- The mass4/separator3 branch has full actual free-gap at all lengths.
Weighted prefix and run budgets are supplied inside the counter argument. -/
theorem mass_four_three_gap (f : Nat → Bool) (n t h M m L s U v T j C : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w) (ht : t<n)
    (hh : 1≤h) (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hU : 1≤U)
    (hv : v=3) (hC4 : C=4)
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
    : j+1≤cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T) := by
  subst C
  subst v
  by_cases hgood : j+1≤cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+3+T)
  · exact hgood
  have hbad : cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+3+T)<j+1 := by omega
  have hb:=Recaman.ShortTargetCounter.short_target_counter f n t h M m L s U 3 T j 4 w hw hpre ht
    hh hM hm hL hs hU (by omega) (by omega) (by omega) hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad
  have hj:=Recaman.ShortCounterJointCounts.short_counter_joint_counts f n t h M m L s U 3 T j 4 w hw hpre ht
    hh hM hm hL hs hU (by omega) (by omega) (by omega) hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad
  have hwc:=Recaman.ShortCounterWeightedCounts.short_counter_weighted_counts f n t h M m L s U 3 T j 4 w hw hpre ht
    hh hM hm hL hs hU (by omega) (by omega) (by omega) hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad
  have hcuts:=Recaman.ShortCounterParameterCuts.short_counter_parameter_cuts f n t h M m L s U 3 T j 4 w hw hpre ht
    hh hM hm hL hs hU (by omega) (by omega) (by omega) hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad
  have hq:=Recaman.ShortCounterJointQuadratic.short_counter_joint_quadratic f n t h M m L s U 3 T j 4 w hw hpre ht
    hh hM hm hL hs hU (by omega) (by omega) (by omega) hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad
  let K: Int:=(M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int)
  have hWM : (M : Int)+(L : Int)+(M : Int)≤K := by
    have h1:=Int.mul_nonneg (show 0≤(M : Int) by omega) (show 0≤(m : Int)+(s : Int)-2 by omega)
    have h2:=Int.mul_nonneg (show 0≤(L : Int) by omega) (show 0≤(s : Int)-1 by omega)
    have he : K-(2*(M : Int)+(L : Int))=
        (M : Int)*((m : Int)+(s : Int)-2)+(L : Int)*((s : Int)-1) := by dsimp [K]; grind only
    omega
  have hraw:=Recaman.ShortCounterJointQuadratic.short_counter_cross_circle f n t h M m L s U 3 T j 4 w hw hpre ht
    hh hM hm hL hs hU (by omega) (by omega) (by omega) hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad
  change ((j : Int)+1)^2+(4 : Int)^2+2*4*3-3^2-1+2*K≤
    (((h : Int)+(m : Int)+(s : Int))-4)^2 at hraw
  have hcircle : ((j : Int)+1)^2+30+2*K≤(((h : Int)+(m : Int)+(s : Int))-4)^2 := by omega
  have hhead_budget (B : Nat) (hc : cN (EndN f 0) n (h+M+m+L+s+U)≤B) : h+m+s≤j+B := by
    let H:=h+M+m+L+s+U
    let P:=fun x=>f x=true ∧ ¬EndN f 0 x
    have hword:=Recaman.SeparatorSupplyReset.three_run_word f n h M m L s U hS hA hS2 hA2 hS3 hA3
    have hAh : cN (fun x=>f x=true) n H=h+m+s := by
      have hx:=ones_seg_eq_count f n (h+M+m+L+s+U)
      rw [hword] at hx
      simp only [ones_append,ones_replicate_A,ones_replicate_S] at hx
      dsimp [H]
      omega
    have hp:=addition_endable_partition f n H
    rw [hAh] at hp
    change h+m+s=cN (EndN f 0) n H+cN P n H at hp
    have hf:=cN_add P n H (3+T)
    change cN (EndN f 0) n H≤B at hc
    change cN P n (h+M+m+L+s+U+3+T)<j+1 at hbad
    simp only [H,Nat.add_assoc] at hf hc hp hbad
    omega
  have hR7 : j+1≤7 := by
    have hc:=Recaman.ShortCounterJointCuts.short_counter_joint_cuts f n t h M m L s U 3 T j 4 w hw hpre ht
      hh hM hm hL hs hU (by omega) (by omega) (by omega) hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad
    have hx:=hc.2.2.1 (by omega)
    omega
  have hS14 : h+m+s≤14 := by
    have hc:=Recaman.ShortCounterHeadCounts.short_counter_head_counts f n t h M m L s U 3 T j 4 w hw hpre ht
      hh hM hm hL hs hU (by omega) (by omega) (by omega) hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad
    omega
  exfalso
  by_cases hMeq : M=j+2
  · have hlong : 2*M≤h+3 := by
      have hx:=Recaman.MassFourThreeArithmetic.boundary_geometry
        ((h : Int)+(m : Int)+(s : Int)) ((j : Int)+1) (M : Int) (h : Int) (m : Int) (s : Int) (L : Int) K
        (by have hx:=hcuts.1; omega) (by omega) (by have hx:=hb.2.1; omega) (by omega)
        (by omega) (by omega) (by omega) rfl (by omega) rfl hcircle
      omega
    have h9:=Recaman.HeadRunCountBounds.head_long_first_nine f n h M m L s U w hw hpre hM hm hL hs hU
      (by omega) hS hA hS2 hA2 hS3 hA3 (fun k hk hkB=>hpos k hk (by omega)) hlong
    have hs9:=hhead_budget 9 h9
    have hsmall:=Recaman.MassFourThreeArithmetic.boundary_small
      ((h : Int)+(m : Int)+(s : Int)) ((j : Int)+1) (M : Int) (m : Int) (s : Int) (L : Int) K
      (by have hx:=hcuts.1; omega) (by omega) (by have hx:=hb.2.1; omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) rfl hcircle
    have h67 : M=6 ∨ M=7 := by omega
    have hm1 : m=1 := by omega
    have h8:=Recaman.HeadSixSevenCount.head_six_seven_middle_one_eight f n h M m L s U w hw hpre hM hm hL hs hU
      (by omega) hS hA hS2 hA2 hS3 hA3 (fun k hk hkB=>hpos k hk (by omega)) h67 hm1 hlong
    have hs8:=hhead_budget 8 h8
    exact Recaman.MassFourThreeArithmetic.boundary_excluded
      ((h : Int)+(m : Int)+(s : Int)) ((j : Int)+1) (M : Int) (L : Int) K
      (by have hx:=hb.2.1; omega) (by omega) (by omega) (by omega) (by omega)
      (by have hx:=hcuts.1; omega) (by omega) hcircle
  · have hs12:=Recaman.ShortCounterSourceCounts.short_counter_source_head_count f n t h M m L s U 3 T j 4 w hw hpre ht
      hh hM hm hL hs hU (by omega) (by omega) (by omega) hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad (Or.inr hMeq)
    have hw17:=Recaman.ShortCounterSourceCounts.short_counter_source_weighted_count f n t h M m L s U 3 T j 4 w hw hpre ht
      hh hM hm hL hs hU (by omega) (by omega) (by omega) hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad (Or.inr hMeq)
    exact Recaman.MassFourThreeArithmetic.nonboundary
      ((h : Int)+(m : Int)+(s : Int)) ((j : Int)+1) (M : Int) ((M : Int)+(L : Int)) K
      (by have hx:=hcuts.1; omega) (by omega) (by have hx:=hb.2.1; omega) (by omega) hWM (by omega) hcircle

end Recaman.MassFourThreeGap
