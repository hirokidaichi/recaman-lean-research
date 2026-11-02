import Recaman.ShortCounterWeightedCounts
import Recaman.ShortCounterJointQuadratic
import Recaman.MassFourOneArithmetic
import Recaman.MassFourOneBounds
import Recaman.SmallInversionActual
import Recaman.S15SecondExclusion
import Recaman.SecondRaySmallShapes
import Recaman.FirstTwoActualBounds
import Recaman.ShortCounterSourceCounts
import Recaman.ShortCounterJointCuts

namespace Recaman.MassFourOneBands

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- Actual small-inversion head charging reduces the remaining counter to three strict parameter bands. -/
theorem mass_four_one_bands (f : Nat → Bool) (n t h M m L s U v T j C : Nat)
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
    (h+m+s=13 ∧ j=4 ∧ (M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int)=17) ∨
    (h+m+s=14 ∧ j=4 ∧ 17≤(M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int) ∧
      (M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int)≤26) ∨
    (h+m+s=14 ∧ j=5 ∧ 17≤(M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int) ∧
      (M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int)≤21) := by
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
  have hbounds:=Recaman.MassFourOneBounds.mass_four_one_bounds f n t h M m L s U 1 T j 4 w hw hpre ht
    hh hM hm hL hs hU rfl rfl hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad
  have hK17 : 17≤K := by
    by_cases hk : 17≤K
    · exact hk
    have hhead7:=Recaman.SmallInversionActual.small_inversion_three_run_count_seven f n h M m L s U w hw hpre hs
      (by omega) hS hA hS2 hA2 hS3 hA3 hM hm hL (by change K≤16; omega)
      (fun k hk hkB=>hpos k hk (by omega))
    have hs12:=Recaman.ShortCounterSourceCounts.short_counter_source_head_budget f n t h M m L s U 1 T j 4 w hw hpre ht
      hh hM hm hL hs hU (by omega) (by omega) (by omega) hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad hsrc 7 hhead7
    let H:=h+M+m+L+s+U
    let P:=fun x=>f x=true ∧ ¬EndN f 0 x
    have hword:=Recaman.SeparatorSupplyReset.three_run_word f n h M m L s U hS hA hS2 hA2 hS3 hA3
    have hAc : cN (fun x=>f x=true) n H=h+m+s := by
      have hx:=ones_seg_eq_count f n (h+M+m+L+s+U)
      rw [hword] at hx
      simp only [ones_append,ones_replicate_A,ones_replicate_S] at hx
      dsimp [H]
      omega
    have hp:=addition_endable_partition f n H
    rw [hAc] at hp
    change h+m+s=cN (EndN f 0) n H+cN P n H at hp
    have hf:=cN_add P n H (1+T)
    change cN (EndN f 0) n H≤7 at hhead7
    change cN P n (h+M+m+L+s+U+1+T)<j+1 at hbad
    simp only [H,Nat.add_assoc] at hp hf hhead7 hbad
    have hsR : h+m+s≤j+7 := by omega
    have hfalse:=Recaman.MassFourOneArithmetic.small_inversion_impossible
      ((h : Int)+(m : Int)+(s : Int)) ((j : Int)+1) (M : Int) ((M : Int)+(L : Int)) K
      (by have hx:=hcuts.1; omega) (by omega) (by have hx:=hb.2.1; omega) (by omega)
      (by have hx:=hjoint.1; omega) hWM (by omega) (by omega) hcircle
    exact False.elim hfalse
  have hbands:=Recaman.MassFourOneArithmetic.inversion_three_bands
    ((h : Int)+(m : Int)+(s : Int)) ((j : Int)+1) K
    (by have hx:=hcuts.1; omega) (by omega) (by have hx:=hb.2.1; omega) hK17 hcircle
  rcases hbands with ha | hb | hc
  · exact Or.inl ⟨by omega,by omega,ha.2.2⟩
  · exact Or.inr (Or.inl ⟨by omega,by omega,hb.2.2.1,hb.2.2.2⟩)
  · exact Or.inr (Or.inr ⟨by omega,by omega,hc.2.2.1,hc.2.2.2⟩)
end Recaman.MassFourOneBands
