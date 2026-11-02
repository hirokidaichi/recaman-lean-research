import Recaman.ShortCounterWeightedCounts
import Recaman.ShortCounterJointQuadratic
import Recaman.MassFourTwoArithmetic
import Recaman.SecondRaySmallShapes
import Recaman.FirstTwoActualBounds
import Recaman.ShortCounterSourceCounts
import Recaman.ShortCounterJointCuts

namespace Recaman.MassFourTwoResidual

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- The mass4/separator3 branch has full actual free-gap at all lengths.
Weighted prefix and run budgets are supplied inside the counter argument. -/
theorem mass_four_two_residual (f : Nat → Bool) (n t h M m L s U v T j C : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w) (ht : t<n)
    (hh : 1≤h) (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hU : 1≤U)
    (hv : v=2) (hC4 : C=4)
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
    h=11 ∧ M=4 ∧ m=1 ∧ s=1 ∧ j=4 ∧ T=3 ∧ ((L=3 ∧ U=6) ∨ (L=4 ∧ U=5)) := by
  subst C
  subst v
  have hb:=Recaman.ShortTargetCounter.short_target_counter f n t h M m L s U 2 T j 4 w hw hpre ht
    hh hM hm hL hs hU (by omega) (by omega) (by omega) hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad
  have hj:=Recaman.ShortCounterJointCounts.short_counter_joint_counts f n t h M m L s U 2 T j 4 w hw hpre ht
    hh hM hm hL hs hU (by omega) (by omega) (by omega) hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad
  have hwc:=Recaman.ShortCounterWeightedCounts.short_counter_weighted_counts f n t h M m L s U 2 T j 4 w hw hpre ht
    hh hM hm hL hs hU (by omega) (by omega) (by omega) hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad
  have hcuts:=Recaman.ShortCounterParameterCuts.short_counter_parameter_cuts f n t h M m L s U 2 T j 4 w hw hpre ht
    hh hM hm hL hs hU (by omega) (by omega) (by omega) hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad
  have hq:=Recaman.ShortCounterJointQuadratic.short_counter_joint_quadratic f n t h M m L s U 2 T j 4 w hw hpre ht
    hh hM hm hL hs hU (by omega) (by omega) (by omega) hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad
  let K: Int:=(M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int)
  have hWM : (M : Int)+(L : Int)+(M : Int)≤K := by
    have h1:=Int.mul_nonneg (show 0≤(M : Int) by omega) (show 0≤(m : Int)+(s : Int)-2 by omega)
    have h2:=Int.mul_nonneg (show 0≤(L : Int) by omega) (show 0≤(s : Int)-1 by omega)
    have he : K-(2*(M : Int)+(L : Int))=
        (M : Int)*((m : Int)+(s : Int)-2)+(L : Int)*((s : Int)-1) := by dsimp [K]; grind only
    omega
  have hraw:=Recaman.ShortCounterJointQuadratic.short_counter_cross_circle f n t h M m L s U 2 T j 4 w hw hpre ht
    hh hM hm hL hs hU (by omega) (by omega) (by omega) hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad
  change ((j : Int)+1)^2+(4 : Int)^2+2*4*2-2^2-1+2*K≤
    (((h : Int)+(m : Int)+(s : Int))-4)^2 at hraw
  have hcircle : ((j : Int)+1)^2+27+2*K≤(((h : Int)+(m : Int)+(s : Int))-4)^2 := by omega
  have hsrc : 2+2≤4 ∨ M≠j+2 := Or.inl (by omega)
  have hjoint:=Recaman.ShortCounterSourceCounts.short_counter_source_weighted_count f n t h M m L s U 2 T j 4 w hw hpre ht
    hh hM hm hL hs hU (by omega) (by omega) (by omega) hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad hsrc
  have hhead14 : h+m+s≤14 := by
    have hx:=Recaman.ShortCounterSourceCounts.short_counter_source_head_count f n t h M m L s U 2 T j 4 w hw hpre ht
      hh hM hm hL hs hU (by omega) (by omega) (by omega) hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad hsrc
    omega
  have hR7 : j+1≤7 := by
    have hqdeep:=hq.2.1 (by omega)
    by_cases hr : j+1≤7
    · exact hr
    have hs8:=Recaman.ShortCounterFactorBounds.square_lower ((j : Int)+1) 8 (by omega) (by omega)
    omega
  have hlong (hM4 : 4≤M) : 2*M≤h+3 := by
    have hx:=Recaman.MassFourTwoArithmetic.long_initial
      ((h : Int)+(m : Int)+(s : Int)) ((j : Int)+1) (M : Int) (h : Int) (m : Int) (s : Int) (L : Int) ((M : Int)+(L : Int)) K
      (by have hx:=hcuts.1; omega) (by omega) (by have hx:=hb.2.1; omega) (by omega)
      (by omega) (by have hx:=hb.2.2.1; omega) (by omega) (by omega) (by omega) rfl rfl
      (by have hx:=hjoint.2; omega) (by have hx:=hjoint.1; omega) rfl hcircle
    omega
  have hprefix:=Recaman.FirstTwoActualBounds.prefix_first_one f n h M m L w hw hpre hM hm hL hS hA hS2 hA2
    (hpos (h+M+m+L) (by omega) (by omega))
    (by by_cases hM3 : M≤3; exact Or.inl hM3; exact Or.inr (hlong (by omega)))
  have hW8:=Recaman.ShortCounterSourceCounts.short_counter_source_prefix_budget f n t h M m L s U 2 T j 4 w hw hpre ht
    hh hM hm hL hs hU (by omega) (by omega) (by omega) hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad hsrc 4 hprefix
  have hhead_budget (B : Nat) (hc : cN (EndN f 0) n (h+M+m+L+s+U)≤B) : h+m+s≤B+4 := by
    have hx:=Recaman.ShortCounterSourceCounts.short_counter_source_head_budget f n t h M m L s U 2 T j 4 w hw hpre ht
      hh hM hm hL hs hU (by omega) (by omega) (by omega) hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad hsrc B hc
    omega
  have hhead9:=Recaman.HeadRunCountBounds.head_from_prefix f n h M m L s U w hw hpre hM hm hL hs hU
    (by omega) hS hA hS2 hA2 hS3 hA3 (fun k hk hkB=>hpos k hk (by omega)) 4 hprefix
  have hS13:=hhead_budget 9 hhead9
  have hsmall : M≤2 → h+m+s≤12 := by
    intro hM2
    apply hhead_budget 8
    exact Recaman.HeadRunCountBounds.head_first_two_eight f n h M m L s U w hw hpre hM hm hL hs hU
      (by omega) hS hA hS2 hA2 hS3 hA3 (fun k hk hkB=>hpos k hk (by omega)) hM2
  have hres:=Recaman.MassFourTwoArithmetic.residual
    ((h : Int)+(m : Int)+(s : Int)) ((j : Int)+1) (M : Int) (m : Int) (s : Int) (L : Int) ((M : Int)+(L : Int)) K
    (by have hx:=hcuts.1; omega) (by omega) (by have hx:=hb.2.1; omega)
    (by omega) (by omega) (by omega) (by omega) (by have hx:=hb.2.2.1; omega) rfl (by omega)
    (by have hx:=hjoint.1; omega) hWM rfl (by intro hx; have hy:=hsmall (by omega); omega) hcircle
  have hsmall_shape (hshape : (M=1 ∧ m=1) ∨ (M=3 ∧ 1≤m ∧ m≤3) ∨ (5≤M ∧ M≤7 ∧ m=1)) :=
    Recaman.SecondRaySmallShapes.head_small_second_eight f n h M m L s U w hw hpre hM hm hL hs hU
      (by omega) hS hA hS2 hA2 hS3 hA3 (fun k hk hkB=>hpos k hk (by omega)) hshape hlong
  rcases hres with hsmallres | hrest
  · have hshape : (M=1 ∧ m=1) ∨ (M=3 ∧ 1≤m ∧ m≤3) ∨ (5≤M ∧ M≤7 ∧ m=1) := Or.inl ⟨by omega,by omega⟩
    have hx:=(hsmall_shape hshape).2 (by omega)
    have hy:=hhead_budget 7 hx
    omega
  · have hM4 : M=4 := by
      by_cases h4 : M=4
      · exact h4
      have hshape : (M=1 ∧ m=1) ∨ (M=3 ∧ 1≤m ∧ m≤3) ∨ (5≤M ∧ M≤7 ∧ m=1) := by
        rcases hrest.2.2.2.2 with h3 | hlarge
        · exact Or.inr (Or.inl ⟨by omega,hm,by omega⟩)
        · exact Or.inr (Or.inr ⟨by omega,by omega,by omega⟩)
      have hx:=(hsmall_shape hshape).1
      have hy:=hhead_budget 8 hx
      omega
    have hms : m=1 ∧ s=1 := by
      rcases hrest.2.2.2.2 with h3 | hlarge
      · omega
      · omega
    have hbal:=hb.1
    refine ⟨by omega,hM4,hms.1,hms.2,by omega,by omega,?_⟩
    omega
end Recaman.MassFourTwoResidual
