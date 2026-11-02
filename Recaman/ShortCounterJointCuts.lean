import Recaman.ShortCounterJointQuadratic
import Recaman.ShortCounterBands

namespace Recaman.ShortCounterJointCuts

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- Joint actual free charging forces target mass at most five, and
removes the old close-mass5 and deep-v3 branches at arbitrary lengths. -/
theorem short_counter_joint_cuts (f : Nat → Bool) (n t h M m L s U v T j C : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w) (ht : t<n)
    (hh : 1≤h) (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hU : 1≤U)
    (hv : v<C) (hvpos : 1≤v) (hC4 : 4≤C)
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
    C≤5 ∧ v≤3 ∧ (C=v+1 → C=4 ∧ v=3 ∧ j+1≤7) ∧ (v+2≤C → v≤2) := by
  have hb:=Recaman.ShortTargetCounter.short_target_counter f n t h M m L s U v T j C w hw hpre ht
    hh hM hm hL hs hU hv hvpos hC4 hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad
  have hbands:=Recaman.ShortCounterBands.short_counter_five_bands f n t h M m L s U v T j C w hw hpre ht
    hh hM hm hL hs hU hv hvpos hC4 hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad
  have hq:=Recaman.ShortCounterJointQuadratic.short_counter_joint_quadratic f n t h M m L s U v T j C w hw hpre ht
    hh hM hm hL hs hU hv hvpos hC4 hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad
  have hc:=Recaman.JointShiftedCircle.parameter_cuts (C : Int) (v : Int) ((j : Int)+1)
    (by omega) (by have hx:=hbands.2.1; omega) (by omega) (by omega)
    (by have hx:=hb.2.1; omega) (by have hx:=hbands.2.2.2.1; omega)
    (by intro hd; exact hq.1 (by omega))
    (by intro hd; exact hq.2.1 (by omega))
    (by intro hd; exact hq.2.2 (by omega))
  refine ⟨by have hx:=hc.1; omega,by have hx:=hc.2.1; omega,?_,?_⟩
  · intro hclose
    have hx:=hc.2.2.1 (by omega)
    omega
  · intro hdeep
    have hx:=hc.2.2.2 (by omega)
    omega

end Recaman.ShortCounterJointCuts
