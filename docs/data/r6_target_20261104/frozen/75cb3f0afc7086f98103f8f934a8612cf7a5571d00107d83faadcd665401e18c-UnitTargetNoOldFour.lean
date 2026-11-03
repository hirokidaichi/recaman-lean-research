import Recaman.FourthActualSeven
import Recaman.UnitTargetNoOldResidual
import Recaman.KFiveHeadActual
import Recaman.UnitTargetSmallHeadKey
import Recaman.MomentNoOld
import Recaman.MassOneTargetCounter
import Recaman.MomentTargetProfile

namespace Recaman.UnitTargetNoOldFour

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

theorem unit_no_old_head_four (f : Nat → Bool) (n t h M m L s U v T j : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w) (ht : t<n)
    (hh : 1≤h) (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hU : 1≤U)
    (hv : 1≤v)
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
    (hC : mass (w.drop t)=1)
    (hpos : ∀ k, 0<k → k≤h+M+m+L+s+U+v+T →
      cN (EndN f 0) n k+1≤cN (fun x=>f x=false) n k)
    (hbad : cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)<j+1)
    (hnoOld : ∀ k, k<T → ∀ r, r<n → ¬Win f r (n+h+M+m+L+s+U+v+k-r)) :
    cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U)=4 := by
  have hr:=Recaman.UnitTargetNoOldResidual.unit_no_old_residual f n t h M m L s U v T j w hw hpre ht
    hh hM hm hL hs hU hv hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad hnoOld
  rcases hr with hfour|hsmall
  · exact hfour
  have hhead3:=Recaman.KFiveHeadActual.K_five_head_three f n h M m L s U w hw hpre hM hm hL hs
    hsmall.2.1 hsmall.2.2.2.2 hS hA hS2 hA2 hS3 hA3
  have hword:=Recaman.SeparatorSupplyReset.three_run_word f n h M m L s U hS hA hS2 hA2 hS3 hA3
  have hAcount:=ones_seg_eq_count f n (h+M+m+L+s+U)
  rw [hword] at hAcount
  simp only [ones_append,ones_replicate_A,ones_replicate_S] at hAcount
  have hpart:=addition_endable_partition f n (h+M+m+L+s+U)
  omega

end Recaman.UnitTargetNoOldFour
