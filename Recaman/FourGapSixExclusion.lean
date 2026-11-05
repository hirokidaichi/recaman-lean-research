import Recaman.FourGapSixCandidate
import Recaman.HeadSaturationCross

namespace Recaman.FourGapSixExclusion

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- A genuine four-run same-old-target counter cannot have gap at
least six. The saturated head costs more AS pairs than the target allows. -/
theorem four_gap_ge_six_excluded (f : Nat → Bool) (n t h M m L s U v T j C : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w) (ht : t<n)
    (hC : mass (seg f t (n-t))=(C : Int))
    (hM : 1≤M) (hL : 1≤L) (hU : 1≤U) (hT : 1≤T) (hm : 1≤m) (hs : 1≤s) (hv : 1≤v)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ i, i<M → f (n+h+i)=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → f x=false)
    (hA2 : ∀ i, i<L → f (n+h+M+m+i)=true)
    (hS3 : ∀ x, n+h+M+m+L≤x → x<n+h+M+m+L+s → f x=false)
    (hA3 : ∀ i, i<U → f (n+h+M+m+L+s+i)=true)
    (hS4 : ∀ x, n+h+M+m+L+s+U≤x → x<n+h+M+m+L+s+U+v → f x=false)
    (hA4 : ∀ i, i<T → f (n+h+M+m+L+s+U+v+i)=true)
    (hpos : ∀ k, 0<k → k≤h+M+m+L+s+U+v+T →
      cN (EndN f 0) n k+1≤cN (fun x => f x=false) n k)
    (hgap : ∀ x, n+h+M+m+L+s+U+v+T≤x → x<n+h+M+m+L+s+U+v+T+j → f x=false)
    (htarget : Win f t (n+h+M+m+L+s+U+v+T+j-t))
    (hbad : cN (fun x => f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)<j+1) (hj : 6≤j) : False := by
  obtain ⟨_,_,hh,hi⟩:=Recaman.FourGapSixCandidate.actual_gap_six_candidate
    f n t h M m L s U v T j C w hw hpre ht hC hM hL hU hT hm hs hv
    hS hA hS2 hA2 hS3 hA3 hS4 hA4 hpos hgap htarget hbad hj
  obtain ⟨hw5,hx⟩:=Recaman.HeadSaturationCross.head_ten_cross_extra_six f n h M m L s U w hw hpre
    hM hm hL hs hU hS hA hS2 hA2 hS3 hA3 (fun k hk hkH=>hpos k hk (by omega)) (by omega)
  omega

end Recaman.FourGapSixExclusion
