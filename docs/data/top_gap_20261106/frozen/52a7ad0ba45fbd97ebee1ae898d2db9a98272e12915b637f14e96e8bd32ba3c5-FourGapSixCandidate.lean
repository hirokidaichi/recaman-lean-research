import Recaman.FourDelayedCounterData
import Recaman.GapSixScalar

namespace Recaman.FourGapSixCandidate

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- Every gap>=6 actual counter would force an impossible combination
of head saturation and low AS cross. -/
theorem actual_gap_six_candidate (f : Nat → Bool) (n t h M m L s U v T j C : Nat)
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
    (hbad : cN (fun x => f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)<j+1) (hj : 6≤j) :
    j=6 ∧ cN (fun x=>f x=true) n (h+M+m+L+s+U+v+T)=17 ∧
    cN (EndN f 0) n (h+M+m+L+s+U)=10 ∧ M*(m+s)+L*s≤10 := by
  obtain ⟨hC2,hA,hAeq,hcount,_,hEH,hr,hF,hfree,_,hW,_,hpair,hsq⟩:=
    Recaman.FourDelayedCounterData.four_delayed_counter_data f n t h M m L s U v T j C w hw hpre ht hC
      hM hL hU hT hm hs hv hS hA hS2 hA2 hS3 hA3 hS4 hA4 hpos hgap htarget hbad (by omega)
  have ha : 2≤M*(m+s) := Nat.mul_le_mul hM (show 2≤m+s by omega)
  have hb : 1≤L*s := Nat.mul_le_mul hL hs
  have hi : 3≤M*(m+s)+L*s := by omega
  obtain ⟨he,ht'⟩:=Recaman.GapSixScalar.last_pair_budget _ _ _ _ _ hj hr hW (by omega) hpair
  exact Recaman.GapSixScalar.gap_six_candidate _ _ _ _ _ _ _ _ _ _ hj hC2 hi hv hA hAeq hcount hEH he hF ht' hsq

end Recaman.FourGapSixCandidate
