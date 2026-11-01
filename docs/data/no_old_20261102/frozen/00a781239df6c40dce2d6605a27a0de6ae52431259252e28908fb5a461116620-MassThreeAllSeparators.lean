import Recaman.LowSeparatorMassThreeGap
import Recaman.MassThreeS3Gap
import Recaman.MassThreeS4Gap
import Recaman.MassThreeS5Gap
import Recaman.LargeSeparatorMassThreeGap

namespace Recaman.MassThreeAllSeparators

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- Integration of the five separator regimes. This case split is an
adapter; the source inequalities are the separately audited inputs. -/
theorem mass_three_all_separators_gap (f : Nat → Bool) (n t h M m L s U v T j : Nat)
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
    (hC : mass (w.drop t)=3)
    (hpos : ∀ k, 0<k → k≤h+M+m+L+s+U+v+T →
      cN (EndN f 0) n k+1≤cN (fun x=>f x=false) n k)
 :
    j+1≤cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T) := by
  by_cases hlow : v=1 ∨ v=2
  · exact Recaman.LowSeparatorMassThreeGap.low_separator_mass_three_gap f n t h M m L s U v T j w hw hpre ht
      hh hM hm hL hs hU hlow hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos
  by_cases hthree : v=3
  · subst v
    exact Recaman.MassThreeS3Gap.mass_three_S3_gap f n t h M m L s U T j w hw hpre ht
      hh hM hm hL hs hU hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos
  by_cases hfour : v=4
  · subst v
    exact Recaman.MassThreeS4Gap.mass_three_S4_gap f n t h M m L s U T j w hw hpre ht
      hh hM hm hL hs hU hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos
  by_cases hfive : v=5
  · subst v
    exact Recaman.MassThreeS5Gap.mass_three_S5_gap f n t h M m L s U T j w hw hpre ht
      hh hM hm hL hs hU hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos
  exact Recaman.LargeSeparatorMassThreeGap.large_separator_mass_three_gap f n t h M m L s U v T j w hw hpre ht
    hh hM hm hL hs hU (by omega) hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos

end Recaman.MassThreeAllSeparators
