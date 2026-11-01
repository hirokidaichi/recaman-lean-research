import Recaman.NoOldFourSGap
import Recaman.OldZeroTargetGap
import Recaman.MassThreeOldOneGap
import Recaman.MassThreeTargetCounter

namespace Recaman.MassThreeS4Gap

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- All old/no-old cases for a mass-three target after a positive
zero-mass three-run head and S4. No old-clock or local-band premise. -/
theorem mass_three_S4_gap (f : Nat → Bool) (n t h M m L s U T j : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w) (ht : t<n)
    (hh : 1≤h) (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hU : 1≤U)
    (hzeroMass : M+L+U=h+m+s)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ k, k<M → f (n+h+k)=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → f x=false)
    (hA2 : ∀ k, k<L → f (n+h+M+m+k)=true)
    (hS3 : ∀ x, n+h+M+m+L≤x → x<n+h+M+m+L+s → f x=false)
    (hA3 : ∀ k, k<U → f (n+h+M+m+L+s+k)=true)
    (hS4 : ∀ x, n+h+M+m+L+s+U≤x → x<n+h+M+m+L+s+U+4 → f x=false)
    (hA4 : ∀ k, k<T → f (n+h+M+m+L+s+U+4+k)=true)
    (hgap : ∀ x, n+h+M+m+L+s+U+4+T≤x → x<n+h+M+m+L+s+U+4+T+j → f x=false)
    (htarget : Win f t (n+h+M+m+L+s+U+4+T+j-t))
    (hC : mass (w.drop t)=3)
    (hpos : ∀ k, 0<k → k≤h+M+m+L+s+U+4+T →
      cN (EndN f 0) n k+1≤cN (fun x=>f x=false) n k)
 :
    j+1≤cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+4+T) := by
  classical
  by_cases hno : ∀ k, k<T → ∀ r, r<n → ¬Win f r (n+h+M+m+L+s+U+4+k-r)
  · exact Recaman.NoOldFourSGap.no_old_four_S_gap f n t h M m L s U T j w hw hpre ht
      hh hM hm hL hs hU hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hno hpos
  by_cases hgood : j+1≤cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+4+T)
  · exact hgood
  have hbad : cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+4+T)<j+1 := by omega
  have hb:=Recaman.MassThreeTargetCounter.mass_three_counter_parameters f n t h M m L s U 4 T j w hw hpre ht
    hh hM hm hL hs hU (Or.inr rfl) hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad
  obtain ⟨k,hkno⟩:=Classical.not_forall.mp hno
  have hk : k<T := by
    by_cases hh : k<T
    · exact hh
    · exact False.elim (hkno (fun hh'=>False.elim (hh hh')))
  have hrno : ¬∀ r, r<n → ¬Win f r (n+h+M+m+L+s+U+4+k-r) := by
    intro hr
    exact hkno (fun _=>hr)
  obtain ⟨r,hrno⟩:=Classical.not_forall.mp hrno
  have hr : r<n := by
    by_cases hh : r<n
    · exact hh
    · exact False.elim (hrno (fun hh'=>False.elim (hh hh')))
  have hwin : Win f r (n+h+M+m+L+s+U+4+k-r) := by
    apply Classical.byContradiction
    intro hn
    exact hrno (fun _=>hn)
  have hw' : BlockWord (seg f 0 n) := by rw [hpre]; exact hw
  have horder:=Recaman.OldSourceKeyOrder.actual_old_target_prior_clock f n r t
    (h+M+m+L+s+U+4) k T j hw' hr ht (by omega) (by have hR:=hb.2.1; omega)
    (by simpa only [Nat.add_assoc] using hA4)
    (by simpa only [Nat.add_assoc] using hgap)
    (by simpa only [Nat.add_assoc] using hwin)
    (by simpa only [Nat.add_assoc] using htarget)
  have hk1 : k≤1 := by have hT:=hb.1; omega
  by_cases hk0 : k=0
  · apply Recaman.OldZeroTargetGap.old_zero_short_target_free_gap f n t h M m L s U 4 T j r w hw hpre ht
      hh hM hm hL hs hU hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 (by decide) hgap htarget hr
      (by simpa only [hk0,Nat.add_zero] using hwin) (by simpa using hC) hpos
  · have hkOne : k=1 := by omega
    apply Recaman.MassThreeOldOneGap.mass_three_old_one_gap f n t h M m L s U T j r w hw hpre ht
      hh hM hm hL hs hU hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hr
      (by simpa only [hkOne,Nat.add_zero] using hwin) hC hpos

end Recaman.MassThreeS4Gap
