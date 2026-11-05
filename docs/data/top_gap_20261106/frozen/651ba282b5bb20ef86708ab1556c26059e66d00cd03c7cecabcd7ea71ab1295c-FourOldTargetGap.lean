import Recaman.FourGapSixExclusion
import Recaman.FourGapFiveExclusion
import Recaman.FourGapFourExclusion

namespace Recaman.FourOldTargetGap

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- Genuine four-run tails with a selected old target satisfy the full
actual free-gap bound at the original base. No head-mass or length cap. -/
theorem four_old_target_free_gap (f : Nat → Bool) (n t h M m L s U v T j C : Nat)
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
    (htarget : Win f t (n+h+M+m+L+s+U+v+T+j-t)) :
    j+1≤cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T) := by
  let B:=h+M+m+L+s+U+v+T
  let A:=cN (fun x=>f x=true) n B
  let F:=cN (fun x=>f x=true ∧ ¬EndN f 0 x) n B
  change j+1≤F
  by_cases hg : j+1≤F
  · exact hg
  have hbad : F<j+1 := by omega
  exfalso
  have hj4 : 4≤j := by
    by_cases h4 : 4≤j
    · exact h4
    · have hC2:=Recaman.OldTargetFreeAccounting.old_target_counter_mass f n t B j C (by omega) hC
        (hpos B (by dsimp [B]; omega) (by omega))
        (by simpa only [B,Nat.add_assoc] using hgap)
        (by simpa only [B,Nat.add_assoc] using htarget) hbad
      have hAlo : 2*j+3≤A := Recaman.PrimitiveOldTargetCut.actual_old_target_A_cut
        f n t B j w hw hpre ht (by rw [hC]; omega)
        (by simpa only [B,Nat.add_assoc] using hgap) (by simpa only [B,Nat.add_assoc] using htarget)
      have hAhi:=positive_r3_additions_free_bound f n 0 B hw (by simpa using hpre) hpos
        (show F≤3 by omega)
      change A≤2*F+1 at hAhi
      omega
  by_cases hj6 : 6≤j
  · exact Recaman.FourGapSixExclusion.four_gap_ge_six_excluded f n t h M m L s U v T j C w hw hpre ht hC
      hM hL hU hT hm hs hv hS hA hS2 hA2 hS3 hA3 hS4 hA4 hpos hgap htarget hbad hj6
  · by_cases hj5 : j=5
    · exact Recaman.FourGapFiveExclusion.four_gap_five_excluded f n t h M m L s U v T j C w hw hpre ht hC
        hM hL hU hT hm hs hv hS hA hS2 hA2 hS3 hA3 hS4 hA4 hpos hgap htarget hbad hj5
    · exact Recaman.FourGapFourExclusion.four_gap_four_excluded f n t h M m L s U v T j C w hw hpre ht hC
        hM hL hU hT hm hs hv hS hA hS2 hA2 hS3 hA3 hS4 hA4 hpos hgap htarget hbad (by omega)

end Recaman.FourOldTargetGap
