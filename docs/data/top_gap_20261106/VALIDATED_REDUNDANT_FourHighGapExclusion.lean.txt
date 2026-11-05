import Recaman.FourHighGapCandidate
import Recaman.FourthUnitSeparators

namespace Recaman.FourHighGapExclusion

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- No genuine four-run counter with the same old target can have gap
nine or greater. The final case lacks a fifth distinct last-ray clock. -/
theorem four_high_gap_excluded (f : Nat → Bool) (n t h M m L s U v T j C : Nat)
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
    (hbad : cN (fun x => f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)<j+1) (hj : 9≤j) : False := by
  let B:=h+M+m+L+s+U+v
  obtain ⟨hj9,_,hT,hm1,hs1,hv1,hE,hword⟩:=Recaman.FourHighGapCandidate.actual_high_gap_unit_candidate
    f n t h M m L s U v T j C w hw hpre ht hC hM hL hU hT hm hs hv
    hS hA hS2 hA2 hS3 hA3 hS4 hA4 hpos hgap htarget hbad hj
  let z:=List.replicate M true++List.replicate 1 false++List.replicate L true++
    List.replicate 1 false++List.replicate U true++List.replicate 1 false
  have hz : seg f n B=List.replicate h false++z := by
    apply hword.trans
    simp only [z,hm1,hs1,hv1]
  have hlocal : rayCount z T≤4 := Recaman.FourthUnitSeparators.unit_separators_after_initial_four M L U T hL hU
  have hw0 : BlockWord (seg f 0 n) := by rw [hpre]; exact hw
  have hcut:=Recaman.OldTargetEarlyClockBudget.old_target_early_word_budget f n t B T j
    (List.replicate h false) z hw0 ht (by omega) hz (by rw [ones_replicate_S]; omega)
    (by simpa only [B,Nat.add_assoc] using hA4)
    (by simpa only [B,Nat.add_assoc] using hgap)
    (by simpa only [B,Nat.add_assoc] using htarget)
  change 5≤cN (EndN f 0) (n+B) T at hE
  omega

end Recaman.FourHighGapExclusion
