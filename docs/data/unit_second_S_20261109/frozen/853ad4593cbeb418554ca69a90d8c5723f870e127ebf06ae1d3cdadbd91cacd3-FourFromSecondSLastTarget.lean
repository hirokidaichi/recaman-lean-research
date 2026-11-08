import Recaman.UnitSecondSNoCounterBase
import Recaman.SecondAHeadBudgetGapBase

namespace Recaman.FourFromSecondSLastTarget
open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

open Classical in
/-- Integration with the existing late-target theorem; this wrapper is
not an additional independent source edge. -/
theorem four_from_last_second_S_target_free_gap_int (e : Int → Bool) (p : Int) (n a t h M m L s U v T j : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : segment e p n=w++List.replicate a true)
    (hM : 1≤M) (hL : 1≤L) (hU : 1≤U) (hT : 1≤T) (hm : 1≤m) (hs : 1≤s) (hv : 1≤v)
    (hS : ∀ x, n≤x → x<n+h → e (p+(x : Int))=false)
    (hA : ∀ i, i<M → e (p+((n+h+i : Nat) : Int))=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → e (p+(x : Int))=false)
    (hA2 : ∀ i, i<L → e (p+((n+h+M+m+i : Nat) : Int))=true)
    (hS3 : ∀ x, n+h+M+m+L≤x → x<n+h+M+m+L+s → e (p+(x : Int))=false)
    (hA3 : ∀ i, i<U → e (p+((n+h+M+m+L+s+i : Nat) : Int))=true)
    (hS4 : ∀ x, n+h+M+m+L+s+U≤x → x<n+h+M+m+L+s+U+v → e (p+(x : Int))=false)
    (hA4 : ∀ i, i<T → e (p+((n+h+M+m+L+s+U+v+i : Nat) : Int))=true)
    (hzero : endableCount e p n=subtractionCount e p n)
    (hpos : ∀ q, n<q → q≤n+h+M+m+L+s+U+v+T+j →
      endableCount e p q+1≤subtractionCount e p q)
    (hgap : ∀ x, n+h+M+m+L+s+U+v+T≤x → x<n+h+M+m+L+s+U+v+T+j → e (p+(x : Int))=false)
    (hta : n+h+M+m-1≤t)
    (htarget : P2 (past e (p+((n+h+M+m+L+s+U+v+T+j : Nat) : Int)) (n+h+M+m+L+s+U+v+T+j-t)))
    : j+1≤countP (fun x=>e x=true ∧ ¬Endable e p x) (p+(n : Int)) (h+M+m+L+s+U+v+T) := by
  by_cases ht : n+h+M+m≤t
  · exact Recaman.SecondAHeadBudgetGapBase.four_from_second_A_target_free_gap_int
      e p n a t h M m L s U v T j w hw hpre hM hL hU hT hm hs hv
      hS hA hS2 hA2 hS3 hA3 hS4 hA4 hzero hpos hgap ht htarget
  · exact Recaman.UnitSecondSNoCounterBase.unit_second_S_free_gap_int
      e p n a t h M m L s U v T j w hw hpre hM hL hU hT hm hs hv
      hS hA hS2 hA2 hS3 hA3 hS4 hA4 hzero hpos hgap (by omega) (by omega) (by omega) htarget

end Recaman.FourFromSecondSLastTarget
