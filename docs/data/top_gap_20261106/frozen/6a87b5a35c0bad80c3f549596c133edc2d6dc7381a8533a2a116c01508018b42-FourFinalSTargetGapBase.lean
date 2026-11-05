import Recaman.FourFinalSTargetGap
import Recaman.FourRunSourceBase

namespace Recaman.FourFinalSTargetGapBase

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

open Classical in
/-- Original integer base, padded history and the same actual P2 window
are preserved for a target within the final S separator. -/
theorem four_final_S_target_free_gap_int (e : Int → Bool) (p : Int) (n a t h M m L s U v T j : Nat)
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
    (hta : n+h+M+m+L+s+U≤t) (htb : t<n+h+M+m+L+s+U+v)
    (htarget : P2 (past e (p+((n+h+M+m+L+s+U+v+T+j : Nat) : Int)) (n+h+M+m+L+s+U+v+T+j-t)))
    : j+1≤countP (fun x=>e x=true ∧ ¬Endable e p x) (p+(n : Int)) (h+M+m+L+s+U+v+T) := by
  rw [segment_seg e p p 0 (by simp)] at hpre
  simp only [endableCount_shift,subtractionCount_shift] at hzero hpos
  rw [nonsupplied_count_shift]
  have hrel : ∀ k, 0<k → k≤h+M+m+L+s+U+v+T →
      cN (EndN (fun i=>e (p+(i : Int))) 0) n k+1≤cN (fun i=>e (p+(i : Int))=false) n k := by
    intro k hk hkB
    have hp:=hpos (n+k) (by omega) (by omega)
    have he:=cN_add (EndN (fun i=>e (p+(i : Int))) 0) 0 n k
    have hs:=cN_add (fun i=>e (p+(i : Int))=false) 0 n k
    simp only [Nat.zero_add] at he hs
    omega
  have hW : Win (fun k=>e (p+(k : Int))) t (n+h+M+m+L+s+U+v+T+j-t) := by
    apply Recaman.FourRunSourceBase.P2_shifted_window e p t (n+h+M+m+L+s+U+v+T+j-t) (by omega)
    simpa only [show t+(n+h+M+m+L+s+U+v+T+j-t)=n+h+M+m+L+s+U+v+T+j by omega] using htarget
  exact Recaman.FourFinalSTargetGap.four_final_S_target_free_gap (fun k=>e (p+(k : Int)))
    n t h M m L s U v T j (w++List.replicate a true) (block_append hw (block_replicate_A a)) hpre
    hM hL hU hT hm hs hv hS hA hS2 hA2 hS3 hA3 hS4 hA4 hrel hgap hta htb hW

end Recaman.FourFinalSTargetGapBase
