import Recaman.LargePrefixTargetArea
import Recaman.SmallPrefixSupplyThirteen

namespace Recaman.FinalSSourceResidual

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.RunSupplyBudget Recaman.FourRunSupplySeventeen
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- Both measured first-two-run branches, in the same actual history.
A necessary-condition reduction, not absence of counterexamples. -/
theorem final_S_counterexample_band_twelve (f : Nat → Bool) (n t h M m L s U v T j q i : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w) (ht : t<n)
    (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hU : 1≤U) (hv : 1≤v)
    (hq : 1≤q) (hqv : q≤v) (hi : i<T) (hband : T≤i+j)
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
    (he : EndN f 0 (n+h+M+m+L+s+U+v+T+j))
    (htarget : Win f t (n+h+M+m+L+s+U+v+T+j-t))
    (hlocal : Win f (n+h+M+m+L+s+U+v-q) (q+i))
    (hbad : cN (fun x => f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)<j+1) :
    4≤cN (fun x => f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T) ∧
    cN (fun x => f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)≤12 ∧
    cN (fun x => f x=true) n (h+M+m+L+s+U+v+T)≤29 ∧ j≤12 := by
  have hword:=four_run_word f n h M m L s U v T hS hA hS2 hA2 hS3 hA3 hS4 hA4
  have hnew:=Recaman.FourRunTargetArea.actual_final_S_source_A_budget
    f n t h M m L s U v T j q i w hw hpre ht
    hM hm hL hs hU hv hq hqv hi hband hword hS4 hA4 hgap htarget hlocal
  have hold:=Recaman.FourRunSupplyBudget.four_run_free_gap_residual f n h M m L s U v T j
    w hw hpre hm hs hv hS hA hS2 hA2 hS3 hA3 hS4 hA4 hpos hgap he hbad
  by_cases hML : j+1≤M+L
  · have hlarge:=Recaman.LargePrefixTargetArea.actual_large_first_two_A_budget
      f n t h M m L s U v T j w hw hpre ht hM hm hL hs hU hv
      (by omega) hML hword hgap htarget
    have hE:=four_run_supply_le_seventeen f n h M m L s U v T
      w hw hpre hM hm hs hv hS hA hS2 hA2 hS3 hA3 hS4 hA4 hpos
    have hp:=addition_endable_partition f n (h+M+m+L+s+U+v+T)
    omega
  · have hsml:=Recaman.SmallPrefixSupplyThirteen.small_prefix_counterexample_band_nine
      f n t h M m L s U v T j q i w hw hpre ht
      hM hm hL hs hU hv (by omega) hq hqv hi hband hS hA hS2 hA2 hS3 hA3 hS4 hA4
      hpos hgap he htarget hlocal hbad
    omega

theorem final_S_band_from_zero_twelve (f : Nat → Bool) (n t h M m L s U v T j q i : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w) (ht : t<n)
    (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hU : 1≤U) (hv : 1≤v)
    (hq : 1≤q) (hqv : q≤v) (hi : i<T) (hband : T≤i+j)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ i, i<M → f (n+h+i)=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → f x=false)
    (hA2 : ∀ i, i<L → f (n+h+M+m+i)=true)
    (hS3 : ∀ x, n+h+M+m+L≤x → x<n+h+M+m+L+s → f x=false)
    (hA3 : ∀ i, i<U → f (n+h+M+m+L+s+i)=true)
    (hS4 : ∀ x, n+h+M+m+L+s+U≤x → x<n+h+M+m+L+s+U+v → f x=false)
    (hA4 : ∀ i, i<T → f (n+h+M+m+L+s+U+v+i)=true)
    (hzero : cN (EndN f 0) 0 n=cN (fun x => f x=false) 0 n)
    (hpos : ∀ k, n<k → k≤n+h+M+m+L+s+U+v+T+j →
      cN (EndN f 0) 0 k+1≤cN (fun x => f x=false) 0 k)
    (hgap : ∀ x, n+h+M+m+L+s+U+v+T≤x → x<n+h+M+m+L+s+U+v+T+j → f x=false)
    (he : EndN f 0 (n+h+M+m+L+s+U+v+T+j))
    (htarget : Win f t (n+h+M+m+L+s+U+v+T+j-t))
    (hlocal : Win f (n+h+M+m+L+s+U+v-q) (q+i))
    (hbad : cN (fun x => f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)<j+1) :
    4≤cN (fun x => f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T) ∧
    cN (fun x => f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)≤12 ∧
    cN (fun x => f x=true) n (h+M+m+L+s+U+v+T)≤29 ∧ j≤12 := by
  have hrel : ∀ k, 0<k → k≤h+M+m+L+s+U+v+T →
      cN (EndN f 0) n k+1≤cN (fun x=>f x=false) n k := by
    intro k hk hkB
    have hp:=hpos (n+k) (by omega) (by omega)
    have hE:=cN_add (EndN f 0) 0 n k
    have hS:=cN_add (fun x=>f x=false) 0 n k
    simp only [Nat.zero_add] at hE hS
    omega
  exact final_S_counterexample_band_twelve f n t h M m L s U v T j q i w hw hpre ht
    hM hm hL hs hU hv hq hqv hi hband hS hA hS2 hA2 hS3 hA3 hS4 hA4
    hrel hgap he htarget hlocal hbad

open Classical in
/-- Base/count adapter only; the substantive source/count bounds are
proved in FourRunTargetArea/AdjacentRunSupply/FourRunSupplySeventeen. -/
theorem final_S_band_int_twelve (e : Int → Bool) (p : Int) (n a t h M m L s U v T j q i : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : segment e p n=w++List.replicate a true) (ht : t<n)
    (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hU : 1≤U) (hv : 1≤v)
    (hq : 1≤q) (hqv : q≤v) (hi : i<T) (hband : T≤i+j)
    (hS : ∀ x, n≤x → x<n+h → e (p+(x : Int))=false)
    (hA : ∀ k, k<M → e (p+((n+h+k : Nat) : Int))=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → e (p+(x : Int))=false)
    (hA2 : ∀ k, k<L → e (p+((n+h+M+m+k : Nat) : Int))=true)
    (hS3 : ∀ x, n+h+M+m+L≤x → x<n+h+M+m+L+s → e (p+(x : Int))=false)
    (hA3 : ∀ k, k<U → e (p+((n+h+M+m+L+s+k : Nat) : Int))=true)
    (hS4 : ∀ x, n+h+M+m+L+s+U≤x → x<n+h+M+m+L+s+U+v → e (p+(x : Int))=false)
    (hA4 : ∀ k, k<T → e (p+((n+h+M+m+L+s+U+v+k : Nat) : Int))=true)
    (hzero : endableCount e p n=subtractionCount e p n)
    (hpos : ∀ k, n<k → k≤n+h+M+m+L+s+U+v+T+j → endableCount e p k+1≤subtractionCount e p k)
    (hgap : ∀ x, n+h+M+m+L+s+U+v+T≤x → x<n+h+M+m+L+s+U+v+T+j → e (p+(x : Int))=false)
    (he : Endable e p (p+((n+h+M+m+L+s+U+v+T+j : Nat) : Int)))
    (htarget : P2 (past e (p+((n+h+M+m+L+s+U+v+T+j : Nat) : Int)) (n+h+M+m+L+s+U+v+T+j-t)))
    (hlocal : P2 (past e (p+((n+h+M+m+L+s+U+v+i : Nat) : Int)) (q+i)))
    (hbad : countP (fun x=>e x=true ∧ ¬Endable e p x) (p+(n : Int)) (h+M+m+L+s+U+v+T)<j+1) :
    4≤countP (fun x=>e x=true ∧ ¬Endable e p x) (p+(n : Int)) (h+M+m+L+s+U+v+T) ∧ countP (fun x=>e x=true ∧ ¬Endable e p x) (p+(n : Int)) (h+M+m+L+s+U+v+T)≤12 ∧
    countP (fun x=>e x=true) (p+(n : Int)) (h+M+m+L+s+U+v+T)≤29 ∧ j≤12 := by
  rw [segment_seg e p p 0 (by simp)] at hpre
  simp only [endableCount_shift,subtractionCount_shift] at hzero hpos
  rw [nonsupplied_count_shift] at hbad ⊢
  rw [countP_cN (fun x=>e x=true) p (p+(n : Int)) n rfl]
  have hW : Win (fun k=>e (p+(k : Int))) t (n+h+M+m+L+s+U+v+T+j-t) := by
    apply Recaman.FourRunSourceBase.P2_shifted_window e p t (n+h+M+m+L+s+U+v+T+j-t) (by omega)
    simpa only [show t+(n+h+M+m+L+s+U+v+T+j-t)=n+h+M+m+L+s+U+v+T+j by omega] using htarget
  have hV : Win (fun k=>e (p+(k : Int))) (n+h+M+m+L+s+U+v-q) (q+i) := by
    apply Recaman.FourRunSourceBase.P2_shifted_window e p (n+h+M+m+L+s+U+v-q) (q+i) (by omega)
    simpa only [show n+h+M+m+L+s+U+v-q+(q+i)=n+h+M+m+L+s+U+v+i by omega] using hlocal
  exact final_S_band_from_zero_twelve (fun k=>e (p+(k : Int))) n t h M m L s U v T j q i
    (w++List.replicate a true) (block_append hw (block_replicate_A a)) hpre ht
    hM hm hL hs hU hv hq hqv hi hband hS hA hS2 hA2 hS3 hA3 hS4 hA4
    hzero hpos hgap ((endable_iff e p p _ 0 (n+h+M+m+L+s+U+v+T+j) (by simp) rfl).mp he) hW hV hbad

end Recaman.FinalSSourceResidual
