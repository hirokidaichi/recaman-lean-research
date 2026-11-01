import Recaman.TenHeadFreeGap
import Recaman.FourRunSourceBase

namespace Recaman.TenHeadFreeBase

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.TenHeadFreeGap

/-- Original Nat zero and full positive deficit supply the relative
premise for the ten-A/ten-S three-run-head subfamily. -/
theorem ten_head_gap_from_zero (f : Nat → Bool) (n t h M m L s U v T j q i : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w) (ht : t<n)
    (hh : 1≤h) (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hU : 1≤U)
    (hS10 : h+m+s=10) (hA10 : M+L+U=10)
    (hz : seg f n 20=List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true)
    (B : Int) (haz : areaW (seg f n 20)= -B) (hlo : 46≤B) (hhi : B≤64)
    (hv : 1≤v) (hq : 1≤q) (hqv : q≤v) (hi : i<T) (hband : T≤i+j)
    (hS : ∀ x, n+20≤x → x<n+20+v → f x=false)
    (hA : ∀ k, k<T → f (n+20+v+k)=true)
    (hgap : ∀ x, n+20+v+T≤x → x<n+20+v+T+j → f x=false)
    (htarget : Win f t (n+20+v+T+j-t))
    (hlocal : Win f (n+20+v-q) (q+i))
    (hzero : cN (EndN f 0) 0 n=cN (fun x=>f x=false) 0 n)
    (hpos : ∀ k, n<k → k≤n+20+v+T+j → cN (EndN f 0) 0 k+1≤cN (fun x=>f x=false) 0 k) :
    j+1≤cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (20+v+T) := by
  have hrel : ∀ k, 0<k → k≤20+v+T → cN (EndN f 0) n k+1≤cN (fun x=>f x=false) n k := by
    intro k hk hkB
    have hp:=hpos (n+k) (by omega) (by omega)
    have hE:=cN_add (EndN f 0) 0 n k
    have hS:=cN_add (fun x=>f x=false) 0 n k
    simp only [Nat.zero_add] at hE hS
    omega
  exact ten_head_final_S_free_gap f n t h M m L s U v T j q i w hw hpre ht hh hM hm hL hs hU
    hS10 hA10 hz B haz hlo hhi hv hq hqv hi hband hS hA hgap htarget hlocal hrel

open Classical in
/-- Original Int p and padded BlockWord prefix, with the same old target
and final-S local P2 windows. This is the full ten-head moment-band
subfamily, not an unrestricted four-run free-gap theorem. -/
theorem ten_head_gap_int (e : Int → Bool) (p : Int) (n a t h M m L s U v T j q i : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : segment e p n=w++List.replicate a true) (ht : t<n)
    (hh : 1≤h) (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hU : 1≤U)
    (hS10 : h+m+s=10) (hA10 : M+L+U=10)
    (hz : segment e (p+(n : Int)) 20=List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true)
    (B : Int) (haz : areaW (segment e (p+(n : Int)) 20)= -B) (hlo : 46≤B) (hhi : B≤64)
    (hv : 1≤v) (hq : 1≤q) (hqv : q≤v) (hi : i<T) (hband : T≤i+j)
    (hS : ∀ x, n+20≤x → x<n+20+v → e (p+(x : Int))=false)
    (hA : ∀ k, k<T → e (p+((n+20+v+k : Nat) : Int))=true)
    (hgap : ∀ x, n+20+v+T≤x → x<n+20+v+T+j → e (p+(x : Int))=false)
    (htarget : P2 (past e (p+((n+20+v+T+j : Nat) : Int)) (n+20+v+T+j-t)))
    (hlocal : P2 (past e (p+((n+20+v+i : Nat) : Int)) (q+i)))
    (hzero : endableCount e p n=subtractionCount e p n)
    (hpos : ∀ k, n<k → k≤n+20+v+T+j → endableCount e p k+1≤subtractionCount e p k) :
    j+1≤countP (fun x=>e x=true ∧ ¬Endable e p x) (p+(n : Int)) (20+v+T) := by
  rw [segment_seg e p p 0 (by simp)] at hpre
  rw [segment_seg e p (p+(n : Int)) n rfl] at hz haz
  simp only [endableCount_shift,subtractionCount_shift] at hzero hpos
  rw [nonsupplied_count_shift]
  have hW : Win (fun k=>e (p+(k : Int))) t (n+20+v+T+j-t) := by
    apply Recaman.FourRunSourceBase.P2_shifted_window e p t (n+20+v+T+j-t) (by omega)
    simpa only [show t+(n+20+v+T+j-t)=n+20+v+T+j by omega] using htarget
  have hV : Win (fun k=>e (p+(k : Int))) (n+20+v-q) (q+i) := by
    apply Recaman.FourRunSourceBase.P2_shifted_window e p (n+20+v-q) (q+i) (by omega)
    simpa only [show n+20+v-q+(q+i)=n+20+v+i by omega] using hlocal
  exact ten_head_gap_from_zero (fun k=>e (p+(k : Int))) n t h M m L s U v T j q i
    (w++List.replicate a true) (block_append hw (block_replicate_A a)) hpre ht hh hM hm hL hs hU hS10 hA10
    hz B haz hlo hhi hv hq hqv hi hband hS hA hgap hW hV hzero hpos

end Recaman.TenHeadFreeBase
