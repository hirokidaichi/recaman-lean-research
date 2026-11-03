import Recaman.UnitOneLastFive
import Recaman.FourRunSourceBase

namespace Recaman.UnitOneLastFiveBase

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic


/-- Original zero/full positivity supplies relative counts for the mass2/separator>=5 full free-gap inequality. Every old source is retained. -/
theorem unit_one_counter_from_zero (f : Nat → Bool) (n t h M m L s U v T j C : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w) (ht : t<n)
    (hh : 1≤h) (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hU : 1≤U)
    (hv : v=1) (hC1 : C=1)
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
    (hC : mass (w.drop t)=(C : Int))
    (hzero : cN (EndN f 0) 0 n=cN (fun x=>f x=false) 0 n)
    (hpos : ∀ k, n<k → k≤n+h+M+m+L+s+U+v+T+j →
      cN (EndN f 0) 0 k+1≤cN (fun x=>f x=false) 0 k)
    (hbad : cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)<j+1)
    (hnoOld : ∀ k, k<T → ∀ r, r<n → ¬Win f r (n+h+M+m+L+s+U+v+k-r))
 :
    cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)=j := by
  have hrel : ∀ k, 0<k → k≤h+M+m+L+s+U+v+T →
      cN (EndN f 0) n k+1≤cN (fun x=>f x=false) n k := by
    intro k hk hkB
    have hp:=hpos (n+k) (by omega) (by omega)
    have hE:=cN_add (EndN f 0) 0 n k
    have hS:=cN_add (fun x=>f x=false) 0 n k
    simp only [Nat.zero_add] at hE hS
    omega
  have hlast:=Recaman.UnitOneLastFive.unit_one_counter_last_five f n t h M m L s U v T j w hw hpre ht
    hh hM hm hL hs hU hv hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget (by omega) hrel hbad hnoOld
  exact hlast.2

open Classical in
theorem unit_one_counter_int (e : Int → Bool) (p : Int) (n a t h M m L s U v T j C : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : segment e p n=w++List.replicate a true) (ht : t<n)
    (hh : 1≤h) (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hU : 1≤U)
    (hv : v=1) (hC1 : C=1)
    (hzeroMass : M+L+U=h+m+s)
    (hS : ∀ x, n≤x → x<n+h → e (p+(x : Int))=false)
    (hA : ∀ k, k<M → e (p+((n+h+k : Nat) : Int))=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → e (p+(x : Int))=false)
    (hA2 : ∀ k, k<L → e (p+((n+h+M+m+k : Nat) : Int))=true)
    (hS3 : ∀ x, n+h+M+m+L≤x → x<n+h+M+m+L+s → e (p+(x : Int))=false)
    (hA3 : ∀ k, k<U → e (p+((n+h+M+m+L+s+k : Nat) : Int))=true)
    (hS4 : ∀ x, n+h+M+m+L+s+U≤x → x<n+h+M+m+L+s+U+v → e (p+(x : Int))=false)
    (hA4 : ∀ k, k<T → e (p+((n+h+M+m+L+s+U+v+k : Nat) : Int))=true)
    (hgap : ∀ x, n+h+M+m+L+s+U+v+T≤x → x<n+h+M+m+L+s+U+v+T+j → e (p+(x : Int))=false)
    (htarget : P2 (past e (p+((n+h+M+m+L+s+U+v+T+j : Nat) : Int)) (n+h+M+m+L+s+U+v+T+j-t)))
    (hC : mass (segment e (p+(t : Int)) (n-t))=(C : Int))
    (hzero : endableCount e p n=subtractionCount e p n)
    (hpos : ∀ k, n<k → k≤n+h+M+m+L+s+U+v+T+j →
      endableCount e p k+1≤subtractionCount e p k)
    (hbad : countP (fun x=>e x=true ∧ ¬Endable e p x) (p+(n : Int)) (h+M+m+L+s+U+v+T)<j+1)
    (hnoOld : ∀ k, k<T → ∀ r, r<n → ¬P2 (past e (p+((n+h+M+m+L+s+U+v+k : Nat) : Int)) (n+h+M+m+L+s+U+v+k-r)))
 :
    countP (fun x=>e x=true ∧ ¬Endable e p x) (p+(n : Int)) (h+M+m+L+s+U+v+T)=j := by
  rw [segment_seg e p p 0 (by simp)] at hpre
  simp only [endableCount_shift,subtractionCount_shift] at hzero hpos
  rw [nonsupplied_count_shift] at hbad
  simp only [nonsupplied_count_shift]
  have hW : Win (fun k=>e (p+(k : Int))) t (n+h+M+m+L+s+U+v+T+j-t) := by
    apply Recaman.FourRunSourceBase.P2_shifted_window e p t (n+h+M+m+L+s+U+v+T+j-t) (by omega)
    simpa only [show t+(n+h+M+m+L+s+U+v+T+j-t)=n+h+M+m+L+s+U+v+T+j by omega] using htarget
  have hN : ∀ k, k<T → ∀ r, r<n →
      ¬Win (fun i=>e (p+(i : Int))) r (n+h+M+m+L+s+U+v+k-r) := by
    intro k hk r hr hw
    apply hnoOld k hk r hr
    have hb:=past_bridge e p r (n+h+M+m+L+s+U+v+k-r)
    have hsum : r+(n+h+M+m+L+s+U+v+k-r)=n+h+M+m+L+s+U+v+k := by omega
    rw [hsum] at hb
    constructor
    · rw [hb.1]
      have hm:=hw.2.1
      rw [hsum] at hm
      omega
    · exact hb.2.trans hw.2.2
  rw [segment_seg e p (p+(t : Int)) t rfl] at hC
  have hd:=seg_drop (fun k=>e (p+(k : Int))) 0 n t (by omega)
  simp only [Nat.zero_add,hpre] at hd
  rw [←hd] at hC
  exact unit_one_counter_from_zero (fun k=>e (p+(k : Int))) n t h M m L s U v T j C
    (w++List.replicate a true) (block_append hw (block_replicate_A a)) hpre ht hh hM hm hL hs hU hv hC1 hzeroMass
    hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap hW hC hzero hpos hbad hN

end Recaman.UnitOneLastFiveBase
