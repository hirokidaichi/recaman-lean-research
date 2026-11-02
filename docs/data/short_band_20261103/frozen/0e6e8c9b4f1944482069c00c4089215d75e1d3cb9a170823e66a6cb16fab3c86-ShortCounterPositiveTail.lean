import Recaman.ThreeRunWindowGap
import Recaman.ShortTargetCounter

namespace Recaman.ShortCounterPositiveTail

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- A genuine fourth A run is forced by the actual counter; no A sign
at the target endpoint is an input. The same target start is retained. -/
theorem short_counter_positive_tail (f : Nat → Bool) (n t h M m L s U v T j C : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w) (ht : t<n)
    (hh : 1≤h) (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hU : 1≤U)
    (hv : v<C) (hvpos : 1≤v) (hC4 : 4≤C)
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
    (hpos : ∀ k, 0<k → k≤h+M+m+L+s+U+v+T →
      cN (EndN f 0) n k+1≤cN (fun x=>f x=false) n k)
    (hbad : cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)<j+1) :
    1≤T ∧ C-v<j+1 := by
  have hb:=Recaman.ShortTargetCounter.short_target_counter f n t h M m L s U v T j C w hw hpre ht
    hh hM hm hL hs hU hv hvpos hC4 hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad
  have hTpos : 1≤T := by
    by_cases hhT : 1≤T
    · exact hhT
    have hT0 : T=0 := by omega
    have hmerged : ∀ x, n+h+M+m+L+s+U≤x → x<n+h+M+m+L+s+U+(v+j) → f x=false := by
      intro x hx hxB
      by_cases hxv : x<n+h+M+m+L+s+U+v
      · exact hS4 x hx hxv
      · exact hgap x (by omega) (by omega)
    have hw' : Win f t (n+h+M+m+L+s+U+(v+j)-t) := by
      simpa only [hT0,Nat.add_zero,Nat.add_assoc] using htarget
    have hfree:=Recaman.ThreeRunWindowGap.three_run_window_gap f n h M m L s U (v+j) t w hw hpre
      hM hm hL hs hU hS hA hS2 hA2 hS3 hA3
      (fun k hk hkB=>hpos k hk (by omega)) hmerged hw'
    let H:=h+M+m+L+s+U
    let P:=fun x=>f x=true ∧ ¬EndN f 0 x
    have hsep : cN P (n+H) v=0 := by
      apply cN_zero_of
      intro x hx hxB hp
      have hf:=hS4 x (by dsimp [H] at hx; omega) (by dsimp [H] at hxB; omega)
      have ha:=hp.1
      rw [hf] at ha
      contradiction
    have hadd:=cN_add P n H v
    change v+j+1≤cN P n H at hfree
    have hbad' : cN P n (H+v)<j+1 := by
      simpa only [hT0,Nat.add_zero] using hbad
    omega
  exact ⟨hTpos,by have hx:=hb.1; omega⟩

end Recaman.ShortCounterPositiveTail
