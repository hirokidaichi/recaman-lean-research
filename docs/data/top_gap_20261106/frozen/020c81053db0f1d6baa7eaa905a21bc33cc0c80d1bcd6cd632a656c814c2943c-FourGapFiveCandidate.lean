import Recaman.FourDelayedCounterData
import Recaman.FourthDelayedWitness
import Recaman.GapFiveClockReduction
import Recaman.GapFiveScalar

namespace Recaman.FourGapFiveCandidate

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- The exact gap5 source clocks force too little cross for a
saturated original head. -/
theorem actual_gap_five_candidate (f : Nat → Bool) (n t h M m L s U v T j C : Nat)
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
    (hbad : cN (fun x => f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)<j+1) (hj : j=5) :
    cN (EndN f 0) n (h+M+m+L+s+U)=10 ∧ M*(m+s)+L*s≤7 := by
  subst j
  let H:=h+M+m+L+s+U
  let B:=H+v
  let A:=cN (fun x=>f x=true) n (B+T)
  let F:=cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (B+T)
  let r:=cN (fun x=>f x=true ∧ ¬EndN f 0 x) n H
  let EH:=cN (EndN f 0) n H
  let E:=cN (EndN f 0) (n+B) T
  obtain ⟨hC2,hAlo,hAeq,hcount,_,hEH,hr,hF,_,hfree,_,hW,_,hpair,hsq,hword⟩:=
    Recaman.FourDelayedCounterData.four_delayed_counter_data f n t h M m L s U v T 5 C w hw hpre ht hC
      hM hL hU hT hm hs hv hS hA hS2 hA2 hS3 hA3 hS4 hA4 hpos hgap htarget hbad (by omega)
  have hw0 : BlockWord (seg f 0 n) := by rw [hpre]; exact hw
  have hC2' : 2≤mass (seg f t (n-t)) := by rw [hC]; omega
  have hA4' : ∀ i, i<T → f (n+B+i)=true := by simpa only [B,H,Nat.add_assoc] using hA4
  have hgap' : ∀ x, n+B+T≤x → x<n+B+T+5 → f x=false := by simpa only [B,H,Nat.add_assoc] using hgap
  have htarget' : Win f t (n+B+T+5-t) := by simpa only [B,H,Nat.add_assoc] using htarget
  have hcase:=Recaman.GapFiveClockReduction.gap_five_clock_reduction f (n+B) T (M+L) s U v r hv hr hW
    (by change T+r≤F+E at hfree; change F≤5 at hF; change T+r≤5+E; omega) hpair
    (fun i hi hd he=>Recaman.FourthDelayedWitness.fourth_delayed_pair_support f n t B h M m L s U v T 5 i
      hw0 ht (by omega) hv hC2' hword hA4' hgap' htarget' hi hd he)
    (fun i hi hd he=>Recaman.FourthDelayedWitness.fourth_third_S_tail_support f n t B h M m L s U v T 5 i
      hw0 ht (by omega) hv hL hC2' hword hA4' hgap' htarget' hi hd he)
  exact Recaman.GapFiveScalar.gap_five_head_candidate M m L s U v T C A r EH E F
    hM hm hL hs hv hC2 hAlo hAeq hcount hEH hF hfree hcase hsq

end Recaman.FourGapFiveCandidate
