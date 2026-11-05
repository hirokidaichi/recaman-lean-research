import Recaman.FourDelayedCounterData
import Recaman.FourthDelayedWitness
import Recaman.GapFourClockReduction
import Recaman.GapFourScalar

namespace Recaman.FourGapFourCandidate

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- The exact gap4 source clocks force too little cross for a
saturated original head. -/
theorem actual_gap_four_candidate (f : Nat → Bool) (n t h M m L s U v T j C : Nat)
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
    (hbad : cN (fun x => f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)<j+1) (hj : j=4) :
    cN (EndN f 0) n (h+M+m+L+s+U)=10 ∧ M+L=9 ∧ M*(m+s)+L*s≤14 := by
  subst j
  let H:=h+M+m+L+s+U
  let B:=H+v
  let A:=cN (fun x=>f x=true) n (B+T)
  let F:=cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (B+T)
  let r:=cN (fun x=>f x=true ∧ ¬EndN f 0 x) n H
  let EH:=cN (EndN f 0) n H
  let E:=cN (EndN f 0) (n+B) T
  obtain ⟨hC2,hAlo,hAeq,hcount,_,hEH,hr,hF,hE7,hfree,hMcost,hW,_,hpair,hsq,hword⟩:=
    Recaman.FourDelayedCounterData.four_delayed_counter_data f n t h M m L s U v T 4 C w hw hpre ht hC
      hM hL hU hT hm hs hv hS hA hS2 hA2 hS3 hA3 hS4 hA4 hpos hgap htarget hbad (by omega)
  have hw0 : BlockWord (seg f 0 n) := by rw [hpre]; exact hw
  have hC2' : 2≤mass (seg f t (n-t)) := by rw [hC]; omega
  have hA4' : ∀ i, i<T → f (n+B+i)=true := by simpa only [B,H,Nat.add_assoc] using hA4
  have hgap' : ∀ x, n+B+T≤x → x<n+B+T+4 → f x=false := by simpa only [B,H,Nat.add_assoc] using hgap
  have htarget' : Win f t (n+B+T+4-t) := by simpa only [B,H,Nat.add_assoc] using htarget
  change F≤4 at hF
  change 4≤r at hr
  change T+r≤F+E at hfree
  change A=EH+E+F at hcount
  change A=M+L+U+T at hAeq
  have hET : E≤T := Recaman.ClockCountSaturation.count_le_length (EndN f 0) (n+B) T
  have hr4 : r=4 := by omega
  have hF4 : F=4 := by omega
  have hfull : E=T := by omega
  have hT7 : T≤7 := by change E≤7 at hE7; omega
  have hM6 : M≤6 := by change M≤r+2 at hMcost; omega
  have hW9 : M+L≤9 := by change M+L≤r+5 at hW; omega
  have hU5 (hw9 : M+L=9) : U≤5 := by change EH≤10 at hEH; omega
  have hcase:=Recaman.GapFourClockReduction.gap_four_clock_reduction f (n+B) T M L s U v
    hv hT hM6 hW9 hU5 hfull hpair
    (fun i hi hd he=>Recaman.FourthDelayedWitness.fourth_delayed_pair_support f n t B h M m L s U v T 4 i
      hw0 ht (by omega) hv hC2' hword hA4' hgap' htarget' hi hd he)
    (fun i hi hd he=>Recaman.FourthDelayedWitness.fourth_third_S_tail_support f n t B h M m L s U v T 4 i
      hw0 ht (by omega) hv hL hC2' hword hA4' hgap' htarget' hi hd he)
    (fun i k hk hi hd he=>Recaman.FourthDelayedWitness.fourth_second_A_tail_support f n t B h M m L s U v T 4 i k
      hw0 ht (by omega) hv hk hC2' hword hA4' hgap' htarget' hi hd he)
  obtain ⟨hW9,hcase⟩:=hcase
  have hhead : EH=5+U := by omega
  obtain ⟨hHead10,hI⟩:=Recaman.GapFourScalar.gap_four_head_candidate M m L s U v T C A EH
    hM hm hs hU hv hC2 hT7 hW9 hEH hhead hAeq hcase hsq
  exact ⟨hHead10,hW9,hI⟩

end Recaman.FourGapFourCandidate
