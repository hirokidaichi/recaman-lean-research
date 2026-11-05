import Recaman.FourMeasuredCounts
import Recaman.FourthEarlyCuts
import Recaman.ThreeHeadFreeCuts
import Recaman.FourCrossExact
import Recaman.FourRunSupplySeventeen
import Recaman.HighGapScalarCuts

namespace Recaman.FourHighGapCandidate

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- The original counts force all three separators to have length one
if a counter with gap at least nine exists. -/
theorem actual_high_gap_unit_candidate (f : Nat → Bool) (n t h M m L s U v T j C : Nat)
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
    (hbad : cN (fun x => f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)<j+1) (hj : 9≤j) :
    let B:=h+M+m+L+s+U+v
    j=9 ∧ cN (fun x=>f x=true) n (B+T)=24 ∧ T≤6 ∧ m=1 ∧ s=1 ∧ v=1 ∧
    5≤cN (EndN f 0) (n+B) T ∧
    seg f n B=List.replicate h false++(List.replicate M true++
      List.replicate m false++List.replicate L true++List.replicate s false++
      List.replicate U true++List.replicate v false) := by
  dsimp only
  let H:=h+M+m+L+s+U
  let B:=H+v
  let A:=cN (fun x=>f x=true) n (B+T)
  let P:=fun x=>f x=true ∧ ¬EndN f 0 x
  let F:=cN P n (B+T)
  let r:=cN P n H
  let EH:=cN (EndN f 0) n H
  let E:=cN (EndN f 0) (n+B) T
  let Q:=((M : Int)+(L : Int)+(U : Int))*(v : Int)+(M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int)
  have hc:=Recaman.FourMeasuredCounts.measured_counts f n h M m L s U v T w hw hpre
    hM hm hs hv hS hA hS2 hA2 hS3 hA3 hS4 hA4 hpos
  change EH≤10 ∧ E≤7 ∧ A=EH+E+F ∧ T+r≤F+E ∧ (r≤3 → EH≤r+1) ∧ _ at hc
  obtain ⟨hEH,hE,hcount,hfree0,hrsmall,hword⟩:=hc
  have hA4' : ∀ i, i<T → f (n+B+i)=true := by simpa only [B,H,Nat.add_assoc] using hA4
  have hgap' : ∀ a, n+B+T≤a → a<n+B+T+j → f a=false := by simpa only [B,H,Nat.add_assoc] using hgap
  have hW : Win f t (n+B+T+j-t) := by simpa only [B,H,Nat.add_assoc] using htarget
  have hF : F≤j := by change F<j+1 at hbad; omega
  have hfree : T+r≤j+E := Nat.le_trans hfree0 (Nat.add_le_add_right hF E)
  have hC2:=Recaman.OldTargetFreeAccounting.old_target_counter_mass f n t (B+T) j C (by omega) hC
    (hpos (B+T) (by dsimp [B,H]; omega) (by omega))
    (by simpa only [Nat.add_assoc] using hgap') (by simpa only [Nat.add_assoc] using hW) hbad
  have hAlo : 2*j+3≤A := Recaman.PrimitiveOldTargetCut.actual_old_target_A_cut
    f n t (B+T) j w hw hpre ht (by rw [hC]; omega)
    (by simpa only [Nat.add_assoc] using hgap') (by simpa only [Nat.add_assoc] using hW)
  have hr4 : 4≤r := by
    by_cases hr : r≤3
    · have he:=hrsmall hr
      omega
    · omega
  have hMcost : M≤r+2 :=
    (Recaman.ThreeHeadFreeCuts.head_free_cuts f n h M m L s U w hw hpre
      hS hA hS2 hA2 (fun k hk hkH=>hpos k hk (by omega))).1
  have hw0 : BlockWord (seg f 0 n) := by rw [hpre]; exact hw
  have hcuts:=Recaman.FourthEarlyCuts.fourth_early_cuts f n t B h M m L s U v T j
    hw0 ht (by omega) hv hword hA4' hgap' hW
  change E≤T-j+5 ∧ (M≤j → E≤T-j+3) ∧ (M+L≤j → E≤T-j+1) at hcuts
  obtain ⟨hcut0,hcut1,hcut2⟩:=hcuts
  have hraw:=Recaman.FourRunSupplySeventeen.four_run_word f n h M m L s U v T
    hS hA hS2 hA2 hS3 hA3 hS4 hA4
  have hAeq : A=M+L+U+T := by
    have he:=ones_seg_eq_count f n (B+T)
    change ones (seg f n (B+T))=(A : Int) at he
    rw [hraw] at he
    simp only [ones_append,ones_replicate_A,ones_replicate_S] at he
    omega
  have hcross : 2*(2*Q)≤runKey (seg f n (B+T))+2*(cntF (seg f n (B+T)) : Int)^2 := by
    rw [hraw,Recaman.FourCrossExact.four_cross_exact]
    change 2*(2*Q)≤4*Q
    omega
  have hsq:=Recaman.GenuineFourCross.actual_cross_charge f n t (B+T) j (2*Q) w hw hpre ht
    hcross (by simpa only [Nat.add_assoc] using hgap') (by simpa only [Nat.add_assoc] using hW)
  rw [hC] at hsq
  obtain ⟨hj9,hA24,hT6,hm1,hs1,hv1,hE5⟩:=Recaman.HighGapScalarCuts.high_gap_unit_candidate_nat
    j M m L s U v T C A r EH E F hj hM hm hL hs hU hv hC2 hAlo hcount hEH hF hr4 hE hfree
    hMcost hAeq (fun ht=>by simpa only [Nat.sub_eq_zero_of_le ht,Nat.zero_add] using hcut0)
    (fun hM _=>hcut1 hM) (fun hM ht=>by simpa only [Nat.sub_eq_zero_of_le ht,Nat.zero_add] using hcut1 hM)
    (fun hML ht=>by simpa only [Nat.sub_eq_zero_of_le ht,Nat.zero_add] using hcut2 hML) hsq
  exact ⟨hj9,hA24,hT6,hm1,hs1,hv1,hE5,hword⟩

end Recaman.FourHighGapCandidate
