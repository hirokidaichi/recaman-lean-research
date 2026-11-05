import Recaman.FourMeasuredCounts
import Recaman.FourthDelayedCuts
import Recaman.ThreeHeadFreeCuts
import Recaman.FourCrossExact
import Recaman.FourRunSupplySeventeen
import Recaman.OldTargetHeadSupplyFloor

namespace Recaman.FourDelayedCounterData

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- The actual head must pay j+1 clocks. Retain both delayed cutoff
budgets and the exact cross in the same original target square. -/
theorem four_delayed_counter_data (f : Nat → Bool) (n t h M m L s U v T j C : Nat)
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
    (hbad : cN (fun x => f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)<j+1) (hj : 4≤j) :
    let H:=h+M+m+L+s+U
    let B:=H+v
    let N:=M+L+U
    let I:=M*(m+s)+L*s
    let A:=cN (fun x=>f x=true) n (B+T)
    let P:=fun x=>f x=true ∧ ¬EndN f 0 x
    let F:=cN P n (B+T)
    let r:=cN P n H
    let EH:=cN (EndN f 0) n H
    let E:=cN (EndN f 0) (n+B) T
    2≤C ∧ 2*j+3≤A ∧ A=N+T ∧ A=EH+E+F ∧ j+1≤EH ∧ EH≤10 ∧
    4≤r ∧ F≤j ∧ T+r≤F+E ∧ M≤r+2 ∧ M+L≤r+5 ∧
    E≤max (T-j) (M+T-(2*j+1))+3 ∧
    E≤max (T-j) (M+L+T-(2*j+1))+1 ∧
    (C : Int)^2+((j : Int)+1)^2+2*((N : Int)*(v : Int)+(I : Int))≤
      ((A : Int)-((j : Int)+1))^2+1 := by
  dsimp only
  let H:=h+M+m+L+s+U
  let B:=H+v
  let N:=M+L+U
  let I:=M*(m+s)+L*s
  let A:=cN (fun x=>f x=true) n (B+T)
  let P:=fun x=>f x=true ∧ ¬EndN f 0 x
  let F:=cN P n (B+T)
  let r:=cN P n H
  let EH:=cN (EndN f 0) n H
  let E:=cN (EndN f 0) (n+B) T
  have hc:=Recaman.FourMeasuredCounts.measured_counts f n h M m L s U v T w hw hpre
    hM hm hs hv hS hA hS2 hA2 hS3 hA3 hS4 hA4 hpos
  change EH≤10 ∧ E≤7 ∧ A=EH+E+F ∧ T+r≤F+E ∧ (r≤3 → EH≤r+1) ∧ _ at hc
  obtain ⟨hEH,_,hcount,hfree,hrsmall,hword⟩:=hc
  have hA4' : ∀ i, i<T → f (n+B+i)=true := by simpa only [B,H,Nat.add_assoc] using hA4
  have hgap' : ∀ a, n+B+T≤a → a<n+B+T+j → f a=false := by simpa only [B,H,Nat.add_assoc] using hgap
  have hW : Win f t (n+B+T+j-t) := by simpa only [B,H,Nat.add_assoc] using htarget
  have hF : F≤j := by change F<j+1 at hbad; omega
  have hC2:=Recaman.OldTargetFreeAccounting.old_target_counter_mass f n t (B+T) j C (by omega) hC
    (hpos (B+T) (by dsimp [B,H]; omega) (by omega))
    (by simpa only [Nat.add_assoc] using hgap') (by simpa only [Nat.add_assoc] using hW) hbad
  have hC2' : 2≤mass (seg f t (n-t)) := by rw [hC]; omega
  have hAlo : 2*j+3≤A := Recaman.PrimitiveOldTargetCut.actual_old_target_A_cut
    f n t (B+T) j w hw hpre ht hC2'
    (by simpa only [Nat.add_assoc] using hgap') (by simpa only [Nat.add_assoc] using hW)
  have hw0 : BlockWord (seg f 0 n) := by rw [hpre]; exact hw
  have hNA : cN (fun x=>f x=true) n B=N := by
    have hn := ones_seg_eq_count f n B
    rw [hword] at hn
    simp only [ones_append,ones_replicate_A,ones_replicate_S,Int.zero_add,Int.add_zero] at hn
    dsimp [N]
    omega
  have hAeq : A=N+T := by
    have he:=cN_add (fun x=>f x=true) n B T
    rw [hNA,count_A_run f (n+B) T hA4'] at he
    exact he
  have hHfloor:=Recaman.OldTargetHeadSupplyFloor.old_target_head_supply_floor f n t B T j
    hw0 ht (by omega) hC2' (by rw [hNA]; dsimp [N]; omega)
    (fun k hk hkB=>hpos k hk (by omega)) hA4' hgap' hW hbad
  have hHEq : cN (EndN f 0) n B=EH := by
    have hp:=addition_endable_partition f n (B+T)
    rw [cN_add (EndN f 0) n B T] at hp
    change A=cN (EndN f 0) n B+E+F at hp
    omega
  rw [hHEq] at hHfloor
  have hr4 : 4≤r := by
    by_cases he : r≤3
    · have hh:=hrsmall he
      omega
    · omega
  have hheadCuts:=Recaman.ThreeHeadFreeCuts.head_free_cuts f n h M m L s U w hw hpre
    hS hA hS2 hA2 (fun k hk hkH=>hpos k hk (by omega))
  have hcuts:=Recaman.FourthDelayedCuts.fourth_delayed_cuts f n t B h M m L s U v T j
    hw0 ht (by omega) hv hC2' hword hA4' hgap' hW
  have hraw:=Recaman.FourRunSupplySeventeen.four_run_word f n h M m L s U v T
    hS hA hS2 hA2 hS3 hA3 hS4 hA4
  have hcross : 2*(2*((N : Int)*(v : Int)+(I : Int)))≤
      runKey (seg f n (B+T))+2*(cntF (seg f n (B+T)) : Int)^2 := by
    rw [hraw,Recaman.FourCrossExact.four_cross_exact]
    dsimp only [N,I]
    simp only [Int.natCast_add,Int.natCast_mul]
    grind only
  have hsq:=Recaman.GenuineFourCross.actual_cross_charge f n t (B+T) j
    (2*((N : Int)*(v : Int)+(I : Int))) w hw hpre ht hcross
    (by simpa only [Nat.add_assoc] using hgap') (by simpa only [Nat.add_assoc] using hW)
  rw [hC] at hsq
  exact ⟨hC2,hAlo,hAeq,hcount,hHfloor,hEH,hr4,hF,hfree,hheadCuts.1,hheadCuts.2,hcuts.1,hcuts.2,hsq⟩

end Recaman.FourDelayedCounterData
