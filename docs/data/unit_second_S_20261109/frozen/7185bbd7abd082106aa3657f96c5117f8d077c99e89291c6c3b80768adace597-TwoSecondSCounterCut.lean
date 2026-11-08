import Recaman.SecondSTargetProfile
import Recaman.TwoSTargetBounds
import Recaman.TwoSActualLastBudget
import Recaman.UnitSActualLastBudget

namespace Recaman.TwoSecondSCounterCut

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

theorem two_second_S_counter_cut (f : Nat → Bool) (n h M m L s U v T j : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w)
    (hM : 1≤M) (hL : 1≤L) (hU : 1≤U) (hT : 1≤T) (hm : 2≤m) (hs : 1≤s) (hv : 1≤v)
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
    (htarget : Win f (n+h+M+m-2) (2+L+s+U+v+T+j))
    (hbad : cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)<j+1) :
    M≤7 ∧ L≤7 ∧ s+v≤11 ∧ 5≤j+1 ∧ j+1≤11 ∧ M+2+s+v≤14
 := by
  let H:=h+M+m+L+s+U
  let B:=H+v
  let A:=cN (fun x=>f x=true) n (B+T)
  let P:=fun x=>f x=true ∧ ¬EndN f 0 x
  let F:=cN P n (B+T)
  let r:=cN P n H
  let EH:=cN (EndN f 0) n H
  let E:=cN (EndN f 0) (n+B) T
  obtain ⟨hbal,hstrict,hsq⟩:=Recaman.SecondSTargetProfile.actual_second_S_target_profile
    f (n+h+M) m L s U v T j (n+h+M+m-2) (by omega) (by omega) hL hs
      hS2 hA2 hS3 hA3 hS4 hA4 hgap
        (by rw [show n+h+M+m+L+s+U+v+T+j-(n+h+M+m-2)=2+L+s+U+v+T+j by omega]; exact htarget)
  rw [show n+h+M+m-(n+h+M+m-2)=2 by omega] at hbal hstrict hsq
  obtain ⟨hEH,hE,hcount,hfree,hrsmall,hword⟩:=
    Recaman.FourMeasuredCounts.measured_counts f n h M m L s U v T w hw hpre
      hM (by omega) hs hv hS hA hS2 hA2 hS3 hA3 hS4 hA4 hpos
  change EH≤10 at hEH
  change E≤7 at hE
  change A=EH+E+F at hcount
  change T+r≤F+E at hfree
  change r≤3 → EH≤r+1 at hrsmall
  change F<j+1 at hbad
  have hET : E≤T := Recaman.ClockCountSaturation.count_le_length (EndN f 0) (n+B) T
  have hAeq : A=M+L+U+T := by
    have he:=ones_seg_eq_count f n (B+T)
    have hw' := Recaman.FourRunSupplySeventeen.four_run_word f n h M m L s U v T
      hS hA hS2 hA2 hS3 hA3 hS4 hA4
    change seg f n (B+T)=_ at hw'
    rw [hw'] at he
    simp only [ones_append,ones_replicate_A,ones_replicate_S] at he
    dsimp [A]
    omega
  have hF4 : 4≤F := by
    by_cases he : F≤3
    · have hb:=positive_r3_additions_free_bound f n 0 (B+T) hw
        (by simpa only [List.replicate_zero,List.append_nil] using hpre)
        (fun k hk hkB=>hpos k hk (by dsimp [B,H] at hkB; omega)) he
      change A≤2*F+1 at hb
      omega
    · omega


  have h16 : M+2+s+v≤16 := by omega
  have hz13 : s+v≤13 := by omega
  obtain ⟨he6,he5⟩:=Recaman.TwoSActualLastBudget.actual_second_S_two_budgets
    f n h M m L s U v T j w hw hpre hL hU hm hs hv (by omega) hz13
      hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget
  have hE6 : E≤6 := by simpa only [E,B,H,Nat.add_assoc] using he6
  have h15 : M+2+s+v≤15 := by omega
  have hM8 : M≤8 := by omega
  have hE5 : E≤5 := by
    have he:=he5 hM8
    simpa only [E,B,H,Nat.add_assoc] using he
  have h14 : M+2+s+v≤14 := by omega
  have hM7 : M≤7 := by omega
  have hz11 : s+v≤11 := by omega
  have hLi : (L : Int)≤7 := by
    apply Recaman.TwoSTargetBounds.two_target_L_cut (L : Int) (U : Int) (v : Int)
      ((s : Int)+(v : Int)) ((j : Int)+1)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    grind only
  exact ⟨hM7,by omega,hz11,by omega,by omega,h14⟩

end Recaman.TwoSecondSCounterCut
