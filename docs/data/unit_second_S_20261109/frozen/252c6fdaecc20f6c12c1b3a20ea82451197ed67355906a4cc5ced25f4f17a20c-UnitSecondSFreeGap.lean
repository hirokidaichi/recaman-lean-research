import Recaman.UnitSecondSCounterCut
import Recaman.UnitSFactorCertificate

namespace Recaman.UnitSecondSFreeGap

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

theorem unit_second_S_free_gap (f : Nat → Bool) (n h M m L s U v T j : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w)
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
    (htarget : Win f (n+h+M+m-1) (1+L+s+U+v+T+j))
    : j+1≤cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)
 := by
  by_cases hgood : j+1≤cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)
  · exact hgood
  have hbad : cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)<j+1 := by omega
  apply False.elim
  obtain ⟨hM8,hL7,hz13,hR5,hR12,h15⟩:=Recaman.UnitSecondSCounterCut.unit_second_S_counter_cut
    f n h M m L s U v T j w hw hpre hM hL hU hT hm hs hv
      hS hA hS2 hA2 hS3 hA3 hS4 hA4 hpos hgap htarget hbad
  let H:=h+M+m+L+s+U
  let B:=H+v
  let A:=cN (fun x=>f x=true) n (B+T)
  let P:=fun x=>f x=true ∧ ¬EndN f 0 x
  let F:=cN P n (B+T)
  let r:=cN P n H
  let EH:=cN (EndN f 0) n H
  let E:=cN (EndN f 0) (n+B) T
  obtain ⟨hbal,hstrict,hsq⟩:=Recaman.SecondSTargetProfile.actual_second_S_target_profile
    f (n+h+M) m L s U v T j (n+h+M+m-1) (by omega) (by omega) hL hs
      hS2 hA2 hS3 hA3 hS4 hA4 hgap
        (by rw [show n+h+M+m+L+s+U+v+T+j-(n+h+M+m-1)=1+L+s+U+v+T+j by omega]; exact htarget)
  rw [show n+h+M+m-(n+h+M+m-1)=1 by omega] at hbal hstrict hsq
  obtain ⟨hEH,hE,hcount,hfree,hrsmall,hword⟩:=
    Recaman.FourMeasuredCounts.measured_counts f n h M m L s U v T w hw hpre
      hM hm hs hv hS hA hS2 hA2 hS3 hA3 hS4 hA4 hpos
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

  let D:=1+s+v-L
  have hDL : D+L=1+s+v := by dsimp [D]; omega
  obtain ⟨hDsq,hRD⟩:=Recaman.UnitSLongAExclusion.unit_target_residual
    (L : Int) (U : Int) (v : Int) ((s : Int)+(v : Int)) ((j : Int)+1) (D : Int)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by grind only)
  have hbalance : T+U=j+1+D := by omega
  have hhead:=Recaman.ShortEarlyHeadBudget.actual_short_head_budget
    f n h M m L s U w hw hpre hM hL hM8 (by omega) hm hs hS hA hS2 hA2 hS3 hA3
      (fun k hk hkH=>hpos k hk (by omega))
  change EH≤M+L+3 at hhead
  have hA4' : ∀ i, i<T → f (n+B+i)=true := by simpa only [B,H,Nat.add_assoc] using hA4
  have hword' : seg f n B=List.replicate h false++List.replicate M true++
      List.replicate m false++List.replicate L true++List.replicate s false++
      List.replicate U true++List.replicate v false := by simpa only [List.append_assoc] using hword
  obtain ⟨hE5,hE4⟩:=Recaman.MixedShortAPairBudget.actual_fourth_bounds
    f n B T h M m L s U v w hw hpre hword' hm hs hv hM8 (by omega) hA4'
  change E≤5 at hE5
  change L≤3 → E≤4 at hE4
  have hD6 : 6≤D := by omega
  have hD7 : D≤7 := by omega
  have hr4 : 4≤r := by
    by_cases he : r≤3
    · have hh:=hrsmall he
      by_cases hL3 : L≤3
      · have he4:=hE4 hL3
        omega
      · omega
    · omega
  have hDU : D≤U := by omega
  have hUR : U≤j+1+2 := by omega
  obtain ⟨hL1,hUD,_,_⟩:=Recaman.UnitSFactorCertificate.unit_S_square_choices
    (D : Int) ((j : Int)+1) (L : Int) (U : Int) (v : Int)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) hDsq
  have hE4':=hE4 (by omega)
  omega

end Recaman.UnitSecondSFreeGap
