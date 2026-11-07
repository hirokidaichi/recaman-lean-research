import Recaman.ThirdSMiddleSources
import Recaman.ThirdSActualCounterCut

namespace Recaman.ThirdSResidualFreeGap

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- The remaining third-S targets satisfy the original full-tail free gap.
All small bands and source exclusions are internally supplied from that target. -/
theorem third_S_residual_free_gap (f : Nat → Bool) (n t h M m L s U v T j : Nat)
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
    (hta : n+h+M+m+L≤t) (htb : t<n+h+M+m+L+s)
    (hq4 : 4≤n+h+M+m+L+s-t)
    (htarget : Win f t (n+h+M+m+L+s+U+v+T+j-t))
    : j+1≤cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T) := by
  by_cases hgood : j+1≤cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)
  · exact hgood
  · exfalso
    have hbad : cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)<j+1 := by omega
    let q:=n+h+M+m+L+s-t
    let H:=h+M+m+L+s+U
    let B:=H+v
    let A:=cN (fun x=>f x=true) n (B+T)
    let P:=fun x=>f x=true ∧ ¬EndN f 0 x
    let F:=cN P n (B+T)
    let r:=cN P n H
    let EH:=cN (EndN f 0) n H
    let E:=cN (EndN f 0) (n+B) T
    obtain ⟨hbal,hsq⟩:=Recaman.ThirdSTargetProfile.actual_third_S_target_profile
      f (n+h+M+m+L) s U v T j t hta htb hS3 hA3 hS4 hA4 hgap htarget
    change T+U=j+1+q+v at hbal
    change ((q : Int)+(v : Int))^2=((j : Int)+1)^2+2*(U : Int)*(v : Int) at hsq
    have hRp : j+1<q+v := by
      by_cases he : j+1<q+v
      · exact he
      · have hl:=Recaman.ShortCounterFactorBounds.square_lower ((j : Int)+1)
          ((q : Int)+(v : Int)) (by omega) (by omega)
        have hp:=Int.mul_pos (show 0<(U : Int) by omega) (show 0<(v : Int) by omega)
        grind only
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
    have hcuts:=Recaman.ThirdSActualCounterCut.third_S_actual_counter_cut
      f n t h M m L s U v T j w hw hpre hM hL hU hT hm hs hv
      hS hA hS2 hA2 hS3 hA3 hS4 hA4 hpos hgap hta htb hq4 htarget hbad
    dsimp only at hcuts
    change M+L+q+v≤15 ∧ q+v≤13 ∧ j+1≤12 ∧ T+U≤25 ∧ M+L+U+T≤27 at hcuts
    obtain ⟨hW15,hp13,_,_,_⟩:=hcuts
    have hF4 : 4≤F := by
      by_cases he : F≤3
      · have hb:=positive_r3_additions_free_bound f n 0 (B+T) hw
          (by simpa only [List.replicate_zero,List.append_nil] using hpre)
          (fun k hk hkB=>hpos k hk (by dsimp [B,H] at hkB; omega)) he
        change A≤2*F+1 at hb
        omega
      · omega
    have hp6 : 6≤q+v := by omega
    have hM8 : M≤8 := by omega
    have hL8 : L≤8 := by omega
    have hA4' : ∀ i, i<T → f (n+B+i)=true := by
      simpa only [B,H,Nat.add_assoc] using hA4
    have hword' : seg f n B=List.replicate h false++List.replicate M true++
        List.replicate m false++List.replicate L true++List.replicate s false++
        List.replicate U true++List.replicate v false := by
      simpa only [List.append_assoc] using hword
    obtain ⟨hE5,hE4⟩:=Recaman.MixedShortAPairBudget.actual_fourth_bounds f n B T h M m L s U v
      w hw hpre hword' hm hs hv hM8 hL8 hA4'
    change E≤5 at hE5
    change L≤3 → E≤4 at hE4
    have hr4 : 4≤r := by
      by_cases he : r≤3
      · have hh:=hrsmall he
        by_cases hL3 : L≤3
        · have he4:=hE4 hL3
          omega
        · omega
      · omega
    have hUp : q+v≤U := by omega
    have hp11 : q+v≤11 := by
      by_cases hL3 : L≤3
      · have he4:=hE4 hL3
        omega
      · omega
    have hsmall:=Recaman.ThirdSTargetSmallBand.small_target_band
      ((q : Int)+(v : Int)) ((j : Int)+1) (U : Int) (v : Int) (T : Int)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) hsq
    have hshape : q+v=11 ∧ U=12 ∧ (v=3 ∨ v=4) := by
      rcases hsmall with h1|h2
      · obtain ⟨hp,_,hU,he,_⟩:=h1
        exact ⟨by omega,by omega,Or.inr (by omega)⟩
      · obtain ⟨hp,_,hU,he,_⟩:=h2
        exact ⟨by omega,by omega,Or.inl (by omega)⟩
    obtain ⟨hpEq,hU12,hvcase⟩:=hshape
    have hL3 : L≤3 := by omega
    have he4:=hE4 hL3
    have hM1 : M=1 := by omega
    have hL1 : L=1 := by omega
    have hword'' : seg f n B=List.replicate h false++List.replicate 1 true++List.replicate m false++
        List.replicate 1 true++List.replicate s false++List.replicate 12 true++List.replicate v false := by
      simpa only [hM1,hL1,hU12] using hword'
    have hlast:=Recaman.ThirdSMiddleSources.actual_last_three f n B T h m s v w hw hpre hword''
      hm (by dsimp [q] at hpEq; omega) hvcase hA4'
    change E≤3 at hlast
    omega

end Recaman.ThirdSResidualFreeGap
