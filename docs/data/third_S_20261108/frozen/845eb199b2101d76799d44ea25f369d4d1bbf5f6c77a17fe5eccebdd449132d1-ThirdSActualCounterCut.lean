import Recaman.ThirdSSaturatedSources
import Recaman.ThirdSSaturationAlgebra
import Recaman.FourMeasuredCounts
import Recaman.FourRunSupplySeventeen

namespace Recaman.ThirdSActualCounterCut

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- A genuine four-run counter with the same third-S target has a
strict residual budget. All source and saturation inputs are derived
from the original measured counts. -/
theorem third_S_actual_counter_cut (f : Nat → Bool) (n t h M m L s U v T j : Nat)
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
    (hbad : cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)<j+1) :
    let q:=n+h+M+m+L+s-t
    M+L+q+v≤15 ∧ q+v≤13 ∧ j+1≤12 ∧ T+U≤25 ∧ M+L+U+T≤27 := by
  dsimp only
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
  have h16 : M+L+q+v≤16 := by omega
  have h15 : M+L+q+v≤15 := by
    by_cases hc : M+L+q+v≤15
    · exact hc
    exfalso
    have heq : M+L+q+v=16 := by omega
    have hEH10 : EH=10 := by omega
    have hE7 : E=7 := by omega
    have hF : F=j := by omega
    have hr4 : 4≤r := by
      by_cases hh : r≤3
      · have hp:=hrsmall hh
        omega
      · omega
    have hA4' : ∀ i, i<T → f (n+B+i)=true := by
      simpa only [B,H,Nat.add_assoc] using hA4
    have hword' : seg f n B=List.replicate h false++List.replicate M true++
        List.replicate m false++List.replicate L true++List.replicate s false++
        List.replicate U true++List.replicate v false := by
      simpa only [B,H,Nat.add_assoc,List.append_assoc] using hword
    obtain ⟨⟨i,_,ha⟩,⟨k,_,hsup⟩⟩:=
      Recaman.ThirdSSaturatedSources.actual_seven_needs_late_sources
        f n B T h M m L s U v w hw hpre hword' hm hs hv hA4' (by omega)
    exact Recaman.ThirdSSaturationAlgebra.saturation_equations_impossible
      (M+L) L s U v T q j r i k (by omega) hv hU hq4
      (by dsimp [q]; omega) heq hr4 (by omega) (by omega) (by omega) hbal hsq ha hsup
  change M+L+q+v≤15 ∧ q+v≤13 ∧ j+1≤12 ∧ T+U≤25 ∧ M+L+U+T≤27
  exact ⟨h15,by omega,by omega,by omega,by omega⟩

end Recaman.ThirdSActualCounterCut
