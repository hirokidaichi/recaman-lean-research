import Recaman.ThirdSUnitLastBudget
import Recaman.ThirdSActualCounterCut

namespace Recaman.UnitThirdSCounterCut

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

private theorem boundary_twelve_impossible (U v T R : Nat)
    (hU : 12≤U) (hv : 1≤v) (hT : 5≤T) (hR : 5≤R) (hR11 : R≤11)
    (hbal : T+U=R+12)
    (hsq : (144 : Int)=(R : Int)^2+2*(U : Int)*(v : Int)) : False := by
  have hr2:=Recaman.ShortCounterFactorBounds.square_lower (R : Int) 5 (by decide) (by omega)
  have hp:=Int.mul_nonneg (show 0≤(U : Int)-12 by omega) (show 0≤(v : Int) by omega)
  have hv4 : v≤4 := by grind only
  rcases (show v=1 ∨ v=2 ∨ v=3 ∨ v=4 by omega) with rfl|rfl|rfl|rfl <;>
    rcases (show R=5 ∨ R=6 ∨ R=7 ∨ R=8 ∨ R=9 ∨ R=10 ∨ R=11 by omega)
      with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp at hsq <;> omega

/-- A unit second A and the same original third-S target reduce the
actual counter residual to at most eleven, without bounding old history. -/
theorem unit_third_S_counter_cut (f : Nat → Bool) (n t h M m L s U v T j : Nat)
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
    (hunit : L=1)
    (hbad : cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)<j+1) :
    let q:=n+h+M+m+L+s-t
    M+q+v≤13 ∧ q+v≤11 ∧ j+1≤10 ∧ T+U≤21 ∧ M+L+U+T≤24 := by
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
  have hE5 : E≤5 := by
    subst L
    have he:=Recaman.ThirdSUnitLastBudget.actual_third_S_five f n t h M m s U v T j w hw hpre
      hm hs hv hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap hta htb htarget
    simpa only [E,B,H,Nat.add_assoc] using he
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
  have h14 : M+L+q+v≤14 := by omega
  have hp12 : q+v≤12 := by omega
  have hp11 : q+v≤11 := by
    by_cases hh : q+v≤11
    · exact hh
    exfalso
    have hp : q+v=12 := by omega
    have hEH10 : EH=10 := by omega
    have hEeq : E=5 := by omega
    have hF : F=j := by omega
    have hr4 : 4≤r := by
      by_cases hh : r≤3
      · have hb:=hrsmall hh
        omega
      · omega
    have hphead:=addition_endable_partition f n H
    change cN (fun x=>f x=true) n H=EH+r at hphead
    have hwordhead:=Recaman.SeparatorSupplyReset.three_run_word f n h M m L s U
      hS hA hS2 hA2 hS3 hA3
    have hones:=ones_seg_eq_count f n H
    change seg f n H=_ at hwordhead
    rw [hwordhead] at hones
    simp only [ones_append,ones_replicate_A,ones_replicate_S] at hones
    have hU12 : 12≤U := by omega
    have hsq12 : (144 : Int)=((j+1 : Nat) : Int)^2+2*(U : Int)*(v : Int) := by
      have hc : (q : Int)+(v : Int)=12 := by omega
      rw [hc,show (12 : Int)^2=144 from by decide] at hsq
      simpa only [Int.natCast_add,Int.natCast_one] using hsq
    exact boundary_twelve_impossible U v T (j+1) hU12 hv (by omega) (by omega)
      (by omega) (by omega) hsq12
  change M+q+v≤13 ∧ q+v≤11 ∧ j+1≤10 ∧ T+U≤21 ∧ M+L+U+T≤24
  exact ⟨by omega,hp11,by omega,by omega,by omega⟩

end Recaman.UnitThirdSCounterCut
