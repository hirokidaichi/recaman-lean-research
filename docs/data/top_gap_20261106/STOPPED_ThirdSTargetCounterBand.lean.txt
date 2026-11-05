import Recaman.FourMeasuredCounts
import Recaman.ThirdSTargetProfile
import Recaman.FourRunSupplySeventeen

namespace Recaman.ThirdSTargetCounterBand

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- A third-separator target leaves a bounded pair of residual
S lengths in an actual counter, with both measured counts tight at the boundary. -/
theorem third_S_target_counter_band (f : Nat → Bool) (n t h M m L s U v T j : Nat)
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
    (htarget : Win f t (n+h+M+m+L+s+U+v+T+j-t))
    (hbad : cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)<j+1) :
    let q:=n+h+M+m+L+s-t
    let H:=h+M+m+L+s+U
    let B:=H+v
    let P:=fun x=>f x=true ∧ ¬EndN f 0 x
    j+1<q+v ∧ M+L+q+v≤16 ∧ T+U≤27 ∧ q+v+cN P n H≤U+6 ∧
    (M+L+q+v=16 →
      cN (EndN f 0) n H=10 ∧ cN (EndN f 0) (n+B) T=7 ∧ cN P n (B+T)=j) := by
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
  obtain ⟨hb,hsq⟩:=Recaman.ThirdSTargetProfile.actual_third_S_target_profile
    f (n+h+M+m+L) s U v T j t hta htb hS3 hA3 hS4 hA4 hgap htarget
  change T+U=j+1+q+v at hb
  change ((q : Int)+(v : Int))^2=((j : Int)+1)^2+2*(U : Int)*(v : Int) at hsq
  have hR : j+1<q+v := by
    by_cases hh : j+1<q+v
    · exact hh
    · have hk:=Recaman.ShortCounterFactorBounds.square_lower ((j : Int)+1)
        ((q : Int)+(v : Int)) (by omega) (by omega)
      have hp:=Int.mul_pos (show 0<(U : Int) by omega) (show 0<(v : Int) by omega)
      grind only
  obtain ⟨hEH,hE,hcount,hfree,_,_⟩:=Recaman.FourMeasuredCounts.measured_counts f n h M m L s U v T
    w hw hpre hM hm hs hv hS hA hS2 hA2 hS3 hA3 hS4 hA4 hpos
  change EH≤10 at hEH
  change E≤7 at hE
  change A=EH+E+F at hcount
  change T+r≤F+E at hfree
  change F<j+1 at hbad
  have hAeq : A=M+L+U+T := by
    have he:=ones_seg_eq_count f n (B+T)
    have hw' := Recaman.FourRunSupplySeventeen.four_run_word f n h M m L s U v T
      hS hA hS2 hA2 hS3 hA3 hS4 hA4
    change seg f n (B+T)=_ at hw'
    rw [hw'] at he
    simp only [ones_append,ones_replicate_A,ones_replicate_S] at he
    change _=A at he
    omega
  change j+1<q+v ∧ M+L+q+v≤16 ∧ T+U≤27 ∧ q+v+r≤U+6 ∧
    (M+L+q+v=16 → EH=10 ∧ E=7 ∧ F=j)
  exact ⟨hR,by omega,by omega,by omega,fun hs=>⟨by omega,by omega,by omega⟩⟩

end Recaman.ThirdSTargetCounterBand
