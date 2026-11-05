import Recaman.FinalSTargetLengths
import Recaman.ShortCounterFactorBounds

namespace Recaman.AlternatingTargetLengths

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.ASourceReuse Recaman.ShortCounterFactorBounds

/-- A target starting within the earlier A run of A/S/A/S forces
a longer final A run than the pure final-S target. The separator
may be zero in the inputs, in which case no target exists. -/
theorem actual_A_S_A_S_target_lengths (f : Nat → Bool) (a U v T j t : Nat)
    (hta : a≤t) (htb : t<a+U)
    (hA0 : ∀ i, i<U → f (a+i)=true)
    (hS : ∀ x, a+U≤x → x<a+U+v → f x=false)
    (hA : ∀ i, i<T → f (a+U+v+i)=true)
    (hgap : ∀ x, a+U+v+T≤x → x<a+U+v+T+j → f x=false)
    (htarget : Win f t (a+U+v+T+j-t)) :
    j+1<v ∧ 2*(j+1)+1≤T := by
  let e:=a+U-t
  have he : 1≤e := by dsimp [e]; omega
  have heend : t+e=a+U := by dsimp [e]; omega
  have hA0' : seg f t e=List.replicate e true := by
    apply seg_A
    intro x hx hxe
    simpa only [Nat.add_sub_cancel' (show a≤x by omega)] using hA0 (x-a) (by omega)
  have hAa : seg f (a+U+v) T=List.replicate T true := by
    apply seg_A
    intro x hx hxT
    simpa only [Nat.add_sub_cancel' hx] using hA (x-(a+U+v)) (by omega)
  have hword : seg f t (a+U+v+T+j-t)=List.replicate e true++List.replicate v false++
      List.replicate T true++List.replicate j false := by
    rw [show a+U+v+T+j-t=e+v+T+j by omega,seg_add,seg_add,seg_add,heend,
      show t+(e+v)=a+U+v by omega,show t+(e+v+T)=a+U+v+T by omega,hA0',hAa,
      seg_false f (a+U) v hS,seg_false f (a+U+v+T) j hgap]
  have hm : mass (List.replicate e true++List.replicate v false++List.replicate T true++List.replicate j false)=1 := by
    rw [←hword,seg_mass]
    have hh:=htarget.2.1
    rw [show t+(a+U+v+T+j-t)=a+U+v+T+j by omega] at hh ⊢
    omega
  have ha : areaW (List.replicate e true++List.replicate v false++List.replicate T true++List.replicate j false)=0 := by
    rw [←hword,←Ar_areaW]
    exact htarget.2.2
  have hk:=source_key_before_gap (List.replicate e true++List.replicate v false) T j hm ha
  rw [runKey_A_S] at hk
  simp only [mass_append,mass_rep_false,mass_replicate_A] at hm
  let R:=(j : Int)+1
  have hR2 := square_lower R 1 (by decide) (by dsimp [R]; omega)
  have hV0 : 0<(v : Int) := by
    by_cases hzero : v=0
    · rw [hzero] at hk
      dsimp [R] at hR2
      grind only
    · omega
  have hEq : (v : Int)^2-2*(e : Int)*(v : Int)=R^2 := by dsimp [R]; grind only
  have hRv : R<(v : Int) := by
    by_cases hle : (v : Int)≤R
    · have hsq:=square_lower R (v : Int) (by omega) hle
      have hpos:=Int.mul_pos (show 0<(e : Int) by omega) hV0
      grind only
    · omega
  have hT : 2*R<(T : Int) := by
    by_cases hl : (T : Int)≤2*R
    · have hprod:=Int.mul_nonpos_of_nonneg_of_nonpos (show 0≤(v : Int) by omega)
        (show (T : Int)-2*R≤0 by omega)
      have hpos:=Int.mul_pos (show 0<(v : Int)-R by omega) (show 0<(v : Int)-R by omega)
      have hbalance : (e : Int)-(v : Int)+(T : Int)=R := by dsimp [R]; omega
      grind only
    · omega
  dsimp [R] at hRv hT
  exact ⟨by omega,by omega⟩

end Recaman.AlternatingTargetLengths
