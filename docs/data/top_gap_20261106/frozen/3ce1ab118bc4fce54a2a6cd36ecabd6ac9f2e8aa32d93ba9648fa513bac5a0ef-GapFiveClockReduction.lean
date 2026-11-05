import Recaman.ClockCountSaturation
import Recaman.ThirdSeparatorClock

namespace Recaman.GapFiveClockReduction

open Recaman.SingleWindowEquality Recaman.RunSupplyBudget
open Recaman.FourthSourceFamilies Recaman.ThirdSeparatorClock Recaman.ClockCountSaturation

/-- Gap5 either has no final-ray supply or forces a counted
third-separator source at zero and exact three-clock final length. -/
theorem gap_five_clock_reduction (f : Nat → Bool) (b T W s U v r : Nat)
    (hv : 1≤v) (hr : 4≤r) (hW : W≤r+5)
    (hfree : T+r≤5+cN (EndN f 0) b T)
    (hcount : cN (EndN f 0) b T≤max (T-5) (W+T-11)+1)
    (hpair : ∀ i, i<T → max (T-5) (W+T-11)≤i → EndN f 0 (b+i) → i=2)
    (hthird : ∀ i, i<T → max (T-5) (W-1+T-11)≤i → EndN f 0 (b+i) →
      sourceAt false s (List.replicate U true++List.replicate v false) i ∨ i=2) :
    (cN (EndN f 0) b T=0 ∧ T≤1) ∨
      (T=3 ∧ r=4 ∧ W=9 ∧ cN (EndN f 0) b T=2 ∧ v+1≤s ∧ U=2*v+2) := by
  let E:=cN (EndN f 0) b T
  let D:=max (T-5) (W+T-11)
  change T+r≤5+E at hfree
  change E≤D+1 at hcount
  change (E=0 ∧ T≤1) ∨ (T=3 ∧ r=4 ∧ W=9 ∧ E=2 ∧ v+1≤s ∧ U=2*v+2)
  by_cases he : E≤1
  · left
    have hD0 : D=0 := by
      dsimp [D]
      rw [Nat.sub_eq_zero_of_le (show T≤5 by omega),Nat.sub_eq_zero_of_le (show W+T≤11 by omega),Nat.max_self]
    have hE0 : E=0 := by
      apply cN_zero_of
      intro x hx hxt hEnd
      have hh:=hpair (x-b) (by omega) (by change D≤x-b; omega)
        (by rwa [Nat.add_sub_cancel' hx])
      omega
    exact ⟨hE0,by omega⟩
  · right
    have hTr : 7≤T+r := by
      by_cases hz : T+r≤6
      · have hD0 : D=0 := by
          dsimp [D]
          rw [Nat.sub_eq_zero_of_le (show T≤5 by omega),Nat.sub_eq_zero_of_le (show W+T≤11 by omega),Nat.max_self]
        omega
      · omega
    have hd : T-5≤W+T-11 := by
      by_cases hb : T-5≤W+T-11
      · exact hb
      · have hD : D=T-5 := by dsimp [D]; rw [Nat.max_eq_left (by omega)]
        omega
    have hD : D=W+T-11 := by dsimp [D]; rw [Nat.max_eq_right hd]
    have hWeq : W=r+5 := by omega
    have hsat : E=D+1 := by omega
    have hET : E≤T := count_le_length (EndN f 0) b T
    obtain ⟨hD2,hT3,hall⟩:=saturated_pair_clock (EndN f 0) b T D (by omega)
      (fun i hi hp=>by
        by_cases he : i<D
        · exact Or.inl he
        · exact Or.inr (hpair i hi (by change D≤i; omega) hp)) (by omega)
    let i:=D-1
    have hiD : i<D := by dsimp [i]; omega
    have hsource:=hthird i (by omega) (by
      apply Nat.max_le.mpr
      dsimp [i]
      exact ⟨by omega,by omega⟩) (hall i hiD)
    have hi1 : i≤1 := by dsimp [i]; omega
    rcases hsource with hs|h2
    · have hh:=third_separator_clock s U v i hv hs
      have hi0 : i=0 := by have he:=hh.1; omega
      have hD1 : D=1 := by dsimp [i] at hi0; omega
      obtain ⟨hsv,hU⟩:=hh.2.2 hi0
      exact ⟨by omega,by omega,by omega,by omega,hsv,hU⟩
    · omega

end Recaman.GapFiveClockReduction
