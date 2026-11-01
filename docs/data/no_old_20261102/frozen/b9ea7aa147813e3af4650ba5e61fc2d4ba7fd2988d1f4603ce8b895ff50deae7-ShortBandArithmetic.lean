import Std

namespace Recaman.ShortBandArithmetic

/-- Numeric consequence only; all count/key premises must be supplied
from actual windows before this helper is used as a research result. -/
theorem five_bands (C v R S T : Nat) (hC : 4≤C) (hv : 1≤v) (hvC : v<C)
    (hR : 5≤R) (hS : 1≤S) (hT : T+C=v+R)
    (hsmall : C=v+1 → S≤14) (hdeep : v+2≤C → S≤C-v+12)
    (hkey : (R : Int)^2≤(S : Int)^2-2*(C : Int)*(S : Int)+(v : Int)^2-2*(C : Int)*(v : Int)+1) :
    ((v=3 ∧ C=4 ∧ R≤8) ∨ (v=4 ∧ C=5 ∧ R=5) ∨
     (v=1 ∧ C≤8 ∧ R≤9) ∨ (v=2 ∧ C≤7 ∧ R≤8) ∨ (v=3 ∧ C=5 ∧ R≤6)) ∧
    C≤8 ∧ v≤4 ∧ R≤9 ∧ S≤19 ∧ S+T≤21 := by
  let D:=C-v
  have hD : 1≤D := by dsimp [D]; omega
  have hCD : (C : Int)=(v : Int)+(D : Int) := by dsimp [D]; omega
  have hRR:=Int.mul_nonneg (show 0≤(R : Int)-5 by omega) (show 0≤(R : Int)+5 by omega)
  have hlarge : 2*C<S := by
    by_cases hh : 2*C<S
    · exact hh
    · have hp:=Int.mul_nonneg (show 0≤(S : Int) by omega) (show 0≤2*(C : Int)-(S : Int) by omega)
      have hq:=Int.mul_nonneg (show 0≤(v : Int) by omega) (show 0≤2*(C : Int)-(v : Int) by omega)
      grind only
  by_cases heq : C=v+1
  · have hS14:=hsmall heq
    have hp:=Int.mul_nonneg (show 0≤14-(S : Int) by omega)
      (show 0≤14+(S : Int)-2*(C : Int) by omega)
    have hb : (R : Int)^2≤198-28*(C : Int)-(C : Int)^2 := by grind only
    have hC5 : C≤5 := by
      by_cases hh : C≤5
      · exact hh
      · have hp:=Int.mul_nonneg (show 0≤(C : Int)-6 by omega) (show 0≤(C : Int)+34 by omega)
        grind only
    have hc : C=4 ∨ C=5 := by omega
    rcases hc with rfl|rfl
    · have hR8 : R≤8 := by
        by_cases hh : R≤8
        · exact hh
        · have hp:=Int.mul_nonneg (show 0≤(R : Int)-9 by omega) (show 0≤(R : Int)+9 by omega)
          grind only
      exact ⟨Or.inl ⟨by omega,rfl,hR8⟩,by omega⟩
    · have hR5 : R=5 := by
        by_cases hh : R=5
        · exact hh
        · have hp:=Int.mul_nonneg (show 0≤(R : Int)-6 by omega) (show 0≤(R : Int)+6 by omega)
          grind only
      exact ⟨Or.inr (Or.inl ⟨by omega,rfl,hR5⟩),by omega⟩
  · have hd : 2≤D := by dsimp [D]; omega
    have hSmax : S≤D+12 := hdeep (by omega)
    have hp:=Int.mul_nonneg (show 0≤(D : Int)+12-(S : Int) by omega)
      (show 0≤(D : Int)+12+(S : Int)-2*(C : Int) by omega)
    have hQ : (R : Int)^2+(D : Int)^2+4*(D : Int)*(v : Int)+(v : Int)^2+24*(v : Int)≤145 := by grind only
    have hv3 : v≤3 := by
      by_cases hh : v≤3
      · exact hh
      · have hdq:=Int.mul_nonneg (show 0≤(D : Int)-2 by omega) (show 0≤(D : Int)+2 by omega)
        have hvq:=Int.mul_nonneg (show 0≤(v : Int)-4 by omega) (show 0≤(v : Int)+4 by omega)
        have hdv:=Int.mul_nonneg (show 0≤(D : Int)-2 by omega) (show 0≤(v : Int) by omega)
        grind only
    have hvs : v=1 ∨ v=2 ∨ v=3 := by omega
    rcases hvs with rfl|rfl|rfl
    · have hD7 : D≤7 := by
        by_cases hh : D≤7
        · exact hh
        · have hp:=Int.mul_nonneg (show 0≤(D : Int)-8 by omega) (show 0≤(D : Int)+12 by omega)
          grind only
      have hd3 : 3≤D := by omega
      have hR9 : R≤9 := by
        by_cases hh : R≤9
        · exact hh
        · have hrq:=Int.mul_nonneg (show 0≤(R : Int)-10 by omega) (show 0≤(R : Int)+10 by omega)
          have hdq:=Int.mul_nonneg (show 0≤(D : Int)-3 by omega) (show 0≤(D : Int)+7 by omega)
          grind only
      exact ⟨Or.inr (Or.inr (Or.inl ⟨rfl,by omega,hR9⟩)),by dsimp [D] at *; omega⟩
    · have hD5 : D≤5 := by
        by_cases hh : D≤5
        · exact hh
        · have hp:=Int.mul_nonneg (show 0≤(D : Int)-6 by omega) (show 0≤(D : Int)+14 by omega)
          grind only
      have hR8 : R≤8 := by
        by_cases hh : R≤8
        · exact hh
        · have hrq:=Int.mul_nonneg (show 0≤(R : Int)-9 by omega) (show 0≤(R : Int)+9 by omega)
          have hdq:=Int.mul_nonneg (show 0≤(D : Int)-2 by omega) (show 0≤(D : Int)+10 by omega)
          grind only
      exact ⟨Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl,by omega,hR8⟩))),by dsimp [D] at *; omega⟩
    · have hD2 : D=2 := by
        by_cases hh : D=2
        · exact hh
        · have hp:=Int.mul_nonneg (show 0≤(D : Int)-3 by omega) (show 0≤(D : Int)+15 by omega)
          grind only
      have hR6 : R≤6 := by
        by_cases hh : R≤6
        · exact hh
        · have hp:=Int.mul_nonneg (show 0≤(R : Int)-7 by omega) (show 0≤(R : Int)+7 by omega)
          grind only
      exact ⟨Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl,by omega,hR6⟩))),by dsimp [D] at *; omega⟩

end Recaman.ShortBandArithmetic
