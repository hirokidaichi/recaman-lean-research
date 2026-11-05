import Recaman.ShortCounterFactorBounds

namespace Recaman.GapFourScalar

open Recaman.ShortCounterFactorBounds

private theorem late_square_budget (U T I Q C : Int)
    (hU : 1≤U) (hT : 4≤T) (hT7 : T≤7)
    (hC : 2≤C) (hQ : (9+U)*(2*T-4)+I≤Q)
    (hsq : C^2+25+2*Q≤(4+U+T)^2+1) :
    36+2*I≤8*U+U^2 := by
  have hC4:=square_lower C 2 (by decide) hC
  have hp:=Int.mul_nonneg (show 0≤T-4 by omega) (show 0≤24+2*U-T by omega)
  grind only

/-- The remaining gap4 highest-clock bounds force head10 at W9 and
allow at most fourteen AS pairs, below that head's actual cost. -/
theorem gap_four_head_candidate (M m L s U v T C A EH : Nat)
    (hM : 1≤M) (hm : 1≤m) (hs : 1≤s) (hU : 1≤U) (hv : 1≤v) (hC : 2≤C)
    (hT7 : T≤7) (hW : M+L=9) (hEH : EH≤10) (hhead : EH=5+U)
    (hAeq : A=M+L+U+T)
    (hcase : (T=1 ∧ U=4 ∧ v=1 ∧ 2≤s) ∨ (4≤T ∧ 2*T-4≤v))
    (h : (C : Int)^2+25+2*(((M+L+U : Nat) : Int)*(v : Int)+((M*(m+s)+L*s : Nat) : Int))≤
      ((A : Int)-5)^2+1) :
    EH=10 ∧ M*(m+s)+L*s≤14 := by
  let I:=M*(m+s)+L*s
  let Q:=((M+L+U : Nat) : Int)*(v : Int)+(I : Int)
  change (C : Int)^2+25+2*Q≤((A : Int)-5)^2+1 at h
  have hIform : I=M*m+(M+L)*s := by dsimp [I]; rw [Nat.mul_add,Nat.add_mul,Nat.add_assoc]
  have hI10 : 10≤I := by
    have h1 : 1≤M*m := Nat.mul_le_mul hM hm
    have h9 : 9≤(M+L)*s := Nat.mul_le_mul (by omega) hs
    omega
  rcases hcase with ⟨hT,hU4,hv1,hs2⟩|⟨hT,hvlarge⟩
  · have hA14 : A=14 := by omega
    have hI19 : 19≤I := by
      have h1 : 1≤M*m := Nat.mul_le_mul hM hm
      have h18 : 18≤(M+L)*s := Nat.mul_le_mul (by omega) hs2
      omega
    have hQ32 : 32≤Q := by dsimp [Q]; rw [hW,hU4,hv1]; omega
    have hC4 := square_lower (C : Int) 2 (by decide) (by omega)
    rw [hA14] at h
    grind only
  · have hv' : 2*(T : Int)-4≤(v : Int) := by omega
    have hQlo : (9+(U : Int))*(2*(T : Int)-4)+(I : Int)≤Q := by
      dsimp [Q]
      rw [hW,Int.natCast_add]
      have hp:=Int.mul_nonneg (show 0≤9+(U : Int) by omega) (show 0≤(v : Int)-(2*(T : Int)-4) by omega)
      grind only
    have hx : (A : Int)-5=4+(U : Int)+(T : Int) := by omega
    rw [hx] at h
    have hb:=late_square_budget (U : Int) (T : Int) (I : Int) Q (C : Int)
      (by omega) (by omega) (by omega) (by omega) hQlo h
    have hU5 : U=5 := by
      by_cases hl : U≤4
      · have hq:=square_lower 4 (U : Int) (by omega) (by omega)
        grind only
      · omega
    rw [hU5] at hb
    refine ⟨by omega,?_⟩
    change I≤14
    grind only

end Recaman.GapFourScalar
