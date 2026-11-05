import Recaman.ShortCounterFactorBounds

namespace Recaman.GapFiveScalar

open Recaman.ShortCounterFactorBounds

/-- The exact clock-zero branch violates the square. A gap5 residual
with no last supply would need ten head suppliers and cross at most seven. -/
theorem gap_five_head_candidate (M m L s U v T C A r EH E F : Nat)
    (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hv : 1≤v) (hC : 2≤C)
    (hA : 13≤A) (hAeq : A=M+L+U+T) (hcount : A=EH+E+F)
    (hhead : EH≤10) (hF : F≤5) (hfree : T+r≤F+E)
    (hcase : (E=0 ∧ T≤1) ∨
      (T=3 ∧ r=4 ∧ M+L=9 ∧ E=2 ∧ v+1≤s ∧ U=2*v+2))
    (h : (C : Int)^2+36+2*(((M+L+U : Nat) : Int)*(v : Int)+((M*(m+s)+L*s : Nat) : Int))≤
      ((A : Int)-6)^2+1) :
    EH=10 ∧ M*(m+s)+L*s≤7 := by
  let N:=M+L+U
  let I:=M*(m+s)+L*s
  let Q:=(N : Int)*(v : Int)+(I : Int)
  let X:=(A : Int)-6
  change A=N+T at hAeq
  change (C : Int)^2+36+2*Q≤X^2+1 at h
  have hX0 : 0≤X := by dsimp [X]; omega
  have hCN:=square_lower (C : Int) 2 (by decide) (by omega)
  have hNv:=Int.mul_nonneg (show 0≤(N : Int) by omega) (show 0≤(v : Int)-1 by omega)
  have hQ : (N : Int)+(I : Int)≤Q := by dsimp [Q]; grind only
  rcases hcase with ⟨he,hT⟩|⟨hT,hr,hW,he,hsv,hU⟩
  · have hi : 3≤I := by
      have ha : 2≤M*(m+s) := Nat.mul_le_mul hM (show 2≤m+s by omega)
      have hb : 1≤L*s := Nat.mul_le_mul hL hs
      dsimp [I]
      omega
    have hA15 : A=15 := by
      by_cases ha : A≤14
      · have hsq := square_lower 8 X hX0 (by dsimp [X]; omega)
        grind only
      · omega
    have hX9 : X=9 := by dsimp [X]; omega
    rw [hX9] at h
    have hQ21 : Q≤21 := by grind only
    exact ⟨by omega,by change I≤7; omega⟩
  · have hU5 : U≤5 := by dsimp [N] at hAeq; omega
    have hv1 : v=1 := by omega
    have hN13 : N=13 := by dsimp [N]; omega
    have hI19 : 19≤I := by
      have hs2 : 2≤s := by omega
      have hp : 18≤(M+L)*s := Nat.mul_le_mul (show 9≤M+L by omega) hs2
      have hm1 : 1≤M*m := Nat.mul_le_mul hM hm
      dsimp [I]
      rw [Nat.mul_add,Nat.add_assoc,←Nat.add_mul]
      omega
    have hX10 : X=10 := by dsimp [X]; omega
    rw [hX10] at h
    grind only

end Recaman.GapFiveScalar
