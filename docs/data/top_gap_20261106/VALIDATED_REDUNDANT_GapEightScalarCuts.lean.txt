import Recaman.ShortCounterFactorBounds

namespace Recaman.GapEightScalarCuts

open Recaman.ShortCounterFactorBounds

private theorem gap_eight_square_impossible (X Q C X0 Q0 : Int)
    (hC : 2≤C) (hX0 : 0≤X) (hX : X≤X0) (hQ : Q0≤Q)
    (hnum : X0^2+1<85+2*Q0) (h : C^2+81+2*Q≤X^2+1) : False := by
  have hx := square_lower X0 X hX0 hX
  have hc := square_lower C 2 (by decide) hC
  grind only

/-- The delay-sensitive cut leaves only a short third-head parity
question. This arithmetic helper needs actual counts from its caller. -/
theorem gap_eight_head_candidate (M m L s U v T C A r EH E F : Int)
    (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hU : 1≤U) (hv : 1≤v)
    (hC : 2≤C) (hA : 19≤A) (hAeq : A=M+L+U+T) (hcount : A=EH+E+F)
    (hhead : EH≤10) (hE : E≤7) (hET : E≤T) (hF : F≤8) (hfree : T+r≤F+E)
    (hrsmall : r≤3 → EH≤r+1) (hMcost : M≤r+2) (hMLcost : M+L≤r+5)
    (hc0 : T≤8 → E≤5)
    (hc1 : M≤8 → 8≤T → E≤T-8+3) (hc2 : M≤8 → T≤8 → E≤3)
    (hd1 : M≤10 → T≤6 → E≤3) (hd2 : M+L≤9 → T≤8 → E≤1)
    (hcircle : C^2+81+2*((M+L+U)*v+M*(m+s)+L*s)≤(A-9)^2+1) :
    EH=10 ∧ s=1 ∧ M*m≤5 := by
  let N:=M+L+U
  let W:=M+L
  let Q:=N*v+M*(m+s)+L*s
  let X:=A-9
  change A=N+T at hAeq
  change W≤r+5 at hMLcost
  change C^2+81+2*Q≤X^2+1 at hcircle
  have hN : 0≤N := by dsimp [N]; omega
  have hW : 0≤W := by dsimp [W]; omega
  have hNv:=Int.mul_nonneg hN (show 0≤v-1 by omega)
  have hMm:=Int.mul_nonneg (show 0≤M by omega) (show 0≤m+s-2 by omega)
  have hLs:=Int.mul_nonneg (show 0≤L by omega) (show 0≤s-1 by omega)
  have hQ : N+2*M+L≤Q := by dsimp [Q]; grind only
  have hX : 0≤X := by dsimp [X]; omega
  have hr : 4≤r := by
    by_cases hr : r≤3
    · have hEH := hrsmall hr
      exfalso
      exact gap_eight_square_impossible X Q C 10 10 hC hX (by dsimp [X]; omega)
        (by omega) (by decide) hcircle
    · omega
  have hMs : M≤8 := by
    by_cases hl : M≤8
    · exact hl
    · have hE5 := hc0 (by omega)
      have hE3 := hd1 (by omega) (by omega)
      exfalso
      exact gap_eight_square_impossible X Q C 12 34 hC hX (by dsimp [X]; omega)
        (by omega) (by decide) hcircle
  have hT : T<8 := by
    by_cases ht : 8≤T
    · have he:=hc1 hMs ht
      omega
    · omega
  have hE3 := hc2 hMs (by omega)
  have hW10 : 10≤W := by
    by_cases hw : W≤9
    · have hE1 := hd2 (by dsimp [W] at hw; exact hw) (by omega)
      exfalso
      exact gap_eight_square_impossible X Q C 10 17 hC hX (by dsimp [X]; omega)
        (by omega) (by decide) hcircle
    · omega
  have hT6 : T≤6 := by omega
  have hA21 : A=21 := by
    by_cases h20 : A≤20
    · exfalso
      exact gap_eight_square_impossible X Q C 11 24 hC hX (by dsimp [X]; omega)
        (by dsimp [W] at hW10; omega) (by decide) hcircle
    · omega
  have hQ30 : Q≤30 := by
    have hx12 : X=12 := by dsimp [X]; omega
    rw [hx12] at hcircle
    have hc:=square_lower C 2 (by decide) hC
    grind only
  have hCross : N+M*m+W*s≤Q := by dsimp [Q,W]; grind only
  have hs1 : s=1 := by
    by_cases hss : 2≤s
    · have hw:=Int.mul_nonneg hW (show 0≤s-2 by omega)
      have hm0:=Int.mul_nonneg (show 0≤M by omega) (show 0≤m by omega)
      have hw2 : 2*W≤W*s := by grind only
      omega
    · omega
  rw [hs1,Int.mul_one] at hCross
  exact ⟨by omega,hs1,by omega⟩

end Recaman.GapEightScalarCuts
