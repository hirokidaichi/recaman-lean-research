import Recaman.ShortCounterFactorBounds

namespace Recaman.HighGapScalarCuts

open Recaman.ShortCounterFactorBounds

private theorem target_square_impossible (R X Q C R0 X0 Q0 : Int)
    (hR0 : 0≤R0) (hR : R0≤R) (hX0 : 0≤X) (hX : X≤X0) (hQ : Q0≤Q)
    (hnum : X0^2+1<R0^2+2*Q0) (h : C^2+R^2+2*Q≤X^2+1) : False := by
  have hr := square_lower R R0 hR0 hR
  have hx := square_lower X0 X hX0 hX
  have hc := Int.sq_nonneg C
  omega

/-- Scalar part of the actual count proof. The surviving unit separators
are necessary conditions; their first-A source is checked separately. -/
theorem high_gap_unit_candidate (j M m L s U v T C A r eH E F : Int)
    (hj : 9≤j) (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hU : 1≤U)
    (hv : 1≤v) (hC : 2≤C) (hA : 2*j+3≤A) (hcount : A=eH+E+F)
    (hhead : eH≤10) (hF : F≤j) (hr : 4≤r) (hE : E≤7) (hfree : T+r≤j+E)
    (hfirst : M≤r+2) (hAeq : A=M+L+U+T)
    (hcut0 : T≤j → E≤5) (hcut1 : M≤j → j≤T → E≤T-j+3)
    (hcut2 : M≤j → T≤j → E≤3) (hcut3 : M+L≤j → T≤j → E≤1)
    (hcircle : C^2+(j+1)^2+2*((M+L+U)*v+M*(m+s)+L*s)≤(A-(j+1))^2+1) :
    j=9 ∧ A=24 ∧ T≤6 ∧ m=1 ∧ s=1 ∧ v=1 ∧ 5≤E := by
  let N:=M+L+U
  let Q:=N*v+M*(m+s)+L*s
  let R:=j+1
  let X:=A-R
  change A=N+T at hAeq
  change C^2+R^2+2*Q≤X^2+1 at hcircle
  have hN : 0≤N := by dsimp [N]; omega
  have hNv := Int.mul_nonneg hN (show 0≤v-1 by omega)
  have hMm := Int.mul_nonneg (show 0≤M by omega) (show 0≤m+s-2 by omega)
  have hLs := Int.mul_nonneg (show 0≤L by omega) (show 0≤s-1 by omega)
  have hQlo : N+2*M+L≤Q := by dsimp [Q]; grind only
  have hX0 : 0≤X := by dsimp [X,R]; omega
  have hLong : j<M := by
    by_cases hshort : M≤j
    · exfalso
      have hTj : T<j := by
        by_cases hT : j≤T
        · have he:=hcut1 hshort hT
          omega
        · omega
      have hE3 := hcut2 hshort (by omega)
      have hML : j<M+L := by
        by_cases hml : M+L≤j
        · have he:=hcut3 hml (by omega)
          omega
        · omega
      have hQ24 : 24≤Q := by omega
      have hX12 : X≤12 := by dsimp [X,R]; omega
      exact target_square_impossible R X Q C 10 12 24 (by decide)
        (by dsimp [R]; omega) hX0 hX12 hQ24 (by decide) hcircle
    · omega
  have hT8 : T≤8 := by omega
  have hE5 := hcut0 (by omega)
  have hT6 : T≤6 := by omega
  have hX14 : X≤14 := by dsimp [X,R]; omega
  have hj9 : j=9 := by
    by_cases hj10 : 10≤j
    · exact False.elim (target_square_impossible R X Q C 11 14 40 (by decide)
        (by dsimp [R]; omega) hX0 hX14 (by omega) (by decide) hcircle)
    · omega
  have hA24 : A=24 := by
    by_cases hA23 : A≤23
    · exact False.elim (target_square_impossible R X Q C 10 13 36 (by decide)
        (by dsimp [R]; omega) hX0 (by dsimp [X,R]; omega) (by omega) (by decide) hcircle)
    · omega
  have hQ46 : Q≤46 := by
    have hR10 : R=10 := by dsimp [R]; omega
    have hXeq : X=14 := by dsimp [X,R]; omega
    rw [hR10,hXeq] at hcircle
    have hc := square_lower C 2 (by decide) hC
    grind only
  have hmS : m+s=2 := by
    by_cases he : 3≤m+s
    · have hp := Int.mul_nonneg (show 0≤M by omega) (show 0≤m+s-3 by omega)
      have hQhi : N+3*M+L≤Q := by dsimp [Q]; grind only
      omega
    · omega
  have hv1 : v=1 := by
    by_cases hv2 : 2≤v
    · have hp := Int.mul_nonneg hN (show 0≤v-2 by omega)
      have hQhi : 2*N+2*M+L≤Q := by dsimp [Q]; grind only
      omega
    · omega
  exact ⟨hj9,hA24,hT6,by omega,by omega,hv1,by omega⟩

end Recaman.HighGapScalarCuts
