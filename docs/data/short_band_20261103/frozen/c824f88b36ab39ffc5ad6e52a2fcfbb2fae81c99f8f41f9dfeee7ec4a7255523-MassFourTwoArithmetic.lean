import Recaman.ShortCounterFactorBounds
namespace Recaman.MassFourTwoArithmetic
open Recaman.ShortCounterFactorBounds

theorem long_initial (S R M h m s L W K : Int) (hS : 8<S) (hS14 : S≤14)
    (hR : 5≤R) (hR7 : R≤7) (hM4 : 4≤M) (hMb : M≤R+1)
    (hm : 1≤m) (hs : 1≤s) (hL : 1≤L) (hshape : S=h+m+s)
    (hW : W=M+L) (hW9 : W≤9) (hw : 2*S≤W+19)
    (hK : K=M*(m+s)+L*s) (hc : R^2+27+2*K≤(S-4)^2) : 2*M≤h+3 := by
  by_cases hl : 2*M≤h+3
  · exact hl
  exfalso
  have hLs:=Int.mul_nonneg (show 0≤L-1 by omega) (show 0≤s by omega)
  have heLs : (L-1)*s=L*s-s := by grind only
  have he4 : (S-4)^2=S^2-8*S+16 := by grind only
  by_cases hq2 : m+s=2
  · have hk : S+3≤K := by rw [hq2] at hK; omega
    have hsq:=square_lower (2*R) S (by omega) (by omega)
    have heR : (2*R)^2=4*R^2 := by grind only
    have hp:=Int.mul_nonneg (show 0≤S by omega) (show 0≤14-S by omega)
    have he : S*(14-S)=14*S-S^2 := by grind only
    omega
  · have hq3 : 3≤m+s := by omega
    have hqprod:=Int.mul_nonneg (show 0≤M by omega) (show 0≤m+s-3 by omega)
    have heq : M*(m+s-3)=M*(m+s)-3*M := by grind only
    have hk : W+2*M≤K := by omega
    have hpoly : R^2+4*M-27≤S^2-12*S := by omega
    have hR25:=square_lower R 5 (by omega) hR
    have hS14eq : S=14 := by
      by_cases h13 : S≤13
      · have hp:=Int.mul_nonneg (show 0≤S by omega) (show 0≤13-S by omega)
        have he : S*(13-S)=13*S-S^2 := by grind only
        omega
      · omega
    have hR6 : R≤6 := by
      by_cases h6 : R≤6
      · exact h6
      have hp:=square_lower R 7 (by omega) (by omega)
      rw [hS14eq] at hpoly
      omega
    have hM6 : M≤6 := by
      by_cases hm6 : M≤6
      · exact hm6
      have hp:=square_lower R 6 (by omega) (by omega)
      rw [hS14eq] at hpoly
      omega
    have hp:=Int.mul_nonneg (show 0≤M-4 by omega) (show 0≤6-M by omega)
    have he : (M-4)*(6-M)=10*M-M^2-24 := by grind only
    have hq : 18-2*M≤m+s := by omega
    have hpq:=Int.mul_nonneg (show 0≤M by omega) (show 0≤m+s-(18-2*M) by omega)
    have heq2 : M*(m+s-(18-2*M))=M*(m+s)-18*M+2*M^2 := by grind only
    rw [hS14eq] at hc
    omega

/-- With the actual first-prefix bound, counters reduce to a few source shapes. -/
theorem residual (S R M m s L W K : Int) (hS : 8<S) (hS13 : S≤13) (hR : 5≤R)
    (hM : 1≤M) (hm : 1≤m) (hs : 1≤s) (hL : 1≤L) (hMb : M≤R+1)
    (hW : W=M+L) (hW8 : W≤8) (hw : 2*S≤W+19)
    (hWM : W+M≤K) (hK : K=M*(m+s)+L*s)
    (hsmall : M≤2 → S≤12)
    (hc : R^2+27+2*K≤(S-4)^2) :
    (M=1 ∧ m=1 ∧ s=1 ∧ S=12 ∧ R=5) ∨
    (S=13 ∧ R=5 ∧ 7≤W ∧ W≤8 ∧
      ((M=3 ∧ m≤3) ∨ (4≤M ∧ M≤7 ∧ m=1 ∧ s=1))) := by
  have he4 : (S-4)^2=S^2-8*S+16 := by grind only
  have hpoly : R^2+2*M-27≤S^2-12*S := by omega
  have hR25:=square_lower R 5 (by omega) hR
  by_cases hM2 : M≤2
  · have hS12:=hsmall hM2
    have hp:=Int.mul_nonneg (show 0≤S by omega) (show 0≤12-S by omega)
    have he : S*(12-S)=12*S-S^2 := by grind only
    have hMeq : M=1 := by omega
    have hR5 : R=5 := by
      by_cases hr : R=5
      · exact hr
      have hp6:=square_lower R 6 (by omega) (by omega)
      omega
    have hS12eq : S=12 := by
      have hsq:=square_lower 7 (S-4) (by omega) (by omega)
      by_cases h12 : S=12
      · exact h12
      have hp11:=square_lower 7 (S-4) (by omega) (by omega)
      omega
    have hW5 : W=5 := by rw [hS12eq,hR5] at hc hw; omega
    have hL4 : L=4 := by omega
    rw [hMeq,hL4] at hK
    left
    omega
  · have hM3 : 3≤M := by omega
    have hS13eq : S=13 := by
      by_cases h12 : S≤12
      · have hp:=Int.mul_nonneg (show 0≤S by omega) (show 0≤12-S by omega)
        have he : S*(12-S)=12*S-S^2 := by grind only
        omega
      · omega
    have hR5 : R=5 := by
      by_cases hr : R=5
      · exact hr
      have hp6:=square_lower R 6 (by omega) (by omega)
      rw [hS13eq] at hpoly
      omega
    have hK14 : K≤14 := by rw [hS13eq,hR5] at hc; omega
    have hW7 : 7≤W := by omega
    have hpLs:=Int.mul_nonneg (show 0≤L-1 by omega) (show 0≤s by omega)
    have heLs : (L-1)*s=L*s-s := by grind only
    have hshape : (M=3 ∧ m≤3) ∨ (4≤M ∧ M≤7 ∧ m=1 ∧ s=1) := by
      by_cases hMexact : M=3
      · left
        rw [hMexact] at hK
        omega
      · right
        have hM4 : 4≤M := by omega
        have hpq:=Int.mul_nonneg (show 0≤M by omega) (show 0≤m+s-3 by omega)
        have heq : M*(m+s-3)=M*(m+s)-3*M := by grind only
        have hq2 : m+s=2 := by
          by_cases hq : m+s=2
          · exact hq
          omega
        omega
    right
    exact ⟨hS13eq,hR5,hW7,hW8,hshape⟩
end Recaman.MassFourTwoArithmetic
