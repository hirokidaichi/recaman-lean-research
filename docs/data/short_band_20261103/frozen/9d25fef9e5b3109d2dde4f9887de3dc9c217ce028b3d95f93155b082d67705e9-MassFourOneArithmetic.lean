import Recaman.ShortCounterFactorBounds
namespace Recaman.MassFourOneArithmetic
open Recaman.ShortCounterFactorBounds

theorem large_R_excluded (S R M h m s L W K : Int) (hS : 8<S) (hS15 : S≤15)
    (hR : 5≤R) (hM : 1≤M) (hm : 1≤m) (hs : 1≤s) (hL : 1≤L)
    (hshape : S=h+m+s) (hW : W=M+L) (hw : 2*S≤W+21) (hWM : W+M≤K)
    (hK : K=M*(m+s)+L*s) (hbudget : M≤3 ∨ 2*M≤h+3 → S≤14)
    (hc : R^2+22+2*K≤(S-4)^2) : R≤7 := by
  by_cases hR7 : R≤7
  · exact hR7
  exfalso
  have he4 : (S-4)^2=S^2-8*S+16 := by grind only
  have hpoly : R^2+2*M-36≤S^2-12*S := by omega
  have hp:=Int.mul_nonneg (show 0≤15-S by omega) (show 0≤S+3 by omega)
  have he : (15-S)*(S+3)=45-(S^2-12*S) := by grind only
  have hR8 : R=8 := by
    by_cases h8 : R=8
    · exact h8
    have hs9:=square_lower R 9 (by omega) (by omega)
    omega
  have hS15eq : S=15 := by
    by_cases h15 : S=15
    · exact h15
    have hs14:=Int.mul_nonneg (show 0≤14-S by omega) (show 0≤S+2 by omega)
    have he14 : (14-S)*(S+2)=28-(S^2-12*S) := by grind only
    rw [hR8] at hpoly
    omega
  have hK17 : K≤17 := by rw [hR8,hS15eq] at hc; omega
  have hW9 : 9≤W := by omega
  have hM8 : M≤8 := by omega
  have hM4 : 4≤M := by
    by_cases h3 : M≤3
    · have hb:=hbudget (Or.inl h3); omega
    · omega
  have hlong : 2*M≤h+3 := by
    by_cases hq2 : m+s=2
    · omega
    · have hLp:=Int.mul_nonneg (show 0≤L by omega) (show 0≤s-1 by omega)
      have hLe : L*(s-1)=L*s-L := by grind only
      have hMp:=Int.mul_nonneg (show 0≤M by omega) (show 0≤m+s-3 by omega)
      have hMe : M*(m+s-3)=M*(m+s)-3*M := by grind only
      have hM4eq : M=4 := by omega
      rw [hM4eq] at hK
      change K=4*(m+s)+L*s at hK
      omega
  have hb:=hbudget (Or.inr hlong)
  omega

theorem S15_residual (S R M h m s L W K : Int) (hS15 : S=15) (hR : 5≤R) (hR7 : R≤7)
    (hM : 1≤M) (hm : 1≤m) (hs : 1≤s) (hL : 1≤L) (hMb : M≤R+1)
    (hshape : S=h+m+s) (hW : W=M+L) (hK : K=M*(m+s)+L*s)
    (hbudget : M≤3 ∨ 2*M≤h+3 → S≤14)
    (hc : R^2+22+2*K≤(S-4)^2) : R=7 ∧ M=8 ∧ h=12 ∧ m=2 ∧ s=1 ∧ L=1 := by
  have hM4 : 4≤M := by
    by_cases h3 : M≤3
    · have hb:=hbudget (Or.inl h3); omega
    · omega
  have hnotlong : h+4≤2*M := by
    by_cases hl : 2*M≤h+3
    · have hb:=hbudget (Or.inr hl); omega
    · omega
  have hq : 19-2*M≤m+s := by omega
  have hpq:=Int.mul_nonneg (show 0≤M by omega) (show 0≤m+s-(19-2*M) by omega)
  have heq : M*(m+s-(19-2*M))=M*(m+s)-19*M+2*M^2 := by grind only
  have hLp:=Int.mul_nonneg (show 0≤L-1 by omega) (show 0≤s by omega)
  have hLe : (L-1)*s=L*s-s := by grind only
  have hM8 : M=8 := by
    by_cases h8 : M=8
    · exact h8
    have hM7 : M≤7 := by omega
    have hp:=Int.mul_nonneg (show 0≤M-4 by omega) (show 0≤7-M by omega)
    have he : (M-4)*(7-M)=11*M-M^2-28 := by grind only
    have hR5 : R=5 := by
      by_cases hr : R=5
      · exact hr
      have hs6:=square_lower R 6 (by omega) (by omega)
      rw [hS15] at hc
      omega
    have hM6 : M≤6 := by omega
    have hp6:=Int.mul_nonneg (show 0≤M-4 by omega) (show 0≤6-M by omega)
    have he6 : (M-4)*(6-M)=10*M-M^2-24 := by grind only
    rw [hS15,hR5] at hc
    omega
  have hR7eq : R=7 := by omega
  have hK25 : K≤25 := by rw [hS15,hR7eq] at hc; omega
  rw [hM8] at hK
  change K=8*(m+s)+L*s at hK
  have hq3 : m+s=3 := by omega
  rw [hq3] at hK
  have hL1 : L=1 := by
    have hp:=Int.mul_nonneg (show 0≤L by omega) (show 0≤s-1 by omega)
    have he : L*(s-1)=L*s-L := by grind only
    omega
  rw [hL1] at hK
  omega
theorem small_inversion_impossible (S R M W K : Int) (hS : 8<S) (hS12 : S≤12)
    (hR : 5≤R) (hM : 1≤M) (hw : 2*S≤W+21) (hK : W+M≤K) (hK3 : 3≤K)
    (hhead : S≤R+6) (hc : R^2+22+2*K≤(S-4)^2) : False := by
  have he4 : (S-4)^2=S^2-8*S+16 := by grind only
  have hp:=Int.mul_nonneg (show 0≤S by omega) (show 0≤12-S by omega)
  have he : S*(12-S)=12*S-S^2 := by grind only
  have hR5 : R=5 := by
    by_cases h5 : R=5
    · exact h5
    have hs6:=square_lower R 6 (by omega) (by omega)
    omega
  have hs7:=square_lower 7 (S-4) (by omega) (by omega)
  rw [hR5] at hc
  omega

theorem inversion_three_bands (S R K : Int) (hS : 8<S) (hS14 : S≤14)
    (hR : 5≤R) (hK17 : 17≤K) (hc : R^2+22+2*K≤(S-4)^2) :
    (S=13 ∧ R=5 ∧ K=17) ∨ (S=14 ∧ R=5 ∧ 17≤K ∧ K≤26) ∨
    (S=14 ∧ R=6 ∧ 17≤K ∧ K≤21) := by
  have hs10:=square_lower 10 (S-4) (by omega) (by omega)
  have hR6 : R≤6 := by
    by_cases h6 : R≤6
    · exact h6
    have hs7:=square_lower R 7 (by omega) (by omega)
    omega
  have hS13 : 13≤S := by
    by_cases h13 : 13≤S
    · exact h13
    have hs8:=square_lower 8 (S-4) (by omega) (by omega)
    have hs5:=square_lower R 5 (by omega) hR
    omega
  by_cases hS13eq : S=13
  · have hR5 : R=5 := by
      by_cases h5 : R=5
      · exact h5
      have hs6:=square_lower R 6 (by omega) (by omega)
      rw [hS13eq] at hc
      omega
    rw [hS13eq,hR5] at hc
    exact Or.inl ⟨hS13eq,hR5,by omega⟩
  · have hS14eq : S=14 := by omega
    by_cases hR5 : R=5
    · rw [hS14eq,hR5] at hc
      exact Or.inr (Or.inl ⟨hS14eq,hR5,hK17,by omega⟩)
    · have hR6eq : R=6 := by omega
      rw [hS14eq,hR6eq] at hc
      exact Or.inr (Or.inr ⟨hS14eq,hR6eq,hK17,by omega⟩)
end Recaman.MassFourOneArithmetic
