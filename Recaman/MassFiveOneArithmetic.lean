import Recaman.ShortCounterFactorBounds

namespace Recaman.MassFiveOneArithmetic
open Recaman.ShortCounterFactorBounds

/-- A counter forces a long initial S block. Scalar inputs are supplied from the same actual head. -/
theorem long_initial (S R M h m s L K : Int) (hS : 10<S) (hS16 : S≤16)
    (hR : 5≤R) (hM : 4≤M) (hm : 1≤m) (hs : 1≤s) (hL : 1≤L)
    (hshape : S=h+m+s) (hMbound : M≤R+1) (hhead : S≤R+9)
    (hK : K=M*(m+s)+L*s) (hcircle : R^2+33+2*K≤(S-5)^2) : 2*M≤h+3 := by
  by_cases hn : 2*M≤h+3
  · exact hn
  exfalso
  have hLs : 1≤L*s := by
    have hp:=Int.mul_nonneg (show 0≤L-1 by omega) (show 0≤s by omega)
    have he : (L-1)*s=L*s-s := by grind only
    omega
  have he : (S-5)^2=S^2-10*S+25 := by grind only
  by_cases hq : m+s=2
  · have hk : S+3≤K := by rw [hq] at hK; omega
    have hSR : S≤2*R := by omega
    have hsq:=square_lower (2*R) S (by omega) hSR
    have heR : (2*R)^2=4*R^2 := by grind only
    have hp:=Int.mul_nonneg (show 0≤S by omega) (show 0≤16-S by omega)
    have hpE : S*(16-S)=16*S-S^2 := by grind only
    omega
  · have hq3 : 3≤m+s := by omega
    have hp:=Int.mul_nonneg (show 0≤M-4 by omega) (show 0≤m+s-2 by omega)
    have hpe : (M-4)*(m+s-2)=M*(m+s)-2*M-4*(m+s)+8 := by grind only
    have hk : S+6≤K := by omega
    have hsq:=square_lower R (S-9) (by omega) (by omega)
    have he9 : (S-9)^2=S^2-18*S+81 := by grind only
    omega

/-- Two run count weights and source-conditioned head budgets exclude mass5/separator1. -/
theorem excluded (S R M m s L W K : Int) (hS : 10<S) (hS16 : S≤16)
    (hR : 5≤R) (hR8 : R≤8) (hMpos : 1≤M) (hm : 1≤m) (hs : 1≤s) (hL : 1≤L)
    (hW : W=M+L) (hKdef : K=M*(m+s)+L*s) (hK3 : 3≤K)
    (hWM : W+M≤K) (hweighted : 2*S≤W+23)
    (hsmall2 : M≤2 → S≤R+7) (hsmall3 : M=3 → S≤R+8)
    (hspecial : M=3 → m=1 → S≤R+7)
    (hlong : 4≤M → S≤R+8)
    (hcircle : R^2+33+2*K≤(S-5)^2) : False := by
  have he : (S-5)^2=S^2-10*S+25 := by grind only
  have hpoly : R^2+2*M-38≤S^2-14*S := by omega
  have small_eight (hupper : S≤R+7) : False := by
    have hp:=Int.mul_nonneg (show 0≤R+7-S by omega) (show 0≤R+7+S-14 by omega)
    have hpe : (R+7-S)*(R+7+S-14)=R^2-49-(S^2-14*S) := by grind only
    omega
  by_cases hM2 : M≤2
  · exact small_eight (hsmall2 hM2)
  by_cases hM3 : M=3
  · by_cases hm1 : m=1
    · exact small_eight (hspecial hM3 hm1)
    · have hq : 3≤m+s := by omega
      have hp:=Int.mul_nonneg (show 0≤L by omega) (show 0≤s-1 by omega)
      have hpe : L*(s-1)=L*s-L := by grind only
      have hk : W+6≤K := by rw [hM3] at hKdef hW; omega
      have hu:=hsmall3 hM3
      have hp2:=Int.mul_nonneg (show 0≤R+8-S by omega) (show 0≤R+8+S-14 by omega)
      have he2 : (R+8-S)*(R+8+S-14)=R^2+2*R-48-(S^2-14*S) := by grind only
      omega
  have hM4 : 4≤M := by omega
  have hu:=hlong hM4
  have hp:=Int.mul_nonneg (show 0≤R+8-S by omega) (show 0≤R+8+S-14 by omega)
  have hpe : (R+8-S)*(R+8+S-14)=R^2+2*R-48-(S^2-14*S) := by grind only
  omega
end Recaman.MassFiveOneArithmetic
