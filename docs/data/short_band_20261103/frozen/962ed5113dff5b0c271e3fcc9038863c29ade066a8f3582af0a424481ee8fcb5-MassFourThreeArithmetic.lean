import Recaman.ShortCounterFactorBounds
namespace Recaman.MassFourThreeArithmetic
open Recaman.ShortCounterFactorBounds

/-- Scalar support for a source-conditioned last3 branch. -/
theorem nonboundary (S R M W K : Int) (hS : 8<S) (hS12 : S≤12) (hR : 5≤R)
    (hM : 1≤M) (hK : W+M≤K) (hw : 2*S≤W+17)
    (hc : R^2+30+2*K≤(S-4)^2) : False := by
  have hp:=Int.mul_nonneg (show 0≤S by omega) (show 0≤12-S by omega)
  have he : S*(12-S)=12*S-S^2 := by grind only
  have he4 : (S-4)^2=S^2-8*S+16 := by grind only
  have hs:=square_lower R 5 (by omega) hR
  omega

/-- Not-long geometry contradicts the bounded same-target circle; no history enumeration. -/
theorem notlong (S R : Int) (hS : 8<S) (hS14 : S≤14) (hR : 5≤R) (hR7 : R≤7)
    (hc : R^2+32+2*(R+1)*(S-2*R+2)≤(S-4)^2) : False := by
  have hp:=Int.mul_nonneg (show 0≤S-9 by omega) (show 0≤14-S by omega)
  have he : (S-9)*(14-S)=23*S-S^2-126 := by grind only
  have he4 : (S-4)^2=S^2-8*S+16 := by grind only
  rcases (show R=5 ∨ R=6 ∨ R=7 by omega) with h5 | h6 | h7
  · subst R
    have hx : (5 : Int)^2+32+2*(5+1)*(S-2*5+2)=12*S-39 := by grind only
    omega
  · subst R
    have hx : (6 : Int)^2+32+2*(6+1)*(S-2*6+2)=14*S-72 := by grind only
    omega
  · subst R
    have hx : (7 : Int)^2+32+2*(7+1)*(S-2*7+2)=16*S-111 := by grind only
    omega

theorem boundary_geometry (S R M h m s L K : Int) (hS : 8<S) (hS14 : S≤14)
    (hR : 5≤R) (hR7 : R≤7) (hm : 1≤m) (hs : 1≤s) (hL : 1≤L)
    (hshape : S=h+m+s) (hM : M=R+1) (hK : K=M*(m+s)+L*s)
    (hc : R^2+30+2*K≤(S-4)^2) : 2*M≤h+3 := by
  by_cases hl : 2*M≤h+3
  · exact hl
  exfalso
  have hq : S-2*R+2≤m+s := by omega
  have hp:=Int.mul_nonneg (show 0≤M by omega) (show 0≤m+s-(S-2*R+2) by omega)
  have he : M*(m+s-(S-2*R+2))=M*(m+s)-M*(S-2*R+2) := by grind only
  have hlp:=Int.mul_nonneg (show 0≤L-1 by omega) (show 0≤s by omega)
  have hle : (L-1)*s=L*s-s := by grind only
  have hmul : 2*(R+1)*(S-2*R+2)=2*(M*(S-2*R+2)) := by rw [hM]; grind only
  have hx : R^2+32+2*(R+1)*(S-2*R+2)≤(S-4)^2 := by rw [hmul]; omega
  exact notlong S R hS hS14 hR hR7 hx

theorem boundary_small (S R M m s L K : Int) (hS : 8<S) (hS14 : S≤14)
    (hR : 5≤R) (hR7 : R≤7) (hm : 1≤m) (hs : 1≤s) (hL : 1≤L)
    (hM : M=R+1) (hhead9 : S≤R+8) (hK : K=M*(m+s)+L*s)
    (hc : R^2+30+2*K≤(S-4)^2) : (M=6 ∨ M=7) ∧ m=1 := by
  have hlp:=Int.mul_nonneg (show 0≤L-1 by omega) (show 0≤s by omega)
  have hle : (L-1)*s=L*s-s := by grind only
  have hp:=Int.mul_nonneg (show 0≤M by omega) (show 0≤m+s-2 by omega)
  have he : M*(m+s-2)=M*(m+s)-2*M := by grind only
  have hsquare:=square_lower 10 (S-4) (by omega) (by omega)
  have hR6 : R≤6 := by
    by_cases hr : R≤6
    · exact hr
    have hreq : R=7 := by omega
    rw [hreq] at hc hM
    omega
  have hq2 : m+s=2 := by
    by_cases hq : m+s=2
    · exact hq
    have hp3:=Int.mul_nonneg (show 0≤M by omega) (show 0≤m+s-3 by omega)
    have he3 : M*(m+s-3)=M*(m+s)-3*M := by grind only
    have hsquare2:=square_lower (R+4) (S-4) (by omega) (by omega)
    have heR : (R+4)^2=R^2+8*R+16 := by grind only
    omega
  constructor
  · omega
  · omega

theorem boundary_excluded (S R M L K : Int) (hR : 5≤R) (hR6 : R≤6)
    (hM : M=R+1) (hL : 1≤L) (hK : 2*M+L≤K) (hS : 8<S) (hhead8 : S≤R+7)
    (hc : R^2+30+2*K≤(S-4)^2) : False := by
  have hsquare:=square_lower (R+3) (S-4) (by omega) (by omega)
  have he : (R+3)^2=R^2+6*R+9 := by grind only
  omega
end Recaman.MassFourThreeArithmetic
