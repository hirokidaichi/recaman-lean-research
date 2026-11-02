import Recaman.ShortCounterFactorBounds

namespace Recaman.MassFiveTwoArithmetic

open Recaman.ShortCounterFactorBounds

/-- Scalar support; every budget is supplied by the actual theorem. -/
theorem excluded (S R M W K : Int) (hS : 10<S) (hR : 5≤R) (hR6 : R≤6)
    (hhead : S≤R+9) (hsmall : M≤3 → S≤R+8) (hK3 : 3≤K)
    (hWM : W+M≤K) (hweighted : 2*S≤W+21)
    (hcircle : R^2+40+2*K≤(S-5)^2) : False := by
  by_cases hM3 : M≤3
  · have hs:=hsmall hM3
    have hsq:=square_lower (R+3) (S-5) (by omega) (by omega)
    have he : (R+3)^2=R^2+6*R+9 := by grind only
    omega
  · have hK : 2*S-17≤K := by omega
    have hp:=Int.mul_nonneg (show 0≤(R+9)-S by omega) (show 0≤(R+9)+S-14 by omega)
    have he : ((R+9)-S)*((R+9)+S-14)=R^2+4*R-45-(S^2-14*S) := by grind only
    have hx : (S-5)^2=S^2-10*S+25 := by grind only
    omega

end Recaman.MassFiveTwoArithmetic
