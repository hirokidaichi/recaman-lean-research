import Recaman.SecondASmallSquare

namespace Recaman.UnitSLongAExclusion

/-- A positive factor certificate excludes a long second A after the
new actual last-six cut has bounded the same target's S residual. -/
theorem unit_target_L_cut (L U v z R : Int) (hL : 1≤L) (hU : 1≤U) (hv : 1≤v)
    (hz : 1≤z) (hz13 : z≤13) (hR : 5≤R)
    (hsq : (z+1)^2=R^2+2*L*z+2*U*v) : L≤7 := by
  by_cases he : L≤7
  · exact he
  · have hp:=Int.mul_nonneg (show 0≤L-8 by omega) (show 0≤z by omega)
    have hq:=Int.mul_nonneg (show 0≤z by omega) (show 0≤14-z by omega)
    have hr:=Recaman.ShortCounterFactorBounds.square_lower R 5 (by decide) hR
    have huv:=Int.mul_pos (show 0<U by omega) (show 0<v by omega)
    grind only

end Recaman.UnitSLongAExclusion
