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

/-- The same target square keeps a positive residual after removing L. -/
theorem unit_target_residual (L U v z R D : Int) (hL : 1≤L) (hU : 1≤U)
    (hv : 1≤v) (hR : 0≤R) (hD : 0≤D) (hbal : D+L=z+1)
    (hsq : (z+1)^2=R^2+2*L*z+2*U*v) :
    D^2=R^2+L^2-2*L+2*U*v ∧ R<D := by
  have hd2 : D^2=D*D := by grind only
  have hr2 : R^2=R*R := by grind only
  have hl2 : L^2=L*L := by grind only
  have hz2 : (z+1)^2=(z+1)*(z+1) := by grind only
  rw [hz2,hr2] at hsq
  have he : D*D=R*R+L*L-2*L+2*U*v := by grind only
  refine ⟨by rw [hd2,hr2,hl2]; exact he,?_⟩
  by_cases hlt : R<D
  · exact hlt
  · have hp:=Int.mul_nonneg (show 0≤R-D by omega) (show 0≤R+D by omega)
    have hq:=Int.mul_nonneg (show 0≤L-1 by omega) (show 0≤L-1 by omega)
    have hu:=Int.mul_pos (show 0<U by omega) (show 0<v by omega)
    grind only

/-- The new actual last-four cut forces U>=7 at D6/R5, so the
remaining target square has no solution even at its weakest L1 bound. -/
theorem last_four_square_impossible (L U v : Int) (hL : 1≤L) (hU : 7≤U)
    (hv : 1≤v) (he : 36=25+L^2-2*L+2*U*v) : False := by
  have hp:=Int.mul_nonneg (show 0≤L-1 by omega) (show 0≤L-1 by omega)
  have hq:=Int.mul_nonneg (show 0≤U by omega) (show 0≤v-1 by omega)
  rw [show L^2=L*L by grind only] at he
  grind only

end Recaman.UnitSLongAExclusion
