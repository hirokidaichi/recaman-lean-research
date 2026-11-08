import Recaman.TwoSTargetBounds

namespace Recaman.TwoSLastFourEnergy

/-- Completing the square loses only two units, less than the gap
between consecutive squares once R>=5. -/
theorem target_residual (L U v z R D : Int) (hU : 1≤U) (hv : 1≤v)
    (hR : 5≤R) (hD : 0≤D) (hbal : D+L=z+2)
    (hsq : (z+2)^2=R^2+2*L*z+2*U*v) :
    D^2=R^2+(L-2)^2-4+2*U*v ∧ R≤D := by
  have he : D^2=R^2+(L-2)^2-4+2*U*v := by grind only
  have hp:=Int.sq_nonneg (L-2)
  have huv:=Int.mul_pos (show 0<U by omega) (show 0<v by omega)
  refine ⟨he,?_⟩
  by_cases hh : R≤D
  · exact hh
  · have hu:=Recaman.ShortCounterFactorBounds.square_lower (R-1) D hD (by omega)
    have hid : (R-1)^2=R^2-2*R+1 := by grind only
    omega

/-- This small complete certificate keeps just the energy U*v=7;
it does not enumerate the source's S/A/S shapes. -/
theorem last_four_energy (L U v R D : Int) (hR : 5≤R) (hRD : R≤D) (hD6 : D≤6)
    (hU : D+1≤U) (hUR : U≤R+2) (hv : 1≤v)
    (he : D^2=R^2+(L-2)^2-4+2*U*v) :
    R=5 ∧ D=6 ∧ U=7 ∧ v=1 := by
  have hp:=Int.sq_nonneg (L-2)
  have hq:=Int.mul_nonneg (show 0≤U by omega) (show 0≤v-1 by omega)
  have hc : (D=5 ∧ R=5) ∨ (D=6 ∧ R=5) ∨ (D=6 ∧ R=6) := by omega
  rcases hc with h5|h65|h6
  · rw [h5.1,h5.2] at he
    grind only
  · have hu : U=7 := by omega
    refine ⟨h65.2,h65.1,hu,?_⟩
    rw [h65.1,h65.2,hu] at he
    omega
  · rw [h6.1,h6.2] at he
    grind only

end Recaman.TwoSLastFourEnergy
