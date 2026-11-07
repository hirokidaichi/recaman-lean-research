import Recaman.SecondASmallSquare
namespace Recaman.UnitSTargetSquare

theorem unit_S_square_choices (D R L U v : Int)
    (hD : 6≤D) (hD7 : D≤7) (hR : 5≤R) (hRD : R<D)
    (hL : 1≤L) (hv : 1≤v) (hU : D≤U) (hUR : U≤R+2)
    (hsq : D^2=R^2+L^2-2*L+2*U*v) :
    L=1 ∧ U=D ∧ v=1 ∧ D=R+1 := by
  have hl:=Int.mul_nonneg (show 0≤L-1 by omega) (show 0≤L-1 by omega)
  have huv : D≤U*v := by
    have hp:=Int.mul_nonneg (show 0≤U by omega) (show 0≤v-1 by omega)
    grind only
  have same_step (he : D=R+1) : L=1 ∧ U=D ∧ v=1 ∧ D=R+1 := by
    have hp:=Int.mul_nonneg (show 0≤U-D by omega) (show 0≤v by omega)
    have hvp:=Int.mul_nonneg (show 0≤D by omega) (show 0≤v-1 by omega)
    have hzero : (L-1)^2=0 := by grind only
    have hL1 : L=1 := by
      by_cases he : L=1
      · exact he
      · have hh:=Recaman.ShortCounterFactorBounds.square_lower (L-1) 1 (by decide) (by omega)
        omega
    have hv1 : v=1 := by
      by_cases he : v=1
      · exact he
      · have hh : 2≤v := by omega
        have hp:=Int.mul_nonneg (show 0≤U by omega) (show 0≤v-2 by omega)
        grind only
    refine ⟨hL1,?_,hv1,he⟩
    rw [hL1,hv1] at hsq
    grind only
  have hd : D=6 ∨ D=7 := by omega
  rcases hd with hd|hd
  · exact same_step (by omega)
  · by_cases he : R=6
    · exact same_step (by omega)
    · have hr : R=5 := by omega
      have hu : U=7 := by omega
      rw [hd,hr,hu] at hsq
      have hv1 : v=1 := by
        by_cases he : v=1
        · exact he
        · have hh : 2≤v := by omega
          grind only
      rw [hv1] at hsq
      have he : (L-1)^2=11 := by grind only
      by_cases hL4 : L≤4
      · have hp:=Int.mul_nonneg (show 0≤4-L by omega) (show 0≤L+2 by omega)
        grind only
      · have hp:=Recaman.ShortCounterFactorBounds.square_lower (L-1) 4 (by decide) (by omega)
        omega
end Recaman.UnitSTargetSquare
