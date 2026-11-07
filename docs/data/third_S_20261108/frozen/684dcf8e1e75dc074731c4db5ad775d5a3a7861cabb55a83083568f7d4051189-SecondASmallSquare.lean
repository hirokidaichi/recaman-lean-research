import Recaman.ShortEarlyHeadBudget

namespace Recaman.SecondASmallSquare

theorem short_square_impossible (D R a U v : Int)
    (hD : 6≤D) (hD7 : D≤7) (hR : 5≤R) (hRD : R<D)
    (ha : 1≤a) (hv : 1≤v) (hU : D≤U) (hUR : U≤R+2)
    (hsq : D^2=R^2+a^2+2*U*v) : False := by
  have ha1:=Recaman.ShortCounterFactorBounds.square_lower a 1 (by decide) ha
  have huv : D≤U*v := by
    have hp:=Int.mul_nonneg (show 0≤U by omega) (show 0≤v-1 by omega)
    grind only
  have hd : D=6 ∨ D=7 := by omega
  rcases hd with hd|hd
  · have hr : R=5 := by omega
    subst D; subst R
    grind only
  · subst D
    have hr : R=5 ∨ R=6 := by omega
    rcases hr with hr|hr
    · subst R
      have hu : U=7 := by omega
      subst U
      have hv1 : v=1 := by
        by_cases he : v=1
        · exact he
        · have hv2 : 2≤v := by omega
          grind only
      subst v
      have hasq : a^2=10 := by grind only
      by_cases ha3 : a≤3
      · have hh:=Recaman.ShortCounterFactorBounds.square_upper a 3 (by omega) ha3
        omega
      · have hh:=Recaman.ShortCounterFactorBounds.square_lower a 4 (by decide) (by omega)
        omega
    · subst R
      grind only

end Recaman.SecondASmallSquare
