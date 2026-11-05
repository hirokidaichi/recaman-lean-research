import Recaman.ShortCounterFactorBounds

namespace Recaman.ThirdSShortTwo

open Recaman.ShortCounterFactorBounds

private theorem le_of_square_le (x y : Int) (hx : 0≤x) (hy : 0≤y) (h : x^2≤y^2) : x≤y := by
  by_cases he : x≤y
  · exact he
  · have hp:=Int.mul_pos (show 0<x-y by omega) (show 0<x+y by omega)
    grind only

private theorem between_squares (x R : Int) (hx : 0≤x) (hr : 0≤R)
    (hl : x^2<R^2) (hh : R^2<(x+1)^2) : False := by
  by_cases h : R≤x
  · have hsq:=square_lower x R hr h
    omega
  · have hsq:=square_lower R (x+1) (by omega) (by omega)
    omega

/-- One or two residual S signs force a long final ray, except for
the single short q2 scalar case. No finite head search is used. -/
theorem third_S_short_two (q U v T R : Int)
    (hq : 1≤q) (hq2 : q≤2) (hU : 1≤U) (hv : 1≤v) (hT : 1≤T) (hR : 1≤R)
    (hm : T+U=R+q+v) (hs : (q+v)^2=R^2+2*U*v) :
    q+R≤v ∨ (R=2 ∧ U=3 ∧ v=2 ∧ T=3) := by
  by_cases hlarge : 2*q≤U
  · have hp:=Int.mul_nonneg (show 0≤U-2*q by omega) (show 0≤v by omega)
    by_cases hV : q≤v
    · have hs' : R^2≤(v-q)^2 := by grind only
      exact Or.inl (by have h:=le_of_square_le R (v-q) (by omega) (by omega) hs'; omega)
    · have hs' : R^2≤(q-v)^2 := by grind only
      have h:=le_of_square_le R (q-v) (by omega) (by omega) hs'
      omega
  · by_cases hq1 : q=1
    · have hU1 : U=1 := by omega
      rw [hq1,hU1] at hs
      exact False.elim (between_squares v R (by omega) (by omega) (by grind only) (by grind only))
    · have hq' : q=2 := by omega
      rw [hq'] at hs
      rcases (show U=1 ∨ U=2 ∨ U=3 by omega) with h1|h2|h3
      · rw [h1] at hs
        exact False.elim (between_squares (v+1) R (by omega) (by omega) (by grind only) (by grind only))
      · rw [h2] at hs
        by_cases hV1 : v=1
        · rw [hV1] at hs
          exact False.elim (between_squares 2 R (by decide) (by omega) (by grind only) (by grind only))
        · exact False.elim (between_squares v R (by omega) (by omega) (by grind only) (by grind only))
      · rw [h3] at hs
        by_cases hV3 : 3≤v
        · exact False.elim (between_squares (v-1) R (by omega) (by omega) (by grind only) (by grind only))
        · rcases (show v=1 ∨ v=2 by omega) with hV1|hV2
          · rw [hV1] at hs
            exact False.elim (between_squares 1 R (by decide) (by omega) (by grind only) (by grind only))
          · rw [hV2] at hs
            have hr : R=2 := by
              have hp : (R-2)*(R+2)=0 := by grind only
              rcases Int.mul_eq_zero.mp hp with he|he <;> omega
            exact Or.inr ⟨hr,h3,hV2,by omega⟩

theorem third_S_target_long_ray (q U v T R : Int) (hq : 0≤q) (hv : 1≤v)
    (hV : q+R≤v) (hm : T+U=R+q+v)
    (hs : (q+v)^2=R^2+2*U*v) : 2*R≤T := by
  have he : 2*v*(T-2*R)=(v-R)^2-q^2 := by
    rw [show U=R+q+v-T by omega] at hs
    grind only
  have hp:=square_lower (v-R) q hq (by omega)
  by_cases he' : 2*R≤T
  · exact he'
  · have hneg:=Int.mul_neg_of_pos_of_neg (show 0<2*v by omega) (show T-2*R<0 by omega)
    omega

end Recaman.ThirdSShortTwo
