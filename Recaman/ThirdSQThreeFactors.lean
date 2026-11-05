import Recaman.ThirdSShortTwo

namespace Recaman.ThirdSQThreeFactors

open Recaman.ShortCounterFactorBounds Recaman.ThirdSShortTwo

private theorem square_gap_three_constants (x R c : Int) (hx : 0≤x) (hR : 1≤R)
    (hc : c=5 ∨ c=8 ∨ c=9) (h : R^2=x^2+c) :
    R=3 ∨ (c=9 ∧ R=5 ∧ x=4) := by
  have hxR : x<R := by
    by_cases hh : x<R
    · exact hh
    · have hb:=square_lower x R (by omega) (by omega)
      omega
  let d:=R-x
  have hd : 1≤d := by dsimp [d]; omega
  have hfac : d*(R+x)=c := by dsimp [d]; grind only
  have hd3 : d≤3 := by
    by_cases hh : d≤3
    · exact hh
    · have h4 : 4≤R+x := by dsimp [d] at hh; omega
      have hp:=Int.mul_nonneg (show 0≤d-4 by omega) (show 0≤R+x-4 by omega)
      have hb : 16≤d*(R+x) := by grind only
      omega
  rcases (show d=1 ∨ d=2 ∨ d=3 by omega) with h1|h2|h3
  · rw [h1,Int.one_mul] at hfac
    dsimp [d] at h1
    omega
  · rw [h2] at hfac
    dsimp [d] at h2
    omega
  · rw [h3] at hfac
    dsimp [d] at h3
    omega

/-- Fixing residual q3 before classifying the factor leaves one
nonlong scalar case with R>3. -/
theorem third_S_q_three_choices (U v T R : Int)
    (hU : 1≤U) (hv : 1≤v) (hR : 1≤R)
    (hm : T+U=R+3+v) (hs : (3+v)^2=R^2+2*U*v) :
    3+R≤v ∨ (R≤3 ∧ 4≤U) ∨ (R=5 ∧ U=3 ∧ v=4 ∧ T=9) := by
  by_cases h6 : 6≤U
  · have hp:=Int.mul_nonneg (show 0≤U-6 by omega) (show 0≤v by omega)
    by_cases hV : 3≤v
    · have hb : R^2≤(v-3)^2 := by grind only
      exact Or.inl (by have hh:=le_of_square_le R (v-3) (by omega) (by omega) hb; omega)
    · have hb : R^2≤(3-v)^2 := by grind only
      exact Or.inr (Or.inl ⟨by have hh:=le_of_square_le R (3-v) (by omega) (by omega) hb; omega,by omega⟩)
  · let x:=v+3-U
    let c:=9-(U-3)^2
    let y:=if 0≤x then x else -x
    have hy : 0≤y := by dsimp [y]; split <;> omega
    have hy' : y=x ∨ y= -x := by dsimp [y]; split <;> simp
    have hxy : x^2=y^2 := by rcases hy' with he|he <;> rw [he] <;> grind only
    have hs' : R^2=y^2+c := by
      have hh : R^2=x^2+c := by dsimp [x,c]; grind only
      rwa [hxy] at hh
    have hc : c=5 ∨ c=8 ∨ c=9 := by
      rcases (show U=1 ∨ U=2 ∨ U=3 ∨ U=4 ∨ U=5 by omega) with h1|h2|h3|h4|h5 <;>
        subst U <;> decide
    rcases square_gap_three_constants y R c hy hR hc hs' with hR3|⟨hc9,hR5,hy4⟩
    · have h4 : 4≤U := by
        by_cases hle : 4≤U
        · exact hle
        · rcases (show U=1 ∨ U=2 ∨ U=3 by omega) with h1|h2|h3
          · have hb:=square_lower x 3 (by decide) (by dsimp [x]; omega)
            have hc5 : c=5 := by dsimp [c]; rw [h1]; decide
            grind only
          · have hb:=square_lower x 2 (by decide) (by dsimp [x]; omega)
            have hc8 : c=8 := by dsimp [c]; rw [h2]; decide
            grind only
          · have hb:=square_lower x 1 (by decide) (by dsimp [x]; omega)
            have hc9 : c=9 := by dsimp [c]; rw [h3]; decide
            grind only
      exact Or.inr (Or.inl ⟨by omega,h4⟩)
    · have hd : (U-3)^2=0 := by dsimp [c] at hc9; omega
      have hU3 : U=3 := by
        have hp : (U-3)*(U-3)=0 := by grind only
        rcases Int.mul_eq_zero.mp hp with hh|hh <;> omega
      dsimp [x] at hy'
      exact Or.inr (Or.inr ⟨hR5,hU3,by omega,by omega⟩)

end Recaman.ThirdSQThreeFactors
