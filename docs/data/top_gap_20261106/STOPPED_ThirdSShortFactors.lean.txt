import Recaman.ShortCounterFactorBounds

namespace Recaman.ThirdSShortFactors

open Recaman.ShortCounterFactorBounds

private theorem le_of_square_le (x y : Int) (hx : 0≤x) (hy : 0≤y) (h : x^2≤y^2) : x≤y := by
  by_cases he : x≤y
  · exact he
  · have hp:=Int.mul_pos (show 0<x-y by omega) (show 0<x+y by omega)
    grind only

/-- A positive square difference at most nine has a difference
factor in 1..3. Only the listed forms can have R>=3. -/
private theorem small_square_gap (x R c : Int) (hx : 0≤x) (hR : 1≤R)
    (hc : 1≤c ∧ c≤9) (h : R^2=x^2+c) :
    R≤2 ∨ (c=5 ∧ R=3 ∧ x=2) ∨ (c=7 ∧ R=4 ∧ x=3) ∨
      (c=8 ∧ R=3 ∧ x=1) ∨ (c=9 ∧ R=3 ∧ x=0) ∨ (c=9 ∧ R=5 ∧ x=4) := by
  have hlt : x<R := by
    by_cases he : x<R
    · exact he
    · have hh:=square_lower x R (by omega) (by omega)
      omega
  let d:=R-x
  have hfac : d*(R+x)=c := by dsimp [d]; grind only
  have hd : d≤3 := by
    by_cases he : d≤3
    · exact he
    · have hd4 : 4≤d := by omega
      have hs4 : 4≤R+x := by dsimp [d] at hd4; omega
      have hp:=Int.mul_nonneg (show 0≤d-4 by omega) (show 0≤R+x-4 by omega)
      have hge : 16≤d*(R+x) := by grind only
      omega
  rcases (show d=1 ∨ d=2 ∨ d=3 by dsimp [d] at *; omega) with h1|h2|h3
  · rw [h1,Int.one_mul] at hfac
    dsimp [d] at h1
    omega
  · rw [h2] at hfac
    dsimp [d] at h2
    omega
  · rw [h3] at hfac
    dsimp [d] at h3
    omega

private theorem abs_from_square (x y : Int) (hy : 0≤y) (h : x^2=y^2) : x=y ∨ x= -y := by
  have hp : (x-y)*(x+y)=0 := by grind only
  rcases Int.mul_eq_zero.mp hp with he|he <;> omega

theorem short_third_S_target_choices (q U v T R : Int)
    (hq : 1≤q) (hq3 : q≤3) (hU : 1≤U) (hv : 1≤v) (hR : 1≤R)
    (hm : T+U=R+q+v) (hs : (q+v)^2=R^2+2*U*v) :
    q+R≤v ∨ R≤2 ∨ (R=3 ∧ 4≤U) ∨ (q=3 ∧ R=5 ∧ U=3 ∧ v=4 ∧ T=9) := by
  by_cases hUlarge : 2*q≤U
  · have hp:=Int.mul_nonneg (show 0≤U-2*q by omega) (show 0≤v by omega)
    by_cases hV : q≤v
    · have hs' : R^2≤(v-q)^2 := by grind only
      exact Or.inl (by have h:=le_of_square_le R (v-q) (by omega) (by omega) hs'; omega)
    · have hs' : R^2≤(q-v)^2 := by grind only
      exact Or.inr (Or.inl (by have h:=le_of_square_le R (q-v) (by omega) (by omega) hs'; omega))
  · let x:=v+q-U
    let c:=q^2-(U-q)^2
    let y:=if 0≤x then x else -x
    have hy : 0≤y := by dsimp [y]; split <;> omega
    have hy' : y=x ∨ y= -x := by dsimp [y]; split <;> simp
    have hxy : x^2=y^2 := by rcases hy' with he|he <;> rw [he] <;> grind only
    have hs' : R^2=y^2+c := by
      have hh : R^2=x^2+c := by dsimp [x,c]; grind only
      rwa [hxy] at hh
    have hc : 1≤c ∧ c≤9 := by
      have hq2:=square_lower 3 q (by omega) hq3
      have hd:=Int.sq_nonneg (U-q)
      have hp:=Int.mul_pos (show 0<U by omega) (show 0<2*q-U by omega)
      dsimp [c]
      grind only
    have hcases:=small_square_gap y R c hy hR hc hs'
    rcases hcases with hsmall|h5|h7|h8|h93|h95
    · exact Or.inr (Or.inl hsmall)
    all_goals
      have hqeq : q=3 := by
        by_cases hh : q≤2
        · have hq2:=square_lower 2 q (by omega) hh
          have hd:=Int.sq_nonneg (U-q)
          have hcl : 5≤c := by omega
          dsimp [c] at hcl
          grind only
        · omega
      have hd : (U-3)^2=9-c := by dsimp [c]; rw [hqeq]; grind only
      dsimp [x] at hy'
    · obtain ⟨hc5,hR3,hy2⟩:=h5
      rw [hc5] at hd
      have he := abs_from_square (U-3) 2 (by decide) (by simpa using hd)
      omega
    · obtain ⟨hc7,_,_⟩:=h7
      rw [hc7] at hd
      have he : 2≤U-3 ∨ U-3≤ -2 := by
        by_cases hg : 2≤U-3
        · exact Or.inl hg
        · by_cases hl : U-3≤ -2
          · exact Or.inr hl
          · have hu : U=2 ∨ U=3 ∨ U=4 := by omega
            rcases hu with h2|h3|h4
            · rw [h2] at hd; contradiction
            · rw [h3] at hd; contradiction
            · rw [h4] at hd; contradiction
      rcases he with he|he
      · have hq2:=square_lower (U-3) 2 (by decide) he
        grind only
      · have hq2:=square_lower (3-U) 2 (by decide) (by omega)
        grind only
    · obtain ⟨hc8,hR3,hy1⟩:=h8
      rw [hc8] at hd
      have he := abs_from_square (U-3) 1 (by decide) (by simpa using hd)
      omega
    · obtain ⟨hc9,_,hy0⟩:=h93
      rw [hc9] at hd
      have he := abs_from_square (U-3) 0 (by decide) (by simpa using hd)
      omega
    · obtain ⟨hc9,hR5,hy4⟩:=h95
      rw [hc9] at hd
      have he := abs_from_square (U-3) 0 (by decide) (by simpa using hd)
      omega

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

theorem third_S_unit_U_small_gap_impossible (q v R : Int) (hq : 1≤q) (hv : 1≤v)
    (hR : 1≤R) (hR2 : R≤2) (hs : (q+v)^2=R^2+2*v) : False := by
  have hp:=square_lower (q+v) (v+1) (by omega) (by omega)
  have hr:=square_lower 2 R (by omega) hR2
  have hv1 : v=1 := by
    by_cases he : 2≤v
    · have hx:=square_lower v 2 (by decide) he
      grind only
    · omega
  rw [hv1] at hs
  rcases (show R=1 ∨ R=2 by omega) with hr1|hr2
  · rw [hr1] at hs
    have hx:=square_lower (q+1) 2 (by decide) (by omega)
    grind only
  · rw [hr2] at hs
    by_cases hq1 : q=1
    · rw [hq1] at hs
      contradiction
    · have hx:=square_lower (q+1) 3 (by decide) (by omega)
      grind only

end Recaman.ThirdSShortFactors
