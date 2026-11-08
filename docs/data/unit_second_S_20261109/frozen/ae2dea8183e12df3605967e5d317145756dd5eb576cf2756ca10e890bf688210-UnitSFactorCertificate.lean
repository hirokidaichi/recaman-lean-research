import Recaman.SecondASmallSquare

namespace Recaman.UnitSFactorCertificate

/-- Three nonnegative summands give a small complete certificate at
D=R+1. All products are explicit rather than opaque square atoms. -/
theorem same_step_factors (L U D v : Int) (hL : 1≤L) (hD : 1≤D)
    (hU : D≤U) (hv : 1≤v)
    (he : L*L-2*L+2*U*v=2*D-1) : L=1 ∧ U=D ∧ v=1 := by
  have h1:=Int.mul_nonneg (show 0≤L-1 by omega) (show 0≤L-1 by omega)
  have h2:=Int.mul_nonneg (show 0≤2*(U-D) by omega) (show 0≤v by omega)
  have h3:=Int.mul_nonneg (show 0≤2*D by omega) (show 0≤v-1 by omega)
  have hc : (L-1)*(L-1)+2*(U-D)*v+2*D*(v-1)=0 := by grind only
  have hz1 : (L-1)*(L-1)=0 := by omega
  have hz2 : 2*(U-D)*v=0 := by omega
  have hz3 : (2*D)*(v-1)=0 := by omega
  have hL1 : L=1 := by
    rcases Int.mul_eq_zero.mp hz1 with he|he <;> omega
  have hv1 : v=1 := by
    rcases Int.mul_eq_zero.mp hz3 with he|he <;> omega
  rw [hv1] at hz2
  exact ⟨hL1,by omega,hv1⟩

/-- After the actual source/head pruning only the unit-L boundary can
satisfy the same-target square. The actual last-four budget pays it. -/
theorem unit_S_square_choices (D R L U v : Int)
    (hD : 6≤D) (hD7 : D≤7) (hR : 5≤R) (hRD : R<D)
    (hL : 1≤L) (hv : 1≤v) (hU : D≤U) (hUR : U≤R+2)
    (hsq : D^2=R^2+L^2-2*L+2*U*v) :
    L=1 ∧ U=D ∧ v=1 ∧ D=R+1 := by
  by_cases hstep : D=R+1
  · have hd2 : D^2=D*D := by grind only
    have hr2 : R^2=R*R := by grind only
    have hl2 : L^2=L*L := by grind only
    rw [hd2,hr2,hl2] at hsq
    have he : L*L-2*L+2*U*v=2*D-1 := by grind only
    obtain ⟨hL1,hUD,hv1⟩:=same_step_factors L U D v hL (by omega) hU hv he
    exact ⟨hL1,hUD,hv1,hstep⟩
  · have hd : D=7 := by omega
    have hr : R=5 := by omega
    have hu : U=7 := by omega
    rw [hd,hr,hu] at hsq
    have hL0 : 0≤L-1 := by omega
    have hsq0:=Int.mul_nonneg hL0 hL0
    have hl2 : L^2=L*L := by grind only
    rw [hl2] at hsq
    have hv1 : v=1 := by
      by_cases he : v=1
      · exact he
      · have hh : 2≤v := by omega
        grind only
    rw [hv1] at hsq
    have hh : (L-1)*(L-1)=11 := by grind only
    by_cases hL4 : L≤4
    · have hp:=Int.mul_nonneg (show 0≤4-L by omega) (show 0≤L+2 by omega)
      grind only
    · have hp:=Int.mul_nonneg (show 0≤L-5 by omega) (show 0≤L+3 by omega)
      grind only

end Recaman.UnitSFactorCertificate
