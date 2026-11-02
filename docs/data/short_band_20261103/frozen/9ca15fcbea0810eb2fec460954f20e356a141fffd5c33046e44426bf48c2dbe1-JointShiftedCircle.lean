import Recaman.ShortCounterFactorBounds

namespace Recaman.JointShiftedCircle

open Recaman.ShortCounterFactorBounds

/-- Arithmetic support: two actual run budgets supply the cross lower
bounds. This lemma is not independently registered as a research result. -/
theorem shifted_bounds (S C v R K : Int) (hC : 0≤C) (hSC : 2*C<S)
    (hhead : S≤R+9) (hfour : S+v≤C+13) (hthree : v+2≤C → S+v≤C+12)
    (hKfour : S+v-C-7≤K) (hKthree : v+2≤C → S+v-C-6≤K)
    (hcircle : R^2+C^2+2*C*v-v^2-1+2*K≤(S-C)^2) :
    (C=v+1 → R^2+C^2+28*C≤186) ∧
    (v+2≤C → R^2+(C-v)^2+4*(C-v)*v+v^2+24*v≤133) ∧
    (v+2≤C → 16*C+2*C*v-v^2+2*v-76≤2*R*(8-C)) := by
  let Y:=S-C-1
  have hY : 0≤Y := by dsimp [Y]; omega
  have hshift4 : R^2+C^2+2*C*v-v^2+2*v-14≤Y^2 := by
    have he : R^2+C^2+2*C*v-v^2+2*v-14-Y^2 =
        (R^2+C^2+2*C*v-v^2-1+2*K-(S-C)^2)-2*(K-(S+v-C-7)) := by
      dsimp [Y]
      grind only
    omega
  have hshift3 (hd : v+2≤C) : R^2+C^2+2*C*v-v^2+2*v-12≤Y^2 := by
    have hk:=hKthree hd
    have he : R^2+C^2+2*C*v-v^2+2*v-12-Y^2 =
        (R^2+C^2+2*C*v-v^2-1+2*K-(S-C)^2)-2*(K-(S+v-C-6)) := by
      dsimp [Y]
      grind only
    omega
  refine ⟨?_,?_,?_⟩
  · intro hc
    have hs : Y≤13-C := by dsimp [Y]; omega
    have hsq:=square_lower (13-C) Y hY hs
    have hf : R^2+C^2+2*C*v-v^2+2*v-14=R^2+2*C^2+2*C-17 := by rw [hc]; grind only
    have he : (13-C)^2=169-26*C+C^2 := by grind only
    omega
  · intro hd
    have hs : Y≤11-v := by have hx:=hthree hd; dsimp [Y]; omega
    have hsq:=square_lower (11-v) Y hY hs
    have hp:=hshift3 hd
    have he : (11-v)^2=121-22*v+v^2 := by grind only
    have hf : R^2+(C-v)^2+4*(C-v)*v+v^2+24*v =
        R^2+C^2+2*C*v-v^2+2*v-12-(121-22*v+v^2)+133 := by grind only
    omega
  · intro hd
    have hs : Y≤R+8-C := by dsimp [Y]; omega
    have hsq:=square_lower (R+8-C) Y hY hs
    have hp:=hshift3 hd
    have he : (R+8-C)^2-(R^2+C^2+2*C*v-v^2+2*v-12)=
        2*R*(8-C)-(16*C+2*C*v-v^2+2*v-76) := by grind only
    omega

private theorem deep_v_two (C v R : Int) (hv : 1≤v) (hd : v+2≤C) (hR : 5≤R)
    (hQ : R^2+(C-v)^2+4*(C-v)*v+v^2+24*v≤133) : v≤2 := by
  by_cases hh : v≤2
  · exact hh
  have hR25:=square_lower R 5 (by omega) hR
  have hD4:=square_lower (C-v) 2 (by omega) (by omega)
  have hv9:=square_lower v 3 (by omega) (by omega)
  have hp:=Int.mul_nonneg (show 0≤C-v-2 by omega) (show 0≤v by omega)
  have he : (C-v-2)*v=(C-v)*v-2*v := by grind only
  omega

/-- Small parameter cuts consume the new shifted inequalities. -/
theorem parameter_cuts (C v R : Int) (hC : 4≤C) (hC8 : C≤8)
    (hv : 1≤v) (hvC : v<C) (hR : 5≤R) (hR9 : R≤9)
    (hclose : C=v+1 → R^2+C^2+28*C≤186)
    (hdeep : v+2≤C → R^2+(C-v)^2+4*(C-v)*v+v^2+24*v≤133)
    (hlinear : v+2≤C → 16*C+2*C*v-v^2+2*v-76≤2*R*(8-C)) :
    C≤5 ∧ v≤3 ∧ (C=v+1 → C=4 ∧ v=3 ∧ R≤7) ∧ (v+2≤C → v≤2) := by
  have hR25:=square_lower R 5 (by omega) hR
  by_cases hc : C=v+1
  · have hq:=hclose hc
    have hC4 : C=4 := by
      by_cases hh : C=4
      · exact hh
      have hC25:=square_lower C 5 (by omega) (by omega)
      omega
    have hv3 : v=3 := by omega
    have hR7 : R≤7 := by
      by_cases hh : R≤7
      · exact hh
      have hR64:=square_lower R 8 (by omega) (by omega)
      rw [hC4] at hq
      omega
    exact ⟨by omega,by omega,fun _=>⟨hC4,hv3,hR7⟩,by intro hd; omega⟩
  · have hd : v+2≤C := by omega
    have hq:=hdeep hd
    have hl:=hlinear hd
    have hv2:=deep_v_two C v R hv hd hR hq
    have hC5 : C≤5 := by
      by_cases hh : C≤5
      · exact hh
      have hcCases : C=6 ∨ C=7 ∨ C=8 := by omega
      have hvCases : v=1 ∨ v=2 := by omega
      rcases hcCases with rfl|rfl|rfl <;> rcases hvCases with rfl|rfl
      all_goals try omega
      have hR81:=square_lower R 9 (by omega) (by omega)
      omega
    exact ⟨hC5,by omega,by intro hh; omega,fun _=>hv2⟩

end Recaman.JointShiftedCircle
