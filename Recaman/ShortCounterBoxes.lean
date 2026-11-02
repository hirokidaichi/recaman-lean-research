import Recaman.ShortCounterFactorBounds

namespace Recaman.ShortCounterBoxes

open Recaman.ShortCounterFactorBounds

private theorem deep_one (C R : Int) (hC : 4≤C) (hR : 5≤R)
    (hq : R^2+(C-1)^2+4*(C-1)+25≤145) : C≤8 ∧ R≤9 := by
  have hR25:=square_lower R 5 (by omega) hR
  have hD9:=square_lower (C-1) 3 (by omega) (by omega)
  constructor
  · by_cases hh : C≤8
    · exact hh
    have hD64:=square_lower (C-1) 8 (by omega) (by omega)
    omega
  · by_cases hh : R≤9
    · exact hh
    have hR100:=square_lower R 10 (by omega) (by omega)
    omega

private theorem deep_two (C R : Int) (hC : 4≤C) (hR : 5≤R)
    (hq : R^2+(C-2)^2+8*(C-2)+52≤145) : C≤7 ∧ R≤8 := by
  have hR25:=square_lower R 5 (by omega) hR
  have hD4:=square_lower (C-2) 2 (by omega) (by omega)
  constructor
  · by_cases hh : C≤7
    · exact hh
    have hD36:=square_lower (C-2) 6 (by omega) (by omega)
    omega
  · by_cases hh : R≤8
    · exact hh
    have hR81:=square_lower R 9 (by omega) (by omega)
    omega

private theorem deep_three (C R : Int) (hC : 5≤C) (hR : 5≤R)
    (hq : R^2+(C-3)^2+12*(C-3)+81≤145) : C=5 ∧ R≤6 := by
  have hR25:=square_lower R 5 (by omega) hR
  have hD4:=square_lower (C-3) 2 (by omega) (by omega)
  constructor
  · by_cases hh : C=5
    · exact hh
    have hD9:=square_lower (C-3) 3 (by omega) (by omega)
    omega
  · by_cases hh : R≤6
    · exact hh
    have hR49:=square_lower R 7 (by omega) (by omega)
    omega

/-- Five explicit boxes consume the strict cuts before case analysis.
They assert containment, not existence or absence of actual histories. -/
theorem five_boxes (C v R : Int) (hC : 4≤C) (hv : 1≤v) (hvC : v<C) (hR : 5≤R)
    (hclose : C=v+1 → C≤5) (hdeep : v+2≤C → v≤3)
    (hcloseQ : C=v+1 → R^2+C^2+28*C≤198)
    (hdeepQ : v+2≤C → R^2+(C-v)^2+4*(C-v)*v+v^2+24*v≤145) :
    (v=3 ∧ C=4 ∧ 5≤R ∧ R≤8) ∨ (v=4 ∧ C=5 ∧ R=5) ∨
    (v=1 ∧ 4≤C ∧ C≤8 ∧ 5≤R ∧ R≤9) ∨
    (v=2 ∧ 4≤C ∧ C≤7 ∧ 5≤R ∧ R≤8) ∨
    (v=3 ∧ C=5 ∧ 5≤R ∧ R≤6) := by
  by_cases hc : C=v+1
  · have hC5:=hclose hc
    have hq:=hcloseQ hc
    have hcases : C=4 ∨ C=5 := by omega
    rcases hcases with h4|h5
    · have hR8 : R≤8 := by
        by_cases hh : R≤8
        · exact hh
        have hR81:=square_lower R 9 (by omega) (by omega)
        rw [h4] at hq
        omega
      exact Or.inl ⟨by omega,h4,hR,hR8⟩
    · have hR5 : R=5 := by
        by_cases hh : R=5
        · exact hh
        have hR36:=square_lower R 6 (by omega) (by omega)
        rw [h5] at hq
        omega
      exact Or.inr (Or.inl ⟨by omega,h5,hR5⟩)
  · have hd : v+2≤C := by omega
    have hv3:=hdeep hd
    have hq:=hdeepQ hd
    have hcases : v=1 ∨ v=2 ∨ v=3 := by omega
    rcases hcases with h1|h2|h3
    · have hq1 : R^2+(C-1)^2+4*(C-1)+25≤145 := by rw [h1] at hq; grind only
      have hb:=deep_one C R hC hR hq1
      exact Or.inr (Or.inr (Or.inl ⟨h1,hC,hb.1,hR,hb.2⟩))
    · have hq2 : R^2+(C-2)^2+8*(C-2)+52≤145 := by rw [h2] at hq; grind only
      have hb:=deep_two C R hC hR hq2
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h2,hC,hb.1,hR,hb.2⟩)))
    · have hq3 : R^2+(C-3)^2+12*(C-3)+81≤145 := by rw [h3] at hq; grind only
      have hb:=deep_three C R (by omega) hR hq3
      exact Or.inr (Or.inr (Or.inr (Or.inr ⟨h3,hb.1,hR,hb.2⟩)))

end Recaman.ShortCounterBoxes
