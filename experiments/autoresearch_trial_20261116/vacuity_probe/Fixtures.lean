import VacuityProbe

/-!
Fixtures for the vacuity probe: known-bad shapes (each named after the
2026-09-15 audit category it imitates) and a few genuine library theorems.
None of the fixtures is a research claim.
-/

namespace VacuityFixtures

open Recaman.LineCapacityPeriodic

/-- C (conclusion as hypothesis), the E-271 `hdist` shape. -/
theorem bad_concl_hyp (e : Int → Bool) (p : Nat) (t : Int)
    (h : suppliedPhases e t p ≤ subtractionPhases e t p) :
    suppliedPhases e t p ≤ subtractionPhases e t p := h

/-- T (free-Nat tautology with contradictory hypotheses), the E-244 shape. -/
theorem bad_free_nat (k : Nat) (hk : k ≤ 5) (hcov : 7 ≤ k) : False := by omega

/-- Verbatim statement of the deleted E-319 `grand_capacity_inequality`
(proof re-done by omega because its helper module was deleted). -/
theorem bad_grand_capacity_inequality (card_U card_D k card_B card_N : Nat)
    (h_hall : card_B ≤ card_N)
    (h_slack : card_B + 1 ≤ card_N → card_B ≤ card_N - 1)
    (hkU : k ≤ card_U)
    (hkD : k ≤ card_D)
    (h_rem : card_U - k ≤ card_D - k) :
    (card_B ≤ card_N ∧ (card_B + 1 ≤ card_N → card_B ≤ card_N - 1)) ∧
    (card_U ≤ card_D) := by
  exact ⟨⟨h_hall, h_slack⟩, by omega⟩

/-- An unproved defined hypothesis that the proof never uses. -/
theorem bad_unused_hyp (e : Int → Bool) (p : Nat) (hH : LineCapacity e) (h0 : 0 < p) :
    p ≠ 0 := by omega

/-- Contradictory hypotheses about a real sign word: the conclusion is free. -/
theorem bad_contradictory (e : Int → Bool) (b : Int) (h1 : e b = true) (h2 : e b = false) :
    LineCapacity e := by simp_all

end VacuityFixtures

#vacuity_probe VacuityFixtures.bad_concl_hyp VacuityFixtures.bad_free_nat
  VacuityFixtures.bad_grand_capacity_inequality VacuityFixtures.bad_unused_hyp
  VacuityFixtures.bad_contradictory
  Recaman.LineCapacityPeriodic.periodic_capacity_of_line
