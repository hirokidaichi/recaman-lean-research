import Recaman.LineCapacityPeriodic

/-!
# Regression fixtures for the vacuity lint (not research claims)

Each theorem imitates a shape from the 2026-09-15 audit
(docs/AUDIT_GRAND_SYNTHESIS_2026-09-15.md); the lint must flag all of them.
-/

namespace VacuityFixtures

open Recaman.LineCapacityPeriodic

/-- C: the conclusion is a hypothesis (the E-271 `hdist` shape). -/
theorem bad_concl_hyp (e : Int → Bool) (p : Nat) (t : Int)
    (h : suppliedPhases e t p ≤ subtractionPhases e t p) :
    suppliedPhases e t p ≤ subtractionPhases e t p := h

/-- T: contradictory hypotheses over free naturals (the E-244 shape). -/
theorem bad_free_nat (k : Nat) (hk : k ≤ 5) (hcov : 7 ≤ k) : False := by omega

/-- The signature of the deleted E-319 `grand_capacity_inequality`, re-proved by omega. -/
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

/-- Contradictory hypotheses about a real sign word. -/
theorem bad_contradictory (e : Int → Bool) (b : Int) (h1 : e b = true) (h2 : e b = false) :
    LineCapacity e := by simp_all

end VacuityFixtures
