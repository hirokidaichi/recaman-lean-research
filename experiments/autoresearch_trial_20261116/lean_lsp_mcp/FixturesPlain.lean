import Recaman.LineCapacityPeriodic

/-! The vacuity fixtures of `../vacuity_probe/Fixtures.lean`, without the probe
import, so that the language server can open them directly. Not research claims. -/

namespace VacuityFixturesPlain

open Recaman.LineCapacityPeriodic

theorem bad_concl_hyp (e : Int → Bool) (p : Nat) (t : Int)
    (h : suppliedPhases e t p ≤ subtractionPhases e t p) :
    suppliedPhases e t p ≤ subtractionPhases e t p := h

theorem bad_free_nat (k : Nat) (hk : k ≤ 5) (hcov : 7 ≤ k) : False := by omega

theorem bad_grand_capacity_inequality (card_U card_D k card_B card_N : Nat)
    (h_hall : card_B ≤ card_N)
    (h_slack : card_B + 1 ≤ card_N → card_B ≤ card_N - 1)
    (hkU : k ≤ card_U)
    (hkD : k ≤ card_D)
    (h_rem : card_U - k ≤ card_D - k) :
    (card_B ≤ card_N ∧ (card_B + 1 ≤ card_N → card_B ≤ card_N - 1)) ∧
    (card_U ≤ card_D) := by
  exact ⟨⟨h_hall, h_slack⟩, by omega⟩

theorem bad_unused_hyp (e : Int → Bool) (p : Nat) (hH : LineCapacity e) (h0 : 0 < p) :
    p ≠ 0 := by omega

theorem bad_contradictory (e : Int → Bool) (b : Int) (h1 : e b = true) (h2 : e b = false) :
    LineCapacity e := by simp_all

end VacuityFixturesPlain
