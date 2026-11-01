import Recaman.PermanentAboveCorridorReplayFloorThree
import Recaman.PermanentAboveCorridorNineteenBoundary

namespace Recaman

noncomputable section

/-! # Complete numeric identification of a nineteen replay

For the exceptional target nineteen the replay blocker collapses the clock
band from both sides: the crossing value sits below nineteen, and the
blocker forces the clock strictly below the value, so the clock is at most
sixteen.  The kernel eliminations of the second floor then leave exactly
two clocks, six and eight.  Each pins every numeric component of the
replay: the anchor, the blocker defect, and — by uniqueness of first
occurrences — the blocker's first time.

A hypothetical counterexample at nineteen therefore replays one of two
fully explicit cycles: crossing clock six with anchor thirteen and blocker
six first seen at time three, or crossing clock eight with anchor twelve
and blocker three first seen at time two.
-/

/-- First occurrences are unique. -/
theorem FirstAt.unique {seq : Nat → Nat} {x t₁ t₂ : Nat}
    (h₁ : FirstAt seq x t₁) (h₂ : FirstAt seq x t₂) : t₁ = t₂ := by
  by_cases hlt : t₁ < t₂
  · exact False.elim (h₂.2 t₁ hlt h₁.1)
  · by_cases hgt : t₂ < t₁
    · exact False.elim (h₁.2 t₂ hgt h₂.1)
    · omega

namespace TerminalExactDischargeReplayCertificate

variable {target start : Nat} {parent : PhaseSearchNode}
variable {source : PermanentTailDischargeReturnCertificate target start parent}

/-- At target nineteen the replay clock is six or eight: the blocker bound
caps the clock below the sub-nineteen crossing value, and the second-floor
eliminations kill everything else. -/
theorem crossingTime_eq_six_or_eight_of_nineteen
    (r : TerminalExactDischargeReplayCertificate source)
    (h19 : target = 19) :
    r.crossingTime = 6 ∨ r.crossingTime = 8 := by
  have hsix := r.six_le_crossingTime
  have hclock := r.clock_lt_crossingValue
  have hbelow : a r.crossingTime < 19 := by
    have hstraddle := r.crossing_straddles_target.1
    omega
  have hcap : r.crossingTime ≤ 16 := by omega
  have hforced := r.forced_addition_at_crossing
  have hcases : r.crossingTime = 6 ∨ r.crossingTime = 7 ∨
      r.crossingTime = 8 ∨ r.crossingTime = 9 ∨ r.crossingTime = 10 ∨
      r.crossingTime = 11 ∨ r.crossingTime = 12 ∨ r.crossingTime = 13 ∨
      r.crossingTime = 14 ∨ r.crossingTime = 15 ∨
      r.crossingTime = 16 := by omega
  rcases hcases with heq | heq | heq | heq | heq | heq | heq | heq |
    heq | heq | heq
  · exact Or.inl heq
  · exact absurd heq r.crossingTime_ne_seven
  · exact Or.inr heq
  · rw [heq] at hforced
    exact absurd hforced (by decide)
  · rw [heq] at hclock
    exact absurd hclock (by decide)
  · rw [heq] at hforced
    exact absurd hforced (by decide)
  · rw [heq] at hclock
    exact absurd hclock (by decide)
  · rw [heq] at hforced
    exact absurd hforced (by decide)
  · rw [heq] at hclock
    exact absurd hclock (by decide)
  · rw [heq] at hforced
    exact absurd hforced (by decide)
  · rw [heq] at hclock
    exact absurd hclock (by decide)

/-- The clock-six nineteen replay is fully explicit: anchor thirteen,
blocker defect six, blocker first time three. -/
theorem six_replay_pins
    (r : TerminalExactDischargeReplayCertificate source)
    (hsix : r.crossingTime = 6) :
    parent.anchorParent = 13 ∧ r.candidate = 6 ∧ r.firstTime = 3 := by
  have hanchor := r.anchor_eq
  rw [hsix] at hanchor
  have hvalue : a 6 = 13 := by decide
  have hcandidate := r.candidate_eq_at_crossing
  rw [hsix] at hcandidate
  have hcand : r.candidate = 6 := by omega
  have hfirst := r.historical.blocker.candidate_first
  rw [hcand] at hfirst
  have hknown : FirstAt a 6 3 := by
    constructor
    · decide
    · intro u hu
      have hcases : u = 0 ∨ u = 1 ∨ u = 2 := by omega
      rcases hcases with rfl | rfl | rfl <;> decide
  exact ⟨by omega, hcand, hfirst.unique hknown⟩

/-- The clock-eight nineteen replay is fully explicit: anchor twelve,
blocker defect three, blocker first time two. -/
theorem eight_replay_pins
    (r : TerminalExactDischargeReplayCertificate source)
    (height : r.crossingTime = 8) :
    parent.anchorParent = 12 ∧ r.candidate = 3 ∧ r.firstTime = 2 := by
  have hanchor := r.anchor_eq
  rw [height] at hanchor
  have hvalue : a 8 = 12 := by decide
  have hcandidate := r.candidate_eq_at_crossing
  rw [height] at hcandidate
  have hcand : r.candidate = 3 := by omega
  have hfirst := r.historical.blocker.candidate_first
  rw [hcand] at hfirst
  have hknown : FirstAt a 3 2 := by
    constructor
    · decide
    · intro u hu
      have hcases : u = 0 ∨ u = 1 := by omega
      rcases hcases with rfl | rfl <;> decide
  exact ⟨by omega, hcand, hfirst.unique hknown⟩

end TerminalExactDischargeReplayCertificate

end

end Recaman
