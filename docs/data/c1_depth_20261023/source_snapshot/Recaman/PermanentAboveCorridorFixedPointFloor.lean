import Recaman.PermanentAboveCorridorFixedPointCore

namespace Recaman

noncomputable section

/-! # Kernel floor of the unified fixed-point core

The replay floor used the terminal blocker, which only the discharge side
carries.  The unified core needs no blocker: its straddle and forced
addition are already orbit events, so small crossing clocks die by direct
kernel computation.  Clock three subtracts in the real orbit; every other
clock up to five straddles only targets that actually occur by time 131.

Hence both fixed points — the discharge replay and the landing cycle —
share the same floor: crossing clock at least six, proved from the core and
the missing-target field alone, together with the triangular envelope
`target ≤ upperTri (clock + 1)`.
-/

namespace TailFixedPointCore

/-- Small clocks are impossible for any missing-target fixed-point core. -/
theorem six_le_crossingTime
    {target : Nat} {parent : PhaseSearchNode} {crossingTime : Nat}
    (core : TailFixedPointCore target parent crossingTime)
    (missing : ¬ ∃ time, a time = target) :
    6 ≤ crossingTime := by
  by_cases hsix : 6 ≤ crossingTime
  · exact hsix
  · have hcases : crossingTime = 0 ∨ crossingTime = 1 ∨ crossingTime = 2 ∨
        crossingTime = 3 ∨ crossingTime = 4 ∨ crossingTime = 5 := by omega
    have hbelow := core.below
    have hendpoint := core.endpoint_ge
    have hforced := core.forced
    rcases hcases with heq | heq | heq | heq | heq | heq
    · rw [heq] at hbelow hendpoint
      have hzero : a 0 = 0 := by decide
      have hone : a (0 + 1) = 1 := by decide
      have htarget : target = 1 := by omega
      subst htarget
      exact absurd ⟨1, by decide⟩ missing
    · rw [heq] at hbelow hendpoint
      have hone : a 1 = 1 := by decide
      have htwo : a (1 + 1) = 3 := by decide
      have htarget : target = 2 ∨ target = 3 := by omega
      rcases htarget with rfl | rfl
      · exact absurd ⟨4, by decide⟩ missing
      · exact absurd ⟨2, by decide⟩ missing
    · rw [heq] at hbelow hendpoint
      have htwo : a 2 = 3 := by decide
      have hthree : a (2 + 1) = 6 := by decide
      have htarget : target = 4 ∨ target = 5 ∨ target = 6 := by omega
      rcases htarget with rfl | rfl | rfl
      · exact absurd ⟨131, by
          set_option maxRecDepth 100000 in decide⟩ missing
      · exact absurd ⟨129, by
          set_option maxRecDepth 100000 in decide⟩ missing
      · exact absurd ⟨3, by decide⟩ missing
    · rw [heq] at hforced
      exact absurd hforced (by decide)
    · rw [heq] at hbelow hendpoint
      have hfour : a 4 = 2 := by decide
      have hfive : a (4 + 1) = 7 := by decide
      have htarget : target = 3 ∨ target = 4 ∨ target = 5 ∨ target = 6 ∨
          target = 7 := by omega
      rcases htarget with rfl | rfl | rfl | rfl | rfl
      · exact absurd ⟨2, by decide⟩ missing
      · exact absurd ⟨131, by
          set_option maxRecDepth 100000 in decide⟩ missing
      · exact absurd ⟨129, by
          set_option maxRecDepth 100000 in decide⟩ missing
      · exact absurd ⟨3, by decide⟩ missing
      · exact absurd ⟨5, by decide⟩ missing
    · rw [heq] at hbelow hendpoint
      have hfive : a 5 = 7 := by decide
      have hsix' : a (5 + 1) = 13 := by decide
      have htarget : target = 8 ∨ target = 9 ∨ target = 10 ∨
          target = 11 ∨ target = 12 ∨ target = 13 := by omega
      rcases htarget with rfl | rfl | rfl | rfl | rfl | rfl
      · exact absurd ⟨16, by decide⟩ missing
      · exact absurd ⟨14, by decide⟩ missing
      · exact absurd ⟨12, by decide⟩ missing
      · exact absurd ⟨10, by decide⟩ missing
      · exact absurd ⟨8, by decide⟩ missing
      · exact absurd ⟨6, by decide⟩ missing

/-- Triangular envelope for any fixed-point core. -/
theorem target_le_upperTri
    {target : Nat} {parent : PhaseSearchNode} {crossingTime : Nat}
    (core : TailFixedPointCore target parent crossingTime) :
    target ≤ upperTri (crossingTime + 1) :=
  Nat.le_trans core.endpoint_ge (a_le_upperTri _)

end TailFixedPointCore

end

end Recaman
