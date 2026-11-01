import Recaman.EventualHighCorridorRecurrence
import Recaman.NoDoubleAdditionRun
import Recaman.DivergentCandidateMissing

namespace Recaman

/-! # The forced-addition burst at a recurring use clock

A rigid recurrence event already forces one addition out of its use clock.
Its successor demand then forces a second addition for free: the exposed
candidate is exactly the historical value `c + m`.  The length-two run
prohibition finally forces a third addition, because after two additions
the candidate returns to the pre-entry value `c + 2m + 1`, which the entry
subtraction departed from.  So every use clock of a recurring corridor
candidate emits a burst of at least three consecutive forced additions,
climbing through `c + 2m + 2`, `c + 3m + 4`, and `c + 4m + 7`, at the
price of the single genuinely new demand `c + m`.
-/

/-- The successor demand converts directly into a second forced addition:
the candidate exposed after the first addition is the historical value
`c + m` itself. -/
theorem recurringCandidate_second_forcedAddition
    {c m : Nat}
    (hvalue : a (m + 1) = c + 2 * m + 2)
    (hseen : c + m ∈ valuesThrough (m + 1)) :
    ¬ CanSubtract (m + 2) (stateAt (m + 1)) := by
  intro hcan
  have hfresh : a (m + 1) - (m + 2) ∉ valuesThrough (m + 1) := hcan.2
  have hcandidate : a (m + 1) - (m + 2) = c + m := by omega
  rw [hcandidate] at hfresh
  exact hfresh hseen

/-- **Addition burst.**  A use clock's entry subtraction, first forced
addition, and historical successor force a run of at least three
consecutive additions with explicit values. -/
theorem recurringCandidate_addition_burst
    {c m : Nat}
    (hm : 1 ≤ m)
    (hentry : CanSubtract m (stateAt (m - 1)))
    (hadd₁ : ¬ CanSubtract (m + 1) (stateAt m))
    (hvalue : a (m + 1) = c + 2 * m + 2)
    (hseen : c + m ∈ valuesThrough (m + 1)) :
    ¬ CanSubtract (m + 2) (stateAt (m + 1)) ∧
      ¬ CanSubtract (m + 3) (stateAt (m + 2)) ∧
      a (m + 2) = c + 3 * m + 4 ∧
      a (m + 3) = c + 4 * m + 7 := by
  have hadd₂ := recurringCandidate_second_forcedAddition hvalue hseen
  have hm1 : m - 1 + 1 = m := by omega
  have hentry' : CanSubtract (m - 1 + 1) (stateAt (m - 1)) := by
    rw [hm1]
    exact hentry
  have hadd₁' : ¬ CanSubtract (m - 1 + 2) (stateAt (m - 1 + 1)) := by
    have hidx : m - 1 + 2 = m + 1 := by omega
    have hidx' : m - 1 + 1 = m := by omega
    rw [hidx, hidx']
    exact hadd₁
  have hadd₂' : ¬ CanSubtract (m - 1 + 3) (stateAt (m - 1 + 2)) := by
    have hidx : m - 1 + 3 = m + 2 := by omega
    have hidx' : m - 1 + 2 = m + 1 := by omega
    rw [hidx, hidx']
    exact hadd₂
  have hadd₃' := double_forcedAddition_extends hentry' hadd₁' hadd₂'
  have hadd₃ : ¬ CanSubtract (m + 3) (stateAt (m + 2)) := by
    have hidx : m - 1 + 4 = m + 3 := by omega
    have hidx' : m - 1 + 3 = m + 2 := by omega
    rw [hidx, hidx'] at hadd₃'
    exact hadd₃'
  have hstep₂ : a (m + 2) = a (m + 1) + (m + 2) :=
    a_succ_of_not_canSubtract hadd₂
  have hvalue₂ : a (m + 2) = c + 3 * m + 4 := by omega
  have hstep₃ : a (m + 3) = a (m + 2) + (m + 3) :=
    a_succ_of_not_canSubtract hadd₃
  have hvalue₃ : a (m + 3) = c + 4 * m + 7 := by omega
  exact ⟨hadd₂, hadd₃, hvalue₂, hvalue₃⟩

/-- **Burst stream.**  In the non-divergent corridor branch, arbitrarily
late use clocks perform the full rigid event together with the
three-addition burst. -/
theorem EventualHighCandidateTail.missingUnbounded_or_burstStream
    {target tailStart : Nat}
    (hcorridor : EventualHighCandidateTail target tailStart) :
    (∀ B, ∃ u, B < u ∧ ∀ time, a time ≠ u) ∨
      ∃ c, target < c ∧
        ∀ M, ∃ m, M ≤ m ∧
          nextSubtractionCandidate m = c ∧
          CanSubtract m (stateAt (m - 1)) ∧
          FirstAt a (a m) m ∧
          a m = c + m + 1 ∧
          ¬ CanSubtract (m + 1) (stateAt m) ∧
          ¬ CanSubtract (m + 2) (stateAt (m + 1)) ∧
          ¬ CanSubtract (m + 3) (stateAt (m + 2)) ∧
          a (m + 1) = c + 2 * m + 2 ∧
          a (m + 2) = c + 3 * m + 4 ∧
          a (m + 3) = c + 4 * m + 7 ∧
          c + m ∈ valuesThrough (m + 1) := by
  rcases EventualHighCandidateTail.missingUnbounded_or_rigidEventStream
      hcorridor with
    hmissing | ⟨c, htargetc, hstream⟩
  · exact Or.inl hmissing
  · apply Or.inr
    refine ⟨c, htargetc, ?_⟩
    intro M
    rcases hstream (M + 1) with
      ⟨m, hm, hcand, hentry, hfirst, hdiag, hadd₁, hout, hseen⟩
    have hburst := recurringCandidate_addition_burst
      (show 1 ≤ m by omega) hentry hadd₁ hout hseen
    exact ⟨m, by omega, hcand, hentry, hfirst, hdiag, hadd₁,
      hburst.1, hburst.2.1, hout, hburst.2.2.1, hburst.2.2.2, hseen⟩

end Recaman
