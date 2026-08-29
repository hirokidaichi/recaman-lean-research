import Recaman.PinnedConfigurationAttack

namespace Recaman

noncomputable section

/-! # Forward orbit of the pinned configuration, and the residue at the tail
minimum

Two loose ends are tightened here.

The first is the tail minimum's first-occurrence question.  The transition
dichotomy leaves one branch, and that branch can now be described completely:
the minimum is reached exactly at the tail start by a forced addition, the
minimum value clears its own time by at least two, the time itself clears the
target, and the value one step earlier is not the target.  Everything short of
that branch gives a first occurrence.  The branch itself resists the counting
tools, and the reason is visible in the description: the addition forces
`m ≤ a m`, which is exactly the hypothesis the late-recurrence argument needs
reversed.

The second is the forward march of the pinned configuration.  It is forced for
three steps past the minimum, and the fourth step is where it stops being
forced.  The reason the tail minimum stops helping is arithmetic: the
subtraction candidate at the fourth step is `target + 2 * m + 4`, which clears
the tail minimum `target + 2` by a wide margin, so tail minimality has nothing
to say about it.  Only the third step had a candidate the tail could reach,
and that one was settled by recognising it as the value the orbit held one
step before the minimum.  Still, the branch is not lost information: both
sides of it place an occurrence of `target + 2 * m + 4` on the orbit.
-/

namespace TerminalExactDischargeReplayCertificate

variable {target start : Nat} {parent : PhaseSearchNode}
variable {source : PermanentTailDischargeReturnCertificate target start parent}

/-- The target clears three: the predecessor clock is positive and sits two
below the target. -/
theorem four_le_target
    (r : TerminalExactDischargeReplayCertificate source) :
    4 ≤ target := by
  have hpos := r.firstTime_pos
  have hclock := r.minimum_predecessor_clock_below_target
  omega

/-- Complete description of the residue in the first-occurrence question at
the tail minimum.  Either the tail minimum is a first occurrence, or the
minimum is reached at the tail start by a forced addition whose source value
is at least two, clears the target in time, and is not the target itself. -/
theorem tailMinimum_firstAt_or_tailStartAddition
    (r : TerminalExactDischargeReplayCertificate source) :
    FirstAt a (a source.historicalMinimumTime)
        source.historicalMinimumTime ∨
      (source.historicalMinimumTime = source.tailStart ∧
        a (source.historicalMinimumTime - 1) +
            source.historicalMinimumTime =
          a source.historicalMinimumTime ∧
        source.historicalMinimumTime + 2 ≤
          a source.historicalMinimumTime ∧
        target < source.historicalMinimumTime ∧
        a source.historicalMinimumTime ≠
          target + source.historicalMinimumTime) := by
  rcases r.tailMinimum_transition with ⟨_, hfirst⟩ | ⟨heq, hadd⟩
  · exact Or.inl hfirst
  · by_cases hsmall : a source.historicalMinimumTime ≤
        source.historicalMinimumTime + 1
    · exact Or.inl (r.tailMinimum_firstAt_of_small_value hsmall).2
    · right
      have hpre := r.target_lt_tailStart
      have h5 := r.five_le_minimumTime
      have hposv := a_pos_of_pos_time
        (n := source.historicalMinimumTime - 1) (by omega)
      have hone := one_no_late_occurrence
        (source.historicalMinimumTime - 1) (by omega)
      refine ⟨heq, hadd, by omega, by omega, ?_⟩
      intro hbad
      exact source.historical_tail.target_missing
        ⟨source.historicalMinimumTime - 1, by omega⟩

/-- Fourth step past the pinned tail minimum: the march branches here.  Either
the subtraction fires, or it is blocked by an earlier occurrence of exactly
the same value. -/
theorem pinned_forward_step_four
    (r : TerminalExactDischargeReplayCertificate source)
    (hpin : a source.historicalMinimumTime = target + 2) :
    a (source.historicalMinimumTime + 4) =
        target + 2 * source.historicalMinimumTime + 4 ∨
      (a (source.historicalMinimumTime + 4) =
          target + 4 * source.historicalMinimumTime + 12 ∧
        target + 2 * source.historicalMinimumTime + 4 ∈
          valuesThrough (source.historicalMinimumTime + 3)) := by
  have h5 := r.five_le_minimumTime
  have htgt := r.four_le_target
  obtain ⟨h1, h2, h3⟩ := r.pinned_forward_orbit hpin
  by_cases hcan : CanSubtract (source.historicalMinimumTime + 3 + 1)
      (stateAt (source.historicalMinimumTime + 3))
  · left
    have hstep : a (source.historicalMinimumTime + 3 + 1) =
        a (source.historicalMinimumTime + 3) -
          (source.historicalMinimumTime + 3 + 1) :=
      a_succ_of_canSubtract (n := source.historicalMinimumTime + 3) hcan
    have hstep' : a (source.historicalMinimumTime + 4) =
        a (source.historicalMinimumTime + 3) -
          (source.historicalMinimumTime + 4) := by
      simpa using hstep
    omega
  · right
    have hstep : a (source.historicalMinimumTime + 3 + 1) =
        a (source.historicalMinimumTime + 3) +
          (source.historicalMinimumTime + 3 + 1) :=
      a_succ_of_not_canSubtract (n := source.historicalMinimumTime + 3) hcan
    have hstep' : a (source.historicalMinimumTime + 4) =
        a (source.historicalMinimumTime + 3) +
          (source.historicalMinimumTime + 4) := by
      simpa using hstep
    rcases not_canSubtract_cases
      (n := source.historicalMinimumTime + 3) hcan with hsmall | hseen
    · exact False.elim (by omega)
    · have heq : a (source.historicalMinimumTime + 3) -
          (source.historicalMinimumTime + 3 + 1) =
          target + 2 * source.historicalMinimumTime + 4 := by omega
      rw [heq] at hseen
      exact ⟨by omega, hseen⟩

/-- Whichever side the fourth step takes, the value `target + 2 * m + 4` is
placed on the orbit. -/
theorem pinned_forward_attains
    (r : TerminalExactDischargeReplayCertificate source)
    (hpin : a source.historicalMinimumTime = target + 2) :
    ∃ time, a time = target + 2 * source.historicalMinimumTime + 4 := by
  rcases r.pinned_forward_step_four hpin with hsub | ⟨_, hseen⟩
  · exact ⟨source.historicalMinimumTime + 4, hsub⟩
  · rcases mem_valuesThrough_iff.mp hseen with ⟨t, _, hval⟩
    exact ⟨t, hval⟩

/-- The fourth-step candidate clears the tail minimum by a wide margin, which
is precisely why tail minimality cannot decide the branch.  Only the third
step had a candidate the tail could reach. -/
theorem pinned_forward_candidate_above_tailMinimum
    (r : TerminalExactDischargeReplayCertificate source)
    (hpin : a source.historicalMinimumTime = target + 2) :
    a source.historicalMinimumTime + 2 * source.historicalMinimumTime + 2 =
        target + 2 * source.historicalMinimumTime + 4 ∧
      a source.historicalMinimumTime <
        target + 2 * source.historicalMinimumTime + 4 := by
  have h5 := r.five_le_minimumTime
  exact ⟨by omega, by omega⟩

/-- Connection data between the two pinned intervals: the second landing sits
strictly below the target while the whole tail sits strictly above it, so the
orbit has to climb back across the target somewhere between the landing and
the tail start, without ever taking the target value. -/
theorem pinned_landing_below_tail_above
    (r : TerminalExactDischargeReplayCertificate source)
    (hpin : PinnedTailMinimumConfiguration target
      source.historicalFirstTime)
    (hmin : a source.historicalMinimumTime = target + 2) :
    a (source.historicalFirstTime + 2) < target ∧
      source.historicalFirstTime + 2 < source.tailStart ∧
      (∀ time, source.tailStart ≤ time → target + 1 < a time) ∧
      (∀ time, a time ≠ target) := by
  have hsecond := hpin.second_landing
  have hclock := hpin.clock_bound
  have hpre := r.target_lt_tailStart
  have hbefore := r.minimum_predecessor_clock_below_target
  refine ⟨by omega, by omega, ?_, ?_⟩
  · intro time htime
    have hlow := source.historical_minimum.minimum.minimal time htime
    omega
  · intro time heq
    exact source.historical_tail.target_missing ⟨time, heq⟩

end TerminalExactDischargeReplayCertificate

end

end Recaman
