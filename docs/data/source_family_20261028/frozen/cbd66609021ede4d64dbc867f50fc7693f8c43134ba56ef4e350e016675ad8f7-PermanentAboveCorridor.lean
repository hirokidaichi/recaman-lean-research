import Recaman.PermanentAboveCycleRebase

namespace Recaman

noncomputable section

/-! # The canonical below-target corridor inside a stationary cycle

A rebased stationary cycle contains a finite segment beginning at the fresh
endpoint of a historical downcross and ending at the predecessor of its first
weak upcrossing.  Canonicality forces every value on that closed segment to
remain below the target.

The first corridor step already gives a useful strict dichotomy.  A legal
subtraction creates another fresh below-target value and decreases the
history budget.  A forced addition which remains inside the corridor forces
its clock below the target, hence lies in a finite target-bounded region.
-/

/-- All states before and including the predecessor of the first weak
upcrossing remain below the target. -/
theorem FirstWeakUpcrossingStep.value_below_of_between
    {target start returnTime time : Nat}
    (h : FirstWeakUpcrossingStep target start returnTime)
    (hstartBelow : a start < target)
    (hstart : start ≤ time)
    (hreturn : time ≤ returnTime) :
    a time < target := by
  by_cases hbelow : a time < target
  · exact hbelow
  · have habove : target ≤ a time := Nat.le_of_not_gt hbelow
    rcases exists_weakUpcrossingStep_between hstart hstartBelow habove with
      ⟨earlier, hearlier, hfinish⟩
    have hearlierTime : earlier < returnTime := by omega
    exact False.elim (h.first earlier hearlierTime hearlier)

/-- A downcross must be a legal subtraction; forced addition cannot move an
at-or-above-target value to below the target. -/
theorem FutureDowncrossStep.canSubtract
    {target historyHorizon time : Nat}
    (h : FutureDowncrossStep target historyHorizon time) :
    CanSubtract (time + 1) (stateAt time) := by
  by_cases hcan : CanSubtract (time + 1) (stateAt time)
  · exact hcan
  · have hadd := a_succ_of_not_canSubtract hcan
    have hmonotone : a time ≤ a (time + 1) := by omega
    have habove : target ≤ a (time + 1) :=
      Nat.le_trans h.start_at_or_above hmonotone
    exact False.elim (Nat.not_lt_of_ge habove h.endpoint_below)

/-- Typed finite corridor from a fresh downcross endpoint to its canonical
first return crossing. -/
structure CanonicalBelowCorridorCertificate
    (target tailStart historicalFirstTime downTime returnTime : Nat) : Prop where
  target_positive : 0 < target
  historical_tail : MissingStrictAboveTail target tailStart
  downcross : FutureDowncrossStep target historicalFirstTime downTime
  endpoint_first : FirstAt a (a (downTime + 1)) (downTime + 1)
  endpoint_before_tail : downTime + 1 < tailStart
  first_return : FirstWeakUpcrossingStep target (downTime + 1) returnTime
  return_before_tail : returnTime + 1 ≤ tailStart

/-- Every typed discharge certificate supplies its canonical below corridor. -/
theorem PermanentTailDischargeReturnCertificate.exists_belowCorridor
    {target start : Nat} {parent : PhaseSearchNode}
    (h : PermanentTailDischargeReturnCertificate target start parent) :
    CanonicalBelowCorridorCertificate target h.tailStart
      h.historicalFirstTime h.downTime h.returnTime := {
  target_positive := h.combined.tail.target_positive
  historical_tail := h.historical_tail
  downcross := h.downcross
  endpoint_first := h.endpoint_first
  endpoint_before_tail := h.endpoint_before_tail
  first_return := h.return_crossing
  return_before_tail := h.return_before_tail
}

/-- Every point of the typed corridor is below the target. -/
theorem CanonicalBelowCorridorCertificate.value_below
    {target tailStart historicalFirstTime downTime returnTime time : Nat}
    (h : CanonicalBelowCorridorCertificate target tailStart
      historicalFirstTime downTime returnTime)
    (hstart : downTime + 1 ≤ time)
    (hreturn : time ≤ returnTime) :
    a time < target :=
  h.first_return.value_below_of_between h.downcross.endpoint_below
    hstart hreturn

/-- Exact first-step classification of the canonical corridor. -/
inductive CanonicalBelowCorridorFirstStepOutcome
    {target tailStart historicalFirstTime downTime returnTime : Nat}
    (certificate : CanonicalBelowCorridorCertificate target tailStart
      historicalFirstTime downTime returnTime) : Prop
  | immediate_rebound
      (return_eq : returnTime = downTime + 1)
      (down_equation : a (downTime + 1) = a downTime - (downTime + 1))
      (return_equation : a (downTime + 2) =
        a (downTime + 1) + (downTime + 2))
      (valley_equation : a (downTime + 2) = a downTime + 1) :
      CanonicalBelowCorridorFirstStepOutcome certificate
  | delayed_subtraction
      (gap_positive : downTime + 1 < returnTime)
      (legal : CanSubtract (downTime + 2) (stateAt (downTime + 1)))
      (next_first : FirstAt a (a (downTime + 2)) (downTime + 2))
      (next_below : a (downTime + 2) < target)
      (budget_drop : missingBelowCount target (downTime + 2) <
        missingBelowCount target (downTime + 1)) :
      CanonicalBelowCorridorFirstStepOutcome certificate
  | delayed_forced_addition
      (gap_positive : downTime + 1 < returnTime)
      (forced : ¬ CanSubtract (downTime + 2) (stateAt (downTime + 1)))
      (next_equation : a (downTime + 2) =
        a (downTime + 1) + (downTime + 2))
      (next_below : a (downTime + 2) < target)
      (clock_below_target : downTime + 2 < target) :
      CanonicalBelowCorridorFirstStepOutcome certificate

/-- The immediate branch is an exact subtraction/addition valley.  Every
delayed branch either consumes a new below-target history value immediately,
or its forced-addition clock is strictly target-bounded. -/
theorem CanonicalBelowCorridorCertificate.firstStepOutcome
    {target tailStart historicalFirstTime downTime returnTime : Nat}
    (h : CanonicalBelowCorridorCertificate target tailStart
      historicalFirstTime downTime returnTime) :
    CanonicalBelowCorridorFirstStepOutcome h := by
  by_cases himmediate : returnTime = downTime + 1
  · have hdownCan := h.downcross.canSubtract
    have hdownEquation := a_succ_of_canSubtract hdownCan
    have hreturnEquation :=
      a_succ_of_not_canSubtract h.first_return.crossing.forced_addition
    have hreturnEquation' : a (downTime + 2) =
        a (downTime + 1) + (downTime + 2) := by
      simpa [himmediate, Nat.add_assoc] using hreturnEquation
    refine CanonicalBelowCorridorFirstStepOutcome.immediate_rebound
      himmediate hdownEquation ?_ ?_
    · exact hreturnEquation'
    · rw [hreturnEquation', hdownEquation]
      have hpositive : downTime + 1 < a downTime := by
        simpa [a] using hdownCan.1
      omega
  · have hgap : downTime + 1 < returnTime := by
      have hstart := h.first_return.crossing.start_le
      omega
    have hnextLe : downTime + 2 ≤ returnTime := by omega
    have hnextBelow := h.value_below (by omega) hnextLe
    by_cases hcan : CanSubtract (downTime + 2) (stateAt (downTime + 1))
    · have hfirst := firstAt_succ_of_canSubtract hcan
      have hbudget := missingBelowCount_strict_of_firstAt hnextBelow
        (show downTime + 1 < downTime + 2 by omega) hfirst
      exact .delayed_subtraction hgap hcan hfirst hnextBelow hbudget
    · have hequation := a_succ_of_not_canSubtract hcan
      have hequation' : a (downTime + 2) =
          a (downTime + 1) + (downTime + 2) := by
        simpa [Nat.add_assoc] using hequation
      have hclock : downTime + 2 < target := by omega
      exact .delayed_forced_addition hgap hcan hequation' hnextBelow hclock

/-- In particular, a delayed corridor has an immediate strict certificate:
history-budget descent or a clock already inside the finite target region. -/
theorem CanonicalBelowCorridorCertificate.delayed_budgetDrop_or_clockBound
    {target tailStart historicalFirstTime downTime returnTime : Nat}
    (h : CanonicalBelowCorridorCertificate target tailStart
      historicalFirstTime downTime returnTime)
    (hdelayed : downTime + 1 < returnTime) :
    missingBelowCount target (downTime + 2) <
        missingBelowCount target (downTime + 1) ∨
      downTime + 2 < target := by
  cases h.firstStepOutcome with
  | immediate_rebound heq hdown hreturn hvalley => omega
  | delayed_subtraction hgap hcan hfirst hbelow hbudget =>
      exact Or.inl hbudget
  | delayed_forced_addition hgap hforced heq hbelow hclock =>
      exact Or.inr hclock

/-- Every legal subtraction strictly inside the corridor creates a fresh
below-target endpoint and consumes history budget. -/
theorem CanonicalBelowCorridorCertificate.internalSubtraction_budgetDrop
    {target tailStart historicalFirstTime downTime returnTime time : Nat}
    (h : CanonicalBelowCorridorCertificate target tailStart
      historicalFirstTime downTime returnTime)
    (hstart : downTime + 1 ≤ time)
    (hbefore : time < returnTime)
    (hcan : CanSubtract (time + 1) (stateAt time)) :
    missingBelowCount target (time + 1) <
      missingBelowCount target time := by
  have hnextBelow := h.value_below
    (show downTime + 1 ≤ time + 1 by omega)
    (show time + 1 ≤ returnTime by omega)
  have hfirst := firstAt_succ_of_canSubtract hcan
  exact missingBelowCount_strict_of_firstAt hnextBelow (by omega) hfirst

/-- Every forced addition strictly inside the corridor has target-bounded
clock.  Hence an all-addition portion cannot escape to arbitrarily late
times while remaining below the fixed target. -/
theorem CanonicalBelowCorridorCertificate.internalForced_clockBelowTarget
    {target tailStart historicalFirstTime downTime returnTime time : Nat}
    (h : CanonicalBelowCorridorCertificate target tailStart
      historicalFirstTime downTime returnTime)
    (hstart : downTime + 1 ≤ time)
    (hbefore : time < returnTime)
    (hforced : ¬ CanSubtract (time + 1) (stateAt time)) :
    time + 1 < target := by
  have hnextBelow := h.value_below
    (show downTime + 1 ≤ time + 1 by omega)
    (show time + 1 ≤ returnTime by omega)
  have hequation := a_succ_of_not_canSubtract hforced
  omega

/-- Uniform strict alternative at every internal corridor transition. -/
theorem CanonicalBelowCorridorCertificate.internalStep_budgetDrop_or_clockBound
    {target tailStart historicalFirstTime downTime returnTime time : Nat}
    (h : CanonicalBelowCorridorCertificate target tailStart
      historicalFirstTime downTime returnTime)
    (hstart : downTime + 1 ≤ time)
    (hbefore : time < returnTime) :
    missingBelowCount target (time + 1) <
        missingBelowCount target time ∨
      time + 1 < target := by
  by_cases hcan : CanSubtract (time + 1) (stateAt time)
  · exact Or.inl (h.internalSubtraction_budgetDrop hstart hbefore hcan)
  · exact Or.inr (h.internalForced_clockBelowTarget hstart hbefore hcan)

end

end Recaman
