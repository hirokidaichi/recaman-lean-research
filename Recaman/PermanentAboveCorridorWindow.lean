import Recaman.PermanentAboveCorridorBoundary

namespace Recaman

noncomputable section

/-! # Finite crossing window of a terminal all-forced suffix

After all legal suffix endpoints have been consumed, a nonempty terminal
suffix is forced addition all the way to its first return crossing.  Its
entire trace, including the final upcrossing step, is therefore explicit.
Missing-target provenance makes the crossing strict on both sides.

The target gap below the crossing and the overshoot above it are each at
most the return clock.  The remaining outer obstruction is thus a finite
arithmetic crossing window, not an unstructured orbit segment.
-/

/-- Telescoping trace on an all-forced suffix up to its return predecessor. -/
theorem AllForcedAdditionSuffix.value_eq_add_forcedClockSum
    {target endpointTime returnTime steps : Nat}
    {suffix : CanonicalBelowCorridorSuffix target endpointTime returnTime}
    (h : AllForcedAdditionSuffix suffix)
    (hfinish : endpointTime + steps ≤ returnTime) :
    a (endpointTime + steps) =
      a endpointTime + forcedClockSum endpointTime steps := by
  induction steps with
  | zero => simp [forcedClockSum]
  | succ steps ih =>
      have hprevious : endpointTime + steps < returnTime := by omega
      have hstart : endpointTime ≤ endpointTime + steps := by omega
      have hforced := h (endpointTime + steps) hstart hprevious
      have hequation := a_succ_of_not_canSubtract hforced
      have ih' := ih (by omega)
      rw [forcedClockSum]
      calc
        a (endpointTime + (steps + 1)) =
            a (endpointTime + steps + 1) := by congr 1 <;> omega
        _ = a (endpointTime + steps) +
            (endpointTime + steps + 1) := hequation
        _ = (a endpointTime + forcedClockSum endpointTime steps) +
            (endpointTime + steps + 1) := by rw [ih']
        _ = a endpointTime +
            (forcedClockSum endpointTime steps +
              (endpointTime + steps + 1)) := by omega

/-- The same trace extended through the final forced return upcrossing. -/
theorem AllForcedAdditionSuffix.final_value_eq_add_forcedClockSum
    {target endpointTime returnTime : Nat}
    {suffix : CanonicalBelowCorridorSuffix target endpointTime returnTime}
    (h : AllForcedAdditionSuffix suffix) :
    a (returnTime + 1) =
      a endpointTime +
        forcedClockSum endpointTime (returnTime - endpointTime + 1) := by
  have hendpointLe := suffix.first_return.crossing.start_le
  have htrace := h.value_eq_add_forcedClockSum
    (steps := returnTime - endpointTime) (by omega)
  have htimeEq : endpointTime + (returnTime - endpointTime) =
      returnTime := by omega
  rw [htimeEq] at htrace
  have hfinal := a_succ_of_not_canSubtract
    suffix.first_return.crossing.forced_addition
  rw [forcedClockSum]
  have hclockEq : endpointTime + (returnTime - endpointTime) + 1 =
      returnTime + 1 := by omega
  rw [hclockEq]
  calc
    a (returnTime + 1) = a returnTime + (returnTime + 1) := hfinal
    _ = (a endpointTime +
          forcedClockSum endpointTime (returnTime - endpointTime)) +
        (returnTime + 1) := by rw [htrace]
    _ = a endpointTime +
        (forcedClockSum endpointTime (returnTime - endpointTime) +
          (returnTime + 1)) := by omega

/-- Proof object for the terminal nonempty all-forced suffix under a missing
target. -/
structure TerminalAllForcedSuffixCertificate
    (target endpointTime returnTime : Nat) : Prop where
  suffix : CanonicalBelowCorridorSuffix target endpointTime returnTime
  target_missing : ¬ ∃ witness, a witness = target
  endpoint_before_return : endpointTime < returnTime
  all_forced : AllForcedAdditionSuffix suffix

/-- Minimal finite arithmetic window remaining at the terminal crossing. -/
structure TerminalAllForcedCrossingWindow
    (target endpointTime returnTime : Nat) : Prop where
  certificate : TerminalAllForcedSuffixCertificate target endpointTime
    returnTime
  return_before_target : returnTime < target
  predecessor_below : a returnTime < target
  endpoint_above : target < a (returnTime + 1)
  final_equation : a (returnTime + 1) =
    a returnTime + (returnTime + 1)
  full_trace : a (returnTime + 1) =
    a endpointTime +
      forcedClockSum endpointTime (returnTime - endpointTime + 1)
  target_gap_positive : 0 < target - a returnTime
  target_gap_le_clock : target - a returnTime ≤ returnTime
  overshoot_positive : 0 < a (returnTime + 1) - target
  overshoot_le_clock : a (returnTime + 1) - target ≤ returnTime

/-- Every terminal all-forced suffix yields the finite crossing window. -/
theorem TerminalAllForcedSuffixCertificate.crossingWindow
    {target endpointTime returnTime : Nat}
    (h : TerminalAllForcedSuffixCertificate target endpointTime returnTime) :
    TerminalAllForcedCrossingWindow target endpointTime returnTime := by
  have hreturnBefore := h.all_forced.returnTime_lt_target
    h.endpoint_before_return
  have hpredecessorBelow := h.suffix.first_return.crossing.below
  have hendpointGe := h.suffix.first_return.crossing.endpoint_ge
  have hendpointNe : a (returnTime + 1) ≠ target := by
    intro hequal
    exact h.target_missing ⟨returnTime + 1, hequal⟩
  have hendpointAbove : target < a (returnTime + 1) :=
    Nat.lt_of_le_of_ne hendpointGe (Ne.symm hendpointNe)
  have hfinal := a_succ_of_not_canSubtract
    h.suffix.first_return.crossing.forced_addition
  have htrace := h.all_forced.final_value_eq_add_forcedClockSum
  have hgapPositive : 0 < target - a returnTime := by omega
  have hgapLe : target - a returnTime ≤ returnTime := by omega
  have hoverPositive : 0 < a (returnTime + 1) - target := by omega
  have hoverLe : a (returnTime + 1) - target ≤ returnTime := by omega
  exact {
    certificate := h
    return_before_target := hreturnBefore
    predecessor_below := hpredecessorBelow
    endpoint_above := hendpointAbove
    final_equation := hfinal
    full_trace := htrace
    target_gap_positive := hgapPositive
    target_gap_le_clock := hgapLe
    overshoot_positive := hoverPositive
    overshoot_le_clock := hoverLe
  }

/-- If a legal child has no later legal endpoint, the hypothetical permanent
tail constructs exactly the terminal all-forced crossing window. -/
theorem CanonicalReturnRebaseCertificate.terminalWindow_of_legal
    {target start : Nat} {parent : PhaseSearchNode}
    {source : PermanentTailDischargeReturnCertificate target start parent}
    (h : CanonicalReturnRebaseCertificate source)
    {time : Nat}
    (hstart : h.discharge.downTime + 1 ≤ time)
    (hbefore : time < h.discharge.returnTime)
    (hcan : CanSubtract (time + 1) (stateAt time))
    (hterminal : ¬ ∃ later,
      time + 1 ≤ later ∧ later < h.discharge.returnTime ∧
        CanSubtract (later + 1) (stateAt later)) :
    ∃ _window : TerminalAllForcedCrossingWindow target (time + 1)
        h.discharge.returnTime,
      missingBelowCount target (time + 1) <
        missingBelowCount target time := by
  rcases h.legalSuffixChild_missingBoundary hstart hbefore hcan with
    ⟨child, hstrict, hbudget, hremaining⟩
  rcases hremaining with hnext | hall
  · exact False.elim (hterminal hnext)
  · let terminal : TerminalAllForcedSuffixCertificate target (time + 1)
        h.discharge.returnTime := {
      suffix := child
      target_missing := h.discharge.combined.tail.target_missing
      endpoint_before_return := hstrict
      all_forced := hall
    }
    exact ⟨terminal.crossingWindow, hbudget⟩

end

end Recaman
