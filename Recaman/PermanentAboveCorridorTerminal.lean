import Recaman.PermanentAboveCorridorWindow

namespace Recaman

noncomputable section

/-! # Strong normalization of a canonical below corridor

Every legal subtraction inside a missing-target corridor moves its canonical
suffix endpoint strictly toward the fixed return.  Strong induction on the
remaining endpoint cursor therefore terminates at an all-forced suffix.

For the original historical corridor there are exactly two resulting shapes:
an immediate subtraction/addition valley, or a delayed corridor ending in the
finite crossing window developed in `PermanentAboveCorridorWindow`.
-/

/-- A nonempty missing-target suffix reaches an all-forced terminal suffix
after finitely many legal endpoint moves. -/
theorem CanonicalBelowCorridorSuffix.exists_terminalAllForced
    {target endpointTime returnTime : Nat}
    (h : CanonicalBelowCorridorSuffix target endpointTime returnTime)
    (htargetMissing : ¬ ∃ witness, a witness = target)
    (hbefore : endpointTime < returnTime) :
    ∃ terminalEndpoint,
      endpointTime ≤ terminalEndpoint ∧
      terminalEndpoint < returnTime ∧
      ∃ terminalSuffix : CanonicalBelowCorridorSuffix target
          terminalEndpoint returnTime,
        AllForcedAdditionSuffix terminalSuffix := by
  have descend : ∀ remaining endpoint,
      corridorSuffixRemaining returnTime endpoint = remaining →
      CanonicalBelowCorridorSuffix target endpoint returnTime →
      endpoint < returnTime →
      ∃ terminalEndpoint,
        endpoint ≤ terminalEndpoint ∧
        terminalEndpoint < returnTime ∧
        ∃ terminalSuffix : CanonicalBelowCorridorSuffix target
            terminalEndpoint returnTime,
          AllForcedAdditionSuffix terminalSuffix := by
    intro remaining
    induction remaining using Nat.strongRecOn with
    | ind remaining ih =>
        intro endpoint hrank suffix hendpointBefore
        by_cases hlegal : ∃ time,
            endpoint ≤ time ∧ time < returnTime ∧
              CanSubtract (time + 1) (stateAt time)
        · rcases hlegal with ⟨time, hstart, htimeBefore, hcan⟩
          rcases suffix.child_of_internalSubtraction_missing
              htargetMissing hstart htimeBefore hcan with
            ⟨child, _hbudget, hprogress, hchildBefore, _hremaining⟩
          have hchildRank :
              corridorSuffixRemaining returnTime (time + 1) < remaining := by
            unfold CorridorSuffixProgress at hprogress
            rw [hrank] at hprogress
            exact hprogress
          rcases ih (corridorSuffixRemaining returnTime (time + 1))
              hchildRank (time + 1) rfl child hchildBefore with
            ⟨terminalEndpoint, hchildLe, hterminalBefore,
              terminalSuffix, hallForced⟩
          exact ⟨terminalEndpoint, by omega, hterminalBefore,
            terminalSuffix, hallForced⟩
        · have hallForced : AllForcedAdditionSuffix suffix := by
            intro time hstart htimeBefore hcan
            exact hlegal ⟨time, hstart, htimeBefore, hcan⟩
          exact ⟨endpoint, Nat.le_refl _, hendpointBefore, suffix,
            hallForced⟩
  exact descend (corridorSuffixRemaining returnTime endpointTime)
    endpointTime rfl h hbefore

/-- The exact historical valley left when the first return is immediate. -/
structure ImmediateHistoricalValleyCertificate
    (target downTime returnTime : Nat) : Prop where
  target_missing : ¬ ∃ witness, a witness = target
  return_eq : returnTime = downTime + 1
  source_above : target < a downTime
  endpoint_below : a (downTime + 1) < target
  down_equation : a (downTime + 1) = a downTime - (downTime + 1)
  return_equation : a (downTime + 2) =
    a (downTime + 1) + (downTime + 2)
  valley_equation : a (downTime + 2) = a downTime + 1

/-- A canonical historical corridor with an immediate return supplies the
typed exact-valley certificate. -/
theorem CanonicalBelowCorridorCertificate.immediateHistoricalValley
    {target tailStart historicalFirstTime downTime returnTime : Nat}
    (h : CanonicalBelowCorridorCertificate target tailStart
      historicalFirstTime downTime returnTime)
    (htargetMissing : ¬ ∃ witness, a witness = target)
    (himmediate : returnTime = downTime + 1) :
    ImmediateHistoricalValleyCertificate target downTime returnTime := by
  have hsourceNe : a downTime ≠ target := by
    intro hequal
    exact htargetMissing ⟨downTime, hequal⟩
  have hsourceAbove : target < a downTime := by
    have hsourceGe := h.downcross.start_at_or_above
    omega
  cases h.firstStepOutcome with
  | immediate_rebound hreturn hdown hreturnEquation hvalley =>
      exact {
        target_missing := htargetMissing
        return_eq := hreturn
        source_above := hsourceAbove
        endpoint_below := h.downcross.endpoint_below
        down_equation := hdown
        return_equation := hreturnEquation
        valley_equation := hvalley
      }
  | delayed_subtraction hgap _ _ _ _ => omega
  | delayed_forced_addition hgap _ _ _ _ => omega

/-- The normalized terminal shape of a typed historical discharge. -/
inductive PermanentTailDischargeTerminalShape
    {target start : Nat} {parent : PhaseSearchNode}
    (source : PermanentTailDischargeReturnCertificate target start parent) :
    Prop
  | immediate_valley
      (certificate : ImmediateHistoricalValleyCertificate target
        source.downTime source.returnTime) :
      PermanentTailDischargeTerminalShape source
  | finite_crossing_window
      (terminalEndpoint : Nat)
      (origin_le : source.downTime + 1 ≤ terminalEndpoint)
      (window : TerminalAllForcedCrossingWindow target terminalEndpoint
        source.returnTime) :
      PermanentTailDischargeTerminalShape source

/-- Every typed historical discharge normalizes to exactly the two explicit
terminal shapes: the original immediate valley or a finite all-forced
crossing window. -/
theorem PermanentTailDischargeReturnCertificate.terminalShape
    {target start : Nat} {parent : PhaseSearchNode}
    (h : PermanentTailDischargeReturnCertificate target start parent) :
    PermanentTailDischargeTerminalShape h := by
  let corridor := h.exists_belowCorridor
  by_cases himmediate : h.returnTime = h.downTime + 1
  · exact .immediate_valley
      (corridor.immediateHistoricalValley
        h.combined.tail.target_missing himmediate)
  · have hbefore : h.downTime + 1 < h.returnTime := by
      have hstart := corridor.first_return.crossing.start_le
      omega
    rcases corridor.toSuffix.exists_terminalAllForced
        h.combined.tail.target_missing hbefore with
      ⟨terminalEndpoint, horiginLe, hterminalBefore, terminalSuffix,
        hallForced⟩
    let terminal : TerminalAllForcedSuffixCertificate target
        terminalEndpoint h.returnTime := {
      suffix := terminalSuffix
      target_missing := h.combined.tail.target_missing
      endpoint_before_return := hterminalBefore
      all_forced := hallForced
    }
    exact .finite_crossing_window terminalEndpoint horiginLe
      terminal.crossingWindow

end

end Recaman
