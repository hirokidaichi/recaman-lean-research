import Recaman.RefinedHistoryLanding
import Recaman.PermanentAboveCorridorLandingHorizon

namespace Recaman

noncomputable section

/-! # Horizon bounds with the pinned semantic branch

`PermanentTailTerminalHorizonAnchoredOutcome` bounds the fresh landing and
its restart crossing inside the parent history, which is what lets the
landing be mounted as a node of the refined search domain.  Its semantic
form is still the broad one.

This stage repeats the same bounding with the certificate-tied
`RefinedSemanticEdge` payload.  The bounding argument itself is unchanged:
every value below the missing target already occurs by the tail start and
first occurrences are minimal, so the landing precedes the start; the tail is
strictly above the target from its start, so a weak upcrossing exists in
between and the canonical first crossing is no later; and the start precedes
the parent horizon.
-/

/-- Refinement of `PermanentTailTerminalHorizonAnchoredOutcome`. -/
inductive RefinedTerminalHorizonAnchoredOutcome
    (target start : Nat) (parent : PhaseSearchNode) : Prop
  | fresh_landing
      (childTime parentTime : Nat)
      (progress : TerminalChronologyHistoryProgress target childTime
        parentTime)
      (value landingTime nextCrossingTime : Nat)
      (value_below : value < target)
      (after_parent : parentTime < landingTime)
      (before_child : landingTime ≤ childTime)
      (landing_first : FirstAt a value landingTime)
      (next_crossing : FirstWeakUpcrossingStep target landingTime
        nextCrossingTime)
      (landing_before_start : landingTime < start)
      (crossing_before_start : nextCrossingTime + 1 ≤ start)
      (crossing_before_horizon : nextCrossingTime + 1 < parent.horizon)
      (landing_cursor : TerminalHistoryCursor target landingTime) :
      RefinedTerminalHorizonAnchoredOutcome target start parent
  | refined_semantic
      (edge : RefinedSemanticEdge target start) :
      RefinedTerminalHorizonAnchoredOutcome target start parent
  | exact_replay
      (replayParent : PhaseSearchNode)
      (replaySource : PermanentTailDischargeReturnCertificate target start
        replayParent)
      (replay : TerminalExactDischargeReplayCertificate replaySource) :
      RefinedTerminalHorizonAnchoredOutcome target start parent

/-- Refined form of `terminalHorizonAnchoredOutcome`. -/
theorem PermanentTailCombinedCertificate.refinedTerminalHorizonAnchoredOutcome
    {target start : Nat} {parent : PhaseSearchNode}
    {minimumTime predecessorFirstTime : Nat}
    (h : PermanentTailCombinedCertificate target start parent minimumTime
      predecessorFirstTime) :
    RefinedTerminalHorizonAnchoredOutcome target start parent := by
  cases h.refinedTerminalAnchoredOutcome with
  | fresh_landing childTime parentTime progress value landingTime
      nextCrossingTime hvalue hafter hbefore hfirst hnext hcursor =>
      have hmem := h.tail.below_covered value hvalue
      rcases mem_valuesThrough_iff.mp hmem with ⟨t, ht, hvalueEq⟩
      have hlandingLe : landingTime ≤ start := by
        by_cases hle : landingTime ≤ t
        · omega
        · exact False.elim (hfirst.2 t (by omega) hvalueEq)
      have hbelow : a landingTime < target := by
        rw [hfirst.1]
        exact hvalue
      have habove := h.tail.strictly_above start (Nat.le_refl _)
      have hlandingLt : landingTime < start := by
        by_cases heq : landingTime = start
        · rw [heq] at hbelow
          omega
        · omega
      rcases exists_weakUpcrossingStep_between (Nat.le_of_lt hlandingLt)
          hbelow (Nat.le_of_lt habove) with
        ⟨witness, hwitness, hwitnessBefore⟩
      have hcrossLe : nextCrossingTime ≤ witness := hnext.time_le hwitness
      have hcrossStart : nextCrossingTime + 1 ≤ start := by omega
      have hcrossHorizon : nextCrossingTime + 1 < parent.horizon :=
        Nat.lt_of_le_of_lt hcrossStart
          h.crossing.tail_strictly_before_horizon
      exact .fresh_landing childTime parentTime progress value landingTime
        nextCrossingTime hvalue hafter hbefore hfirst hnext hlandingLt
        hcrossStart hcrossHorizon hcursor
  | refined_semantic edge =>
      exact .refined_semantic edge
  | exact_replay replayParent replaySource replay =>
      exact .exact_replay replayParent replaySource replay

end

end Recaman
