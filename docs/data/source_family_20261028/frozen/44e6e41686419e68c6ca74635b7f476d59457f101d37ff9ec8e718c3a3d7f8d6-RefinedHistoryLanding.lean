import Recaman.RefinedReplayInterface
import Recaman.PermanentAboveCorridorHistoryLanding

namespace Recaman

noncomputable section

/-! # Anchored landings with the pinned semantic branch

`PermanentTailTerminalAnchoredOutcome` upgrades every history edge to an
explicit fresh below-target landing, its transported history cursor, and the
canonical restart crossing.  Its semantic form is still the broad one.

This stage repeats that upgrade with the certificate-tied
`RefinedSemanticEdge` payload.  The landing recovery itself is unchanged: the
strengthened history edge already supplies both the below-target witness and
the cursor at the landing time through `exists_freshLandingCursor`.
-/

/-- Refinement of `PermanentTailTerminalAnchoredOutcome`. -/
inductive RefinedTerminalAnchoredOutcome (target start : Nat) : Prop
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
      (landing_cursor : TerminalHistoryCursor target landingTime) :
      RefinedTerminalAnchoredOutcome target start
  | refined_semantic
      (edge : RefinedSemanticEdge target start) :
      RefinedTerminalAnchoredOutcome target start
  | exact_replay
      (replayParent : PhaseSearchNode)
      (replaySource : PermanentTailDischargeReturnCertificate target start
        replayParent)
      (replay : TerminalExactDischargeReplayCertificate replaySource) :
      RefinedTerminalAnchoredOutcome target start

/-- Refined form of `terminalAnchoredOutcome`: every branch hands the outer
recursion a certificate-tied refined semantic edge, a replay fixed point, or
a concrete fresh landing with its cursor and restart crossing. -/
theorem PermanentTailCombinedCertificate.refinedTerminalAnchoredOutcome
    {target start : Nat} {parent : PhaseSearchNode}
    {minimumTime predecessorFirstTime : Nat}
    (h : PermanentTailCombinedCertificate target start parent minimumTime
      predecessorFirstTime) :
    RefinedTerminalAnchoredOutcome target start := by
  cases h.refinedTerminalMissingOutcome with
  | history_progress childTime parentTime progress =>
      rcases progress.exists_freshLandingCursor with
        ⟨value, landingTime, hvalue, hafter, hbefore, hfirst, hcursor⟩
      have hbelow : a landingTime < target := by
        rw [hfirst.1]
        exact hvalue
      rcases exists_firstWeakUpcrossingStep_from_below
          h.tail.target_positive hbelow with ⟨nextCrossingTime, hnext⟩
      exact .fresh_landing childTime parentTime progress value landingTime
        nextCrossingTime hvalue hafter hbefore hfirst hnext hcursor
  | refined_semantic edge =>
      exact .refined_semantic edge
  | exact_replay replayParent replaySource replay =>
      exact .exact_replay replayParent replaySource replay

end

end Recaman
