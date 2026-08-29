import Recaman.RefinedLandingHorizon
import Recaman.PermanentAboveCorridorLandingMount

namespace Recaman

noncomputable section

/-! # Mounted landings with the pinned semantic branch

`PermanentTailTerminalMountedOutcome` turns every bounded landing into an
actual member of the refined search domain: a ready crossing node at the
parent horizon.  Its semantic form is still the broad one.

This stage repeats the mounting with the certificate-tied
`RefinedSemanticEdge` payload.  The mounting itself needs no new work:
`landingReadyCrossing` is stated on the combined certificate and the
bounded crossing alone, so it applies verbatim.  After this stage every
branch of the closed terminal analysis speaks the language of the refined
recursion domain.
-/

/-- Refinement of `PermanentTailTerminalMountedOutcome`. -/
inductive RefinedTerminalMountedOutcome
    (target start : Nat) (parent : PhaseSearchNode) : Prop
  | landing_crossing
      (childTime parentTime : Nat)
      (progress : TerminalChronologyHistoryProgress target childTime
        parentTime)
      (value landingTime nextCrossingTime : Nat)
      (value_below : value < target)
      (after_parent : parentTime < landingTime)
      (landing_first : FirstAt a value landingTime)
      (next_crossing : FirstWeakUpcrossingStep target landingTime
        nextCrossingTime)
      (crossing_before_start : nextCrossingTime + 1 ≤ start)
      (crossing_before_horizon : nextCrossingTime + 1 < parent.horizon)
      (ready : ReadyCrossingSearchInvariant target
        (terminalPredecessorCrossingNode parent nextCrossingTime))
      (before_child : landingTime ≤ childTime)
      (landing_cursor : TerminalHistoryCursor target landingTime) :
      RefinedTerminalMountedOutcome target start parent
  | refined_semantic
      (edge : RefinedSemanticEdge target start) :
      RefinedTerminalMountedOutcome target start parent
  | exact_replay
      (replayParent : PhaseSearchNode)
      (replaySource : PermanentTailDischargeReturnCertificate target start
        replayParent)
      (replay : TerminalExactDischargeReplayCertificate replaySource) :
      RefinedTerminalMountedOutcome target start parent

/-- Refined form of `terminalMountedOutcome`. -/
theorem PermanentTailCombinedCertificate.refinedTerminalMountedOutcome
    {target start : Nat} {parent : PhaseSearchNode}
    {minimumTime predecessorFirstTime : Nat}
    (h : PermanentTailCombinedCertificate target start parent minimumTime
      predecessorFirstTime) :
    RefinedTerminalMountedOutcome target start parent := by
  cases h.refinedTerminalHorizonAnchoredOutcome with
  | fresh_landing childTime parentTime progress value landingTime
      nextCrossingTime hvalue hafter hbefore hfirst hnext hlandingLt
      hcrossStart hcrossHorizon hcursor =>
      exact .landing_crossing childTime parentTime progress value
        landingTime nextCrossingTime hvalue hafter hfirst hnext hcrossStart
        hcrossHorizon (h.landingReadyCrossing hnext hcrossHorizon) hbefore
        hcursor
  | refined_semantic edge =>
      exact .refined_semantic edge
  | exact_replay replayParent replaySource replay =>
      exact .exact_replay replayParent replaySource replay

/-- Re-entry form: a mounted landing crossing is itself a new combined
parent of the same analysis, so the refined interface is available there
too. -/
theorem PermanentTailCombinedCertificate.refinedTerminalMountedOutcome_of_landing
    {target start : Nat} {parent : PhaseSearchNode}
    {minimumTime predecessorFirstTime : Nat}
    (h : PermanentTailCombinedCertificate target start parent minimumTime
      predecessorFirstTime)
    {crossingTime : Nat}
    (ready : ReadyCrossingSearchInvariant target
      (terminalPredecessorCrossingNode parent crossingTime)) :
    RefinedTerminalMountedOutcome target start
      (terminalPredecessorCrossingNode parent crossingTime) :=
  (h.installReadyCrossing ready).refinedTerminalMountedOutcome

end

end Recaman
