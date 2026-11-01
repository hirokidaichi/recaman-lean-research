import Recaman.PermanentAboveCorridorLandingMount

namespace Recaman

noncomputable section

/-! # Installing mounted landing crossings as new combined parents

Every permanent-tail field of the combined certificate other than the ready
crossing itself depends only on the shared history horizon.  A mounted
landing crossing reuses the parent horizon, so the whole combined
certificate transports onto it.  The closed terminal analysis can therefore
be re-entered from the mounted node: landing crossings are not terminal
leaves but new parents of the same analysis.

Relative to the old parent the mounted node sits in the familiar two-way
split: a strictly smaller crossing anchor is an immediate global phase
descent, and otherwise the anchor is nondecreasing — the same boundary that
governs the installed successor iteration.
-/

/-- The combined certificate transports onto any mounted ready crossing at
the same horizon. -/
theorem PermanentTailCombinedCertificate.installReadyCrossing
    {target start : Nat} {parent : PhaseSearchNode}
    {minimumTime predecessorFirstTime : Nat}
    (h : PermanentTailCombinedCertificate target start parent minimumTime
      predecessorFirstTime)
    {crossingTime : Nat}
    (ready : ReadyCrossingSearchInvariant target
      (terminalPredecessorCrossingNode parent crossingTime)) :
    PermanentTailCombinedCertificate target start
      (terminalPredecessorCrossingNode parent crossingTime) minimumTime
      predecessorFirstTime := by
  have hcrossing : PermanentTailCrossingCertificate target start
      (terminalPredecessorCrossingNode parent crossingTime) := {
    ready_crossing := ready
    horizon_in_tail := by
      simpa [terminalPredecessorCrossingNode] using
        h.crossing.horizon_in_tail
    tail_strictly_before_horizon := by
      simpa [terminalPredecessorCrossingNode] using
        h.crossing.tail_strictly_before_horizon
    budget_zero := by
      simpa [terminalPredecessorCrossingNode] using
        h.crossing.budget_zero
    horizon_strictly_above := by
      simpa [terminalPredecessorCrossingNode] using
        h.crossing.horizon_strictly_above
    no_future_downcross := by
      simpa [terminalPredecessorCrossingNode] using
        h.crossing.no_future_downcross
  }
  exact {
    tail := h.tail
    crossing := hcrossing
    minimum := h.minimum
  }

/-- Rank position of a mounted crossing relative to its parent: immediate
global phase descent, or a nondecreasing anchor. -/
inductive MountedLandingRankOutcome
    (target : Nat) (parent : PhaseSearchNode) (crossingTime : Nat) : Prop
  | phase_exit
      (progress : PhaseSearchProgress target
        (terminalPredecessorCrossingNode parent crossingTime) parent) :
      MountedLandingRankOutcome target parent crossingTime
  | anchor_nondecreasing
      (hanchor : parent.anchorParent ≤ a crossingTime) :
      MountedLandingRankOutcome target parent crossingTime

/-- The two-way anchor boundary of the installed iteration also governs
mounted landing crossings. -/
theorem PermanentTailCombinedCertificate.mountedLandingRankOutcome
    {target start : Nat} {parent : PhaseSearchNode}
    {minimumTime predecessorFirstTime : Nat}
    (h : PermanentTailCombinedCertificate target start parent minimumTime
      predecessorFirstTime)
    (crossingTime : Nat) :
    MountedLandingRankOutcome target parent crossingTime := by
  by_cases hdrop : a crossingTime < parent.anchorParent
  · rcases h.crossing.ready_crossing.crossing with
      ⟨oldAnchor, oldTime, quotient, remainder, hold⟩
    have hparentAnchor : parent.anchorParent = a oldTime := by
      simpa using congrArg PhaseSearchNode.anchorParent hold.node_eq
    have hdrop' : a crossingTime < a oldTime := by
      rw [← hparentAnchor]
      exact hdrop
    have hprogress : PhaseSearchProgress target
        (terminalPredecessorCrossingNode parent crossingTime) parent := by
      rw [hold.node_eq]
      exact phaseSearchProgress_of_horizonAndAnchor (Nat.le_refl _) hdrop'
    exact .phase_exit hprogress
  · exact .anchor_nondecreasing (Nat.le_of_not_gt hdrop)

/-- The closed terminal analysis re-enters from a mounted landing crossing:
landing branches are new parents, not terminal leaves. -/
theorem PermanentTailCombinedCertificate.terminalMountedOutcome_of_landing
    {target start : Nat} {parent : PhaseSearchNode}
    {minimumTime predecessorFirstTime : Nat}
    (h : PermanentTailCombinedCertificate target start parent minimumTime
      predecessorFirstTime)
    {crossingTime : Nat}
    (ready : ReadyCrossingSearchInvariant target
      (terminalPredecessorCrossingNode parent crossingTime)) :
    PermanentTailTerminalMountedOutcome target start
      (terminalPredecessorCrossingNode parent crossingTime) :=
  (h.installReadyCrossing ready).terminalMountedOutcome

end

end Recaman
