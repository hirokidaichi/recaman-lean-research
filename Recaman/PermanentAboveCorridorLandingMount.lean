import Recaman.PermanentAboveCorridorLandingHorizon

namespace Recaman

noncomputable section

/-! # Mounting anchored landings as ready crossing nodes

A first weak upcrossing that finishes strictly inside the parent horizon has
everything a crossing-recovery certificate needs inside a missing-target
tail: the endpoint strictly exceeds the target because the target itself is
missing, the step is a certified forced addition, and coordinates exist at
the positive post-crossing time.  The parent's own readiness clock
transports because the mounted node reuses the parent horizon.

Hence every history edge of the closed terminal analysis now delivers an
actual member of the refined semantic domain — a ready crossing node at the
parent horizon — rather than only numeric landing data.  Together with the
semantic and replay branches, all interface branches speak the language of
the outer search domain.
-/

/-- Any first upcrossing finishing inside the parent horizon mounts as a
ready crossing node of the refined semantic domain. -/
theorem PermanentTailCombinedCertificate.landingReadyCrossing
    {target start : Nat} {parent : PhaseSearchNode}
    {minimumTime predecessorFirstTime : Nat}
    (h : PermanentTailCombinedCertificate target start parent minimumTime
      predecessorFirstTime)
    {landingTime nextCrossingTime : Nat}
    (next_crossing : FirstWeakUpcrossingStep target landingTime
      nextCrossingTime)
    (crossing_before_horizon : nextCrossingTime + 1 < parent.horizon) :
    ReadyCrossingSearchInvariant target
      (terminalPredecessorCrossingNode parent nextCrossingTime) := by
  have hendpointNe : a (nextCrossingTime + 1) ≠ target := fun hequal =>
    h.tail.target_missing ⟨nextCrossingTime + 1, hequal⟩
  have hendpointStrict : target < a (nextCrossingTime + 1) :=
    Nat.lt_of_le_of_ne next_crossing.crossing.endpoint_ge
      (Ne.symm hendpointNe)
  have htargetUnseen : target ∉ valuesThrough nextCrossingTime := by
    intro hseen
    rcases mem_valuesThrough_iff.mp hseen with ⟨witness, _, hvalue⟩
    exact h.tail.target_missing ⟨witness, hvalue⟩
  rcases exists_coordinatesAt (n := nextCrossingTime + 1) (by omega) with
    ⟨quotient, remainder, hcoordinates⟩
  have hrecovery : CrossingRecoveryInvariant target parent.horizon
      (a (nextCrossingTime + 1)) nextCrossingTime quotient remainder := {
    target_missing := htargetUnseen
    forced_addition := next_crossing.crossing.forced_addition
    crossing := ⟨next_crossing.crossing.below, hendpointStrict,
      a_succ_of_not_canSubtract next_crossing.crossing.forced_addition⟩
    coordinates := hcoordinates
    crossing_before_horizon := crossing_before_horizon
    predecessor_lt_anchor :=
      Nat.lt_trans next_crossing.crossing.below hendpointStrict
  }
  exact {
    crossing := ⟨a (nextCrossingTime + 1), nextCrossingTime, quotient,
      remainder, {
        target_positive := h.tail.target_positive
        node_eq := rfl
        recovery := hrecovery
      }⟩
    horizon_ready := by
      simpa [terminalPredecessorCrossingNode] using
        h.crossing.ready_crossing.horizon_ready
  }

/-- Terminal interface whose history branch carries an actual semantic node:
the mounted ready crossing at the parent horizon. -/
inductive PermanentTailTerminalMountedOutcome
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
      PermanentTailTerminalMountedOutcome target start parent
  | semantic_progress
      (stepParent child : PhaseSearchNode)
      (semantic : PhaseSemanticInvariant target child)
      (progress : PhaseSearchProgress target child stepParent) :
      PermanentTailTerminalMountedOutcome target start parent
  | exact_replay
      (replayParent : PhaseSearchNode)
      (replaySource : PermanentTailDischargeReturnCertificate target start
        replayParent)
      (replay : TerminalExactDischargeReplayCertificate replaySource) :
      PermanentTailTerminalMountedOutcome target start parent

/-- Every branch of the closed terminal analysis now hands the outer search
an object of its own semantic domain. -/
theorem PermanentTailCombinedCertificate.terminalMountedOutcome
    {target start : Nat} {parent : PhaseSearchNode}
    {minimumTime predecessorFirstTime : Nat}
    (h : PermanentTailCombinedCertificate target start parent minimumTime
      predecessorFirstTime) :
    PermanentTailTerminalMountedOutcome target start parent := by
  cases h.terminalHorizonAnchoredOutcome with
  | fresh_landing childTime parentTime progress value landingTime
      nextCrossingTime hvalue hafter hbefore hfirst hnext hlandingLt
      hcrossStart hcrossHorizon hcursor =>
      exact .landing_crossing childTime parentTime progress value
        landingTime nextCrossingTime hvalue hafter hfirst hnext hcrossStart
        hcrossHorizon (h.landingReadyCrossing hnext hcrossHorizon) hbefore
        hcursor
  | semantic_progress stepParent child semantic progress =>
      exact .semantic_progress stepParent child semantic progress
  | exact_replay replayParent replaySource replay =>
      exact .exact_replay replayParent replaySource replay

end

end Recaman
