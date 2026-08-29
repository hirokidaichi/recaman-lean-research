import Recaman.PermanentAboveCorridorPredecessorAdapter
import Recaman.OrbitReadyRefinedStep

namespace Recaman

noncomputable section

/-! # Crossing child generated from a below-target blocker predecessor

A below-target predecessor can restart the canonical upcrossing search at its
actual orbit clock.  The first such crossing is no later than the discharge
return already stored by the terminal certificate, hence it lies strictly
inside the existing parent horizon.  Global target-missing provenance makes
the crossing strict.

This construction also covers predecessor time zero: coordinates are needed
only at the positive post-crossing time.  The resulting node is an existing
ready crossing and therefore belongs to the refined semantic domain.  Relative
to the old crossing parent, its exact remaining obstruction is a
nondecreasing crossing predecessor anchor.
-/

/-- Numeric crossing node at the old history horizon. -/
def terminalPredecessorCrossingNode
    (parent : PhaseSearchNode) (crossingTime : Nat) : PhaseSearchNode :=
  ⟨parent.horizon, a crossingTime, .normal, a crossingTime⟩

/-- Complete ready-crossing adapter selected from a below-target predecessor. -/
structure TerminalBelowPredecessorCrossingCertificate
    {target start : Nat} {parent : PhaseSearchNode}
    {source : PermanentTailDischargeReturnCertificate target start parent}
    {freshEndpoint candidate firstTime predecessor predecessorFirstTime : Nat}
    {historical : TerminalOuterHistoricalBlockerCertificate source
      freshEndpoint candidate firstTime}
    (below : BelowTargetHistoricalPredecessorCertificate
      (predecessor := predecessor)
      (predecessorFirstTime := predecessorFirstTime) historical)
    (crossingTime quotient remainder : Nat) : Prop where
  first_crossing : FirstWeakUpcrossingStep target (firstTime - 1)
    crossingTime
  crossingTime_le_return : crossingTime ≤ source.returnTime
  ready_crossing : ReadyCrossingSearchInvariant target
    (terminalPredecessorCrossingNode parent crossingTime)

/-- The selected crossing is automatically an existing refined child. -/
theorem TerminalBelowPredecessorCrossingCertificate.refined
    {target start : Nat} {parent : PhaseSearchNode}
    {source : PermanentTailDischargeReturnCertificate target start parent}
    {freshEndpoint candidate firstTime predecessor predecessorFirstTime
      crossingTime quotient remainder : Nat}
    {historical : TerminalOuterHistoricalBlockerCertificate source
      freshEndpoint candidate firstTime}
    {below : BelowTargetHistoricalPredecessorCertificate
      (predecessor := predecessor)
      (predecessorFirstTime := predecessorFirstTime) historical}
    (h : TerminalBelowPredecessorCrossingCertificate below crossingTime
      quotient remainder) :
    OrbitReadyRefinedInvariant target
      (terminalPredecessorCrossingNode parent crossingTime) :=
  Or.inr (Or.inr h.ready_crossing.crossing)

/-- The original blocker backtrack edge remains available after selecting the
crossing child. -/
theorem TerminalBelowPredecessorCrossingCertificate.backtrack
    {target start : Nat} {parent : PhaseSearchNode}
    {source : PermanentTailDischargeReturnCertificate target start parent}
    {freshEndpoint candidate firstTime predecessor predecessorFirstTime
      crossingTime quotient remainder : Nat}
    {historical : TerminalOuterHistoricalBlockerCertificate source
      freshEndpoint candidate firstTime}
    {below : BelowTargetHistoricalPredecessorCertificate
      (predecessor := predecessor)
      (predecessorFirstTime := predecessorFirstTime) historical}
    (_h : TerminalBelowPredecessorCrossingCertificate below crossingTime
      quotient remainder) :
    TerminalHistoricalBacktrackCertificate target source.returnTime candidate
      firstTime :=
  historical.blocker.backtrackCertificate

/-- The first crossing from any below-target predecessor yields a ready
crossing at the old parent horizon.  This proof does not need coordinates at
the predecessor time, so it includes the time-zero boundary. -/
theorem BelowTargetHistoricalPredecessorCertificate.exists_crossingCertificate
    {target start : Nat} {parent : PhaseSearchNode}
    {source : PermanentTailDischargeReturnCertificate target start parent}
    {freshEndpoint candidate firstTime predecessor predecessorFirstTime : Nat}
    {historical : TerminalOuterHistoricalBlockerCertificate source
      freshEndpoint candidate firstTime}
    (h : BelowTargetHistoricalPredecessorCertificate
      (predecessor := predecessor)
      (predecessorFirstTime := predecessorFirstTime) historical) :
    ∃ crossingTime quotient remainder,
      TerminalBelowPredecessorCrossingCertificate h crossingTime quotient
        remainder := by
  have hstartBelow : a (firstTime - 1) < target := by
    rw [h.provenance.predecessor_eq]
    exact h.predecessor_below_target
  rcases exists_firstWeakUpcrossingStep_from_below
      source.combined.tail.target_positive hstartBelow with
    ⟨crossingTime, hfirst⟩
  have hcrossingLe : crossingTime ≤ source.returnTime :=
    hfirst.time_le h.future_return
  have hendpointNe : a (crossingTime + 1) ≠ target := by
    intro hequal
    exact source.combined.tail.target_missing
      ⟨crossingTime + 1, hequal⟩
  have hendpointStrict : target < a (crossingTime + 1) :=
    Nat.lt_of_le_of_ne hfirst.crossing.endpoint_ge (Ne.symm hendpointNe)
  have htargetUnseen : target ∉ valuesThrough crossingTime := by
    intro hseen
    rcases mem_valuesThrough_iff.mp hseen with
      ⟨witness, _, hvalue⟩
    exact source.combined.tail.target_missing ⟨witness, hvalue⟩
  rcases exists_coordinatesAt (n := crossingTime + 1) (by omega) with
    ⟨quotient, remainder, hcoordinates⟩
  have hcrossingBefore : crossingTime + 1 < parent.horizon :=
    Nat.lt_of_le_of_lt (Nat.add_le_add_right hcrossingLe 1)
      source.return_before_parentHorizon
  have hrecovery : CrossingRecoveryInvariant target parent.horizon
      (a (crossingTime + 1)) crossingTime quotient remainder := {
    target_missing := htargetUnseen
    forced_addition := hfirst.crossing.forced_addition
    crossing := ⟨hfirst.crossing.below, hendpointStrict,
      a_succ_of_not_canSubtract hfirst.crossing.forced_addition⟩
    coordinates := hcoordinates
    crossing_before_horizon := hcrossingBefore
    predecessor_lt_anchor :=
      Nat.lt_trans hfirst.crossing.below hendpointStrict
  }
  have hready : ReadyCrossingSearchInvariant target
      (terminalPredecessorCrossingNode parent crossingTime) := {
    crossing := ⟨a (crossingTime + 1), crossingTime, quotient, remainder, {
      target_positive := source.combined.tail.target_positive
      node_eq := rfl
      recovery := hrecovery
    }⟩
    horizon_ready := by
      simpa [terminalPredecessorCrossingNode] using
        source.combined.crossing.ready_crossing.horizon_ready
  }
  exact ⟨crossingTime, quotient, remainder, {
    first_crossing := hfirst
    crossingTime_le_return := hcrossingLe
    ready_crossing := hready
  }⟩

/-- Exact rank outcome of the new refined crossing relative to the old parent. -/
inductive TerminalBelowPredecessorCrossingRankOutcome
    {target start : Nat} {parent : PhaseSearchNode}
    {source : PermanentTailDischargeReturnCertificate target start parent}
    {freshEndpoint candidate firstTime predecessor predecessorFirstTime : Nat}
    {historical : TerminalOuterHistoricalBlockerCertificate source
      freshEndpoint candidate firstTime}
    (below : BelowTargetHistoricalPredecessorCertificate
      (predecessor := predecessor)
      (predecessorFirstTime := predecessorFirstTime) historical) : Prop
  | refined_progress
      (crossingTime quotient remainder : Nat)
      (certificate : TerminalBelowPredecessorCrossingCertificate below
        crossingTime quotient remainder)
      (progress : PhaseSearchProgress target
        (terminalPredecessorCrossingNode parent crossingTime) parent) :
      TerminalBelowPredecessorCrossingRankOutcome below
  | anchor_growth
      (crossingTime quotient remainder : Nat)
      (certificate : TerminalBelowPredecessorCrossingCertificate below
        crossingTime quotient remainder)
      (anchor_nondecreasing :
        parent.anchorParent ≤ a crossingTime) :
      TerminalBelowPredecessorCrossingRankOutcome below

/-- The below-target adapter always enters the refined crossing domain; its
rank either decreases immediately or exposes only a nondecreasing anchor. -/
theorem BelowTargetHistoricalPredecessorCertificate.crossingRankOutcome
    {target start : Nat} {parent : PhaseSearchNode}
    {source : PermanentTailDischargeReturnCertificate target start parent}
    {freshEndpoint candidate firstTime predecessor predecessorFirstTime : Nat}
    {historical : TerminalOuterHistoricalBlockerCertificate source
      freshEndpoint candidate firstTime}
    (h : BelowTargetHistoricalPredecessorCertificate
      (predecessor := predecessor)
      (predecessorFirstTime := predecessorFirstTime) historical) :
    TerminalBelowPredecessorCrossingRankOutcome h := by
  rcases h.exists_crossingCertificate with
    ⟨crossingTime, quotient, remainder, hcrossing⟩
  by_cases hdrop : a crossingTime < parent.anchorParent
  · rcases source.combined.crossing.ready_crossing.crossing with
      ⟨oldAnchor, oldTime, oldQuotient, oldRemainder, oldCertificate⟩
    have hparentAnchor : parent.anchorParent = a oldTime := by
      simpa using congrArg PhaseSearchNode.anchorParent
        oldCertificate.node_eq
    have hdrop' : a crossingTime < a oldTime := by
      rw [← hparentAnchor]
      exact hdrop
    have hprogress : PhaseSearchProgress target
        (terminalPredecessorCrossingNode parent crossingTime) parent := by
      rw [oldCertificate.node_eq]
      exact phaseSearchProgress_of_horizonAndAnchor (Nat.le_refl _) hdrop'
    exact .refined_progress crossingTime quotient remainder hcrossing
      hprogress
  · exact .anchor_growth crossingTime quotient remainder hcrossing
      (Nat.le_of_not_gt hdrop)

/-- Total refinement of the predecessor semantic classification. -/
inductive TerminalBlockerPredecessorRefinedOutcome
    {target start : Nat} {parent : PhaseSearchNode}
    {source : PermanentTailDischargeReturnCertificate target start parent}
    {freshEndpoint candidate firstTime : Nat}
    (historical : TerminalOuterHistoricalBlockerCertificate source
      freshEndpoint candidate firstTime) : Prop
  | normal_ready
      (predecessor predecessorFirstTime quotient remainder : Nat)
      (predecessor_certificate : TerminalBlockerPredecessorCertificate
        historical predecessor predecessorFirstTime)
      (invariant : NormalPhaseInvariantAt target
        ⟨firstTime - 1, predecessor, .normal, a (firstTime - 1)⟩
        (firstTime - 1) quotient remainder) :
      TerminalBlockerPredecessorRefinedOutcome historical
  | above_residual
      (predecessor predecessorFirstTime quotient remainder : Nat)
      (residual : AboveTargetPredecessorResidual
        (predecessor := predecessor)
        (predecessorFirstTime := predecessorFirstTime) historical quotient
        remainder) :
      TerminalBlockerPredecessorRefinedOutcome historical
  | crossing
      (predecessor predecessorFirstTime : Nat)
      (below : BelowTargetHistoricalPredecessorCertificate
        (predecessor := predecessor)
        (predecessorFirstTime := predecessorFirstTime) historical)
      (rank_outcome : TerminalBelowPredecessorCrossingRankOutcome below) :
      TerminalBlockerPredecessorRefinedOutcome historical

/-- The only new residual introduced by refining the below-target branch is
crossing-anchor growth; the time-zero case is already absorbed. -/
theorem TerminalOuterHistoricalBlockerCertificate.predecessorRefinedOutcome
    {target start : Nat} {parent : PhaseSearchNode}
    {source : PermanentTailDischargeReturnCertificate target start parent}
    {freshEndpoint candidate firstTime : Nat}
    (h : TerminalOuterHistoricalBlockerCertificate source freshEndpoint
      candidate firstTime) :
    TerminalBlockerPredecessorRefinedOutcome h := by
  cases h.predecessorSemanticOutcome with
  | normal_ready predecessor predecessorFirstTime quotient remainder
      predecessor_certificate invariant =>
      exact .normal_ready predecessor predecessorFirstTime quotient remainder
        predecessor_certificate invariant
  | above_residual predecessor predecessorFirstTime quotient remainder
      residual =>
      exact .above_residual predecessor predecessorFirstTime quotient remainder
        residual
  | below_historical predecessor predecessorFirstTime certificate =>
      exact .crossing predecessor predecessorFirstTime certificate
        certificate.crossingRankOutcome

end

end Recaman
