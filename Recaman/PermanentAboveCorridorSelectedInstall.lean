import Recaman.PermanentAboveCorridorAnchorCandidates

namespace Recaman

noncomputable section

/-! # Installing the selected predecessor crossing as the next parent

The selected crossing node reuses the old history horizon.  Therefore every
permanent-tail field independent of the crossing witness transports directly:
tail membership, zero missing budget, strict height at the horizon, absence of
future downcrosses, and the historical minimum certificate.

The broad combined certificate hides its crossing time existentially.  To
iterate the cursor ranks without losing that time, this module also constructs
the next discharge certificate directly and fixes its `oldCrossingTime` to
the selected crossing.  The only remaining iteration split is chronological:
whether the next historical downcross endpoint precedes that selected time.
-/

/-- Full semantic installation of a selected predecessor crossing. -/
structure TerminalSelectedCrossingInstallCertificate
    {target start : Nat} {parent : PhaseSearchNode}
    {source : PermanentTailDischargeReturnCertificate target start parent}
    {freshEndpoint candidate firstTime predecessor predecessorFirstTime
      crossingTime quotient remainder : Nat}
    {historical : TerminalOuterHistoricalBlockerCertificate source
      freshEndpoint candidate firstTime}
    {below : BelowTargetHistoricalPredecessorCertificate
      (predecessor := predecessor)
      (predecessorFirstTime := predecessorFirstTime) historical}
    (crossing : TerminalBelowPredecessorCrossingCertificate below crossingTime
      quotient remainder) : Prop where
  permanent_crossing : PermanentTailCrossingCertificate target start
    (terminalPredecessorCrossingNode parent crossingTime)
  combined : PermanentTailCombinedCertificate target start
    (terminalPredecessorCrossingNode parent crossingTime)
    source.combinedMinimumTime source.combinedPredecessorFirstTime
  same_horizon :
    (terminalPredecessorCrossingNode parent crossingTime).horizon =
      parent.horizon
  selected_anchor :
    (terminalPredecessorCrossingNode parent crossingTime).anchorParent =
      a crossingTime

/-- All permanent-tail semantics transport because the selected node changes
only the crossing predecessor anchor at the same horizon. -/
theorem TerminalBelowPredecessorCrossingCertificate.install
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
    TerminalSelectedCrossingInstallCertificate h := by
  let installed :=
    terminalPredecessorCrossingNode parent crossingTime
  have hpermanent : PermanentTailCrossingCertificate target start
      installed := {
    ready_crossing := h.ready_crossing
    horizon_in_tail := by
      simpa [installed, terminalPredecessorCrossingNode] using
        source.combined.crossing.horizon_in_tail
    tail_strictly_before_horizon := by
      simpa [installed, terminalPredecessorCrossingNode] using
        source.combined.crossing.tail_strictly_before_horizon
    budget_zero := by
      simpa [installed, terminalPredecessorCrossingNode] using
        source.combined.crossing.budget_zero
    horizon_strictly_above := by
      simpa [installed, terminalPredecessorCrossingNode] using
        source.combined.crossing.horizon_strictly_above
    no_future_downcross := by
      simpa [installed, terminalPredecessorCrossingNode] using
        source.combined.crossing.no_future_downcross
  }
  have hcombined : PermanentTailCombinedCertificate target start installed
      source.combinedMinimumTime source.combinedPredecessorFirstTime := {
    tail := source.combined.tail
    crossing := hpermanent
    minimum := source.combined.minimum
  }
  exact {
    permanent_crossing := hpermanent
    combined := hcombined
    same_horizon := rfl
    selected_anchor := rfl
  }

/-- A next discharge whose old crossing witness is definitionally the
selected predecessor crossing, rather than an arbitrary existential witness
with the same numeric node. -/
structure TerminalSelectedCrossingDischargeCertificate
    {target start : Nat} {parent : PhaseSearchNode}
    {source : PermanentTailDischargeReturnCertificate target start parent}
    {freshEndpoint candidate firstTime predecessor predecessorFirstTime
      crossingTime quotient remainder : Nat}
    {historical : TerminalOuterHistoricalBlockerCertificate source
      freshEndpoint candidate firstTime}
    {below : BelowTargetHistoricalPredecessorCertificate
      (predecessor := predecessor)
      (predecessorFirstTime := predecessorFirstTime) historical}
    {crossing : TerminalBelowPredecessorCrossingCertificate below crossingTime
      quotient remainder}
    (install : TerminalSelectedCrossingInstallCertificate crossing) where
  discharge : PermanentTailDischargeReturnCertificate target start
    (terminalPredecessorCrossingNode parent crossingTime)
  old_crossing_time_eq : discharge.oldCrossingTime = crossingTime
  old_anchor_eq :
    (terminalPredecessorCrossingNode parent crossingTime).anchorParent =
      a discharge.oldCrossingTime

/-- Re-run the historical discharge construction while retaining the selected
crossing time as typed provenance. -/
theorem TerminalSelectedCrossingInstallCertificate.exists_nextDischarge
    {target start : Nat} {parent : PhaseSearchNode}
    {source : PermanentTailDischargeReturnCertificate target start parent}
    {freshEndpoint candidate firstTime predecessor predecessorFirstTime
      crossingTime quotient remainder : Nat}
    {historical : TerminalOuterHistoricalBlockerCertificate source
      freshEndpoint candidate firstTime}
    {below : BelowTargetHistoricalPredecessorCertificate
      (predecessor := predecessor)
      (predecessorFirstTime := predecessorFirstTime) historical}
    {crossing : TerminalBelowPredecessorCrossingCertificate below crossingTime
      quotient remainder}
    (h : TerminalSelectedCrossingInstallCertificate crossing) :
    Nonempty (TerminalSelectedCrossingDischargeCertificate h) := by
  rcases h.combined.tail.exists_historicalDowncrossCertificate with
    ⟨tailStart, historicalMinimumTime, historicalFirstTime, downTime,
      htailStart, hhistoricalTail, hhistoricalMinimum, hdown, hendpointFirst,
      hendpointBefore, hbudgetDrop⟩
  rcases exists_firstWeakUpcrossingStep_from_below
      h.combined.tail.target_positive hdown.endpoint_below with
    ⟨returnTime, hreturn⟩
  have htailAbove := hhistoricalTail.strictly_above tailStart
    (Nat.le_refl _)
  rcases exists_weakUpcrossingStep_between
      (Nat.le_of_lt hendpointBefore) hdown.endpoint_below
      (Nat.le_of_lt htailAbove) with
    ⟨witnessTime, hwitness, hwitnessBefore⟩
  have hreturnBefore :=
    hreturn.endpoint_le_of_witness hwitness hwitnessBefore
  have holdCrossing : WeakUpcrossingStep target 0 crossingTime := {
    start_le := Nat.zero_le _
    below := crossing.first_crossing.crossing.below
    endpoint_ge := crossing.first_crossing.crossing.endpoint_ge
    forced_addition := crossing.first_crossing.crossing.forced_addition
  }
  have hcrossingBefore : crossingTime + 1 < parent.horizon :=
    Nat.lt_of_le_of_lt
      (Nat.add_le_add_right crossing.crossingTime_le_return 1)
      source.return_before_parentHorizon
  let discharge : PermanentTailDischargeReturnCertificate target start
      (terminalPredecessorCrossingNode parent crossingTime) := {
    combinedMinimumTime := source.combinedMinimumTime
    combinedPredecessorFirstTime := source.combinedPredecessorFirstTime
    combined := h.combined
    tailStart := tailStart
    historicalMinimumTime := historicalMinimumTime
    historicalFirstTime := historicalFirstTime
    downTime := downTime
    returnTime := returnTime
    oldCrossingTime := crossingTime
    tailStart_le_start := htailStart
    historical_tail := hhistoricalTail
    historical_minimum := hhistoricalMinimum
    downcross := hdown
    endpoint_first := hendpointFirst
    endpoint_before_tail := hendpointBefore
    return_crossing := hreturn
    return_before_tail := hreturnBefore
    old_crossing := holdCrossing
    old_crossing_before_horizon := by
      simpa [terminalPredecessorCrossingNode] using hcrossingBefore
    parent_anchor_eq := rfl
  }
  exact ⟨{
    discharge := discharge
    old_crossing_time_eq := rfl
    old_anchor_eq := rfl
  }⟩

/-- Exact chronology boundary for applying the eligible restart theorem on
the next installed cycle. -/
inductive TerminalSelectedCrossingIterationChronology
    {target start : Nat} {parent : PhaseSearchNode}
    {source : PermanentTailDischargeReturnCertificate target start parent}
    {freshEndpoint candidate firstTime predecessor predecessorFirstTime
      crossingTime quotient remainder : Nat}
    {historical : TerminalOuterHistoricalBlockerCertificate source
      freshEndpoint candidate firstTime}
    {below : BelowTargetHistoricalPredecessorCertificate
      (predecessor := predecessor)
      (predecessorFirstTime := predecessorFirstTime) historical}
    {crossing : TerminalBelowPredecessorCrossingCertificate below crossingTime
      quotient remainder}
    {install : TerminalSelectedCrossingInstallCertificate crossing}
    (next : TerminalSelectedCrossingDischargeCertificate install) : Prop
  | eligible
      (endpoint_le_selected :
        next.discharge.downTime + 1 ≤ crossingTime) :
      TerminalSelectedCrossingIterationChronology next
  | mismatch
      (selected_before_endpoint :
        crossingTime < next.discharge.downTime + 1) :
      TerminalSelectedCrossingIterationChronology next

theorem TerminalSelectedCrossingDischargeCertificate.chronology
    {target start : Nat} {parent : PhaseSearchNode}
    {source : PermanentTailDischargeReturnCertificate target start parent}
    {freshEndpoint candidate firstTime predecessor predecessorFirstTime
      crossingTime quotient remainder : Nat}
    {historical : TerminalOuterHistoricalBlockerCertificate source
      freshEndpoint candidate firstTime}
    {below : BelowTargetHistoricalPredecessorCertificate
      (predecessor := predecessor)
      (predecessorFirstTime := predecessorFirstTime) historical}
    {crossing : TerminalBelowPredecessorCrossingCertificate below crossingTime
      quotient remainder}
    {install : TerminalSelectedCrossingInstallCertificate crossing}
    (h : TerminalSelectedCrossingDischargeCertificate install) :
    TerminalSelectedCrossingIterationChronology h := by
  by_cases heligible : h.discharge.downTime + 1 ≤ crossingTime
  · exact .eligible heligible
  · exact .mismatch (Nat.lt_of_not_ge heligible)

/-- A finite anchor-growth edge survives installation as a relation between
the old and installed semantic parent anchors. -/
theorem TerminalCrossingAnchorGrowthCertificate.installedProgress
    {target start : Nat} {parent : PhaseSearchNode}
    {source : PermanentTailDischargeReturnCertificate target start parent}
    {freshEndpoint candidate firstTime predecessor predecessorFirstTime
      crossingTime quotient remainder : Nat}
    {historical : TerminalOuterHistoricalBlockerCertificate source
      freshEndpoint candidate firstTime}
    {below : BelowTargetHistoricalPredecessorCertificate
      (predecessor := predecessor)
      (predecessorFirstTime := predecessorFirstTime) historical}
    {crossing : TerminalBelowPredecessorCrossingCertificate below crossingTime
      quotient remainder}
    (h : TerminalCrossingAnchorGrowthCertificate crossing) :
    TerminalCrossingAnchorProgress target
      (terminalPredecessorCrossingNode parent crossingTime).anchorParent
      parent.anchorParent := by
  simpa [terminalPredecessorCrossingNode] using h.gap_progress

end

end Recaman
