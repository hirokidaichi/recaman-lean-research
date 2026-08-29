import Recaman.PermanentAboveCycleExit

namespace Recaman

noncomputable section

/-! # Canonical rebasing normalizes the discharge kernel

After a canonical discharge return, the most immediate repair for anchor
growth or wrong chronology is to make that return crossing the next parent.
This module verifies that the rebase is semantically legitimate: it retains
the old zero-budget horizon, permanent tail, and tail-minimum certificate.

It also proves the exact limitation of this repair.  Replaying the same
historical discharge from the rebased canonical parent returns the identical
crossing.  Thus canonical rebasing normalizes every discharge certificate to
the literal stationary kernel; it does not eliminate that kernel.
-/

/-- Full typed result of rebasing a discharge certificate onto its canonical
return crossing. -/
structure CanonicalReturnRebaseCertificate
    {target start : Nat} {parent : PhaseSearchNode}
    (source : PermanentTailDischargeReturnCertificate target start parent) where
  rebased : PhaseSearchNode
  node_eq : rebased =
    ⟨parent.horizon, a source.returnTime, .normal, a source.returnTime⟩
  combined : PermanentTailCombinedCertificate target start rebased
    source.combinedMinimumTime source.combinedPredecessorFirstTime
  discharge : PermanentTailDischargeReturnCertificate target start rebased
  same_tail_start : discharge.tailStart = source.tailStart
  same_down_time : discharge.downTime = source.downTime
  same_return_time : discharge.returnTime = source.returnTime
  old_is_return : discharge.oldCrossingTime = source.returnTime
  same_anchor : a discharge.returnTime = rebased.anchorParent
  same_crossing_time : discharge.returnTime = discharge.oldCrossingTime
  stationary : CanonicalDischargeKernelResidual discharge

/-- The canonical return can be installed as a ready zero-budget crossing at
the old horizon, while preserving the old permanent-tail and minimum data. -/
theorem PermanentTailDischargeReturnCertificate.exists_canonicalReturnRebase
    {target start : Nat} {parent : PhaseSearchNode}
    (h : PermanentTailDischargeReturnCertificate target start parent) :
    Nonempty (CanonicalReturnRebaseCertificate h) := by
  have hendpointNe : a (h.returnTime + 1) ≠ target := by
    intro hequal
    exact h.combined.tail.target_missing ⟨h.returnTime + 1, hequal⟩
  have hendpointStrict : target < a (h.returnTime + 1) :=
    Nat.lt_of_le_of_ne h.return_crossing.crossing.endpoint_ge
      (Ne.symm hendpointNe)
  have htargetUnseen : target ∉ valuesThrough h.returnTime := by
    intro hseen
    rcases mem_valuesThrough_iff.mp hseen with ⟨witness, _, hvalue⟩
    exact h.combined.tail.target_missing ⟨witness, hvalue⟩
  rcases exists_coordinatesAt (n := h.returnTime + 1) (by omega) with
    ⟨quotient, remainder, hcoordinates⟩
  let rebased : PhaseSearchNode :=
    ⟨parent.horizon, a h.returnTime, .normal, a h.returnTime⟩
  have hrecovery : CrossingRecoveryInvariant target parent.horizon
      (a (h.returnTime + 1)) h.returnTime quotient remainder := {
    target_missing := htargetUnseen
    forced_addition := h.return_crossing.crossing.forced_addition
    crossing := ⟨h.return_crossing.crossing.below, hendpointStrict,
      a_succ_of_not_canSubtract
        h.return_crossing.crossing.forced_addition⟩
    coordinates := hcoordinates
    crossing_before_horizon := h.return_before_parentHorizon
    predecessor_lt_anchor :=
      Nat.lt_trans h.return_crossing.crossing.below hendpointStrict
  }
  have hready : ReadyCrossingSearchInvariant target rebased := {
    crossing := ⟨a (h.returnTime + 1), h.returnTime, quotient, remainder, {
      target_positive := h.combined.tail.target_positive
      node_eq := rfl
      recovery := hrecovery
    }⟩
    horizon_ready := by
      simpa [rebased] using
        h.combined.crossing.ready_crossing.horizon_ready
  }
  have hcrossing : PermanentTailCrossingCertificate target start rebased := {
    ready_crossing := hready
    horizon_in_tail := by
      simpa [rebased] using h.combined.crossing.horizon_in_tail
    tail_strictly_before_horizon := by
      simpa [rebased] using
        h.combined.crossing.tail_strictly_before_horizon
    budget_zero := by
      simpa [rebased] using h.combined.crossing.budget_zero
    horizon_strictly_above := by
      simpa [rebased] using h.combined.crossing.horizon_strictly_above
    no_future_downcross := by
      simpa [rebased] using h.combined.crossing.no_future_downcross
  }
  have hcombined : PermanentTailCombinedCertificate target start rebased
      h.combinedMinimumTime h.combinedPredecessorFirstTime := {
    tail := h.combined.tail
    crossing := hcrossing
    minimum := h.combined.minimum
  }
  have holdCrossing : WeakUpcrossingStep target 0 h.returnTime := {
    start_le := Nat.zero_le _
    below := h.return_crossing.crossing.below
    endpoint_ge := h.return_crossing.crossing.endpoint_ge
    forced_addition := h.return_crossing.crossing.forced_addition
  }
  let discharge : PermanentTailDischargeReturnCertificate target start
      rebased := {
    combinedMinimumTime := h.combinedMinimumTime
    combinedPredecessorFirstTime := h.combinedPredecessorFirstTime
    combined := hcombined
    tailStart := h.tailStart
    historicalMinimumTime := h.historicalMinimumTime
    historicalFirstTime := h.historicalFirstTime
    downTime := h.downTime
    returnTime := h.returnTime
    oldCrossingTime := h.returnTime
    tailStart_le_start := h.tailStart_le_start
    historical_tail := h.historical_tail
    historical_minimum := h.historical_minimum
    downcross := h.downcross
    endpoint_first := h.endpoint_first
    endpoint_before_tail := h.endpoint_before_tail
    return_crossing := h.return_crossing
    return_before_tail := h.return_before_tail
    old_crossing := holdCrossing
    old_crossing_before_horizon := by
      simpa [rebased] using h.return_before_parentHorizon
    parent_anchor_eq := by simp [rebased]
  }
  have hstationary : CanonicalDischargeKernelResidual discharge := by
    exact discharge.kernelStationary_of_oldCanonical
      discharge.return_crossing
  exact ⟨{
    rebased := rebased
    node_eq := rfl
    combined := hcombined
    discharge := discharge
    same_tail_start := rfl
    same_down_time := rfl
    same_return_time := rfl
    old_is_return := rfl
    same_anchor := rfl
    same_crossing_time := rfl
    stationary := hstationary
  }⟩

/-- Every discharge certificate, including anchor-growth and chronology
residuals, admits an unconditional normalization to the literal stationary
kernel. -/
theorem PermanentTailDischargeReturnCertificate.exists_rebasedStationaryKernel
    {target start : Nat} {parent : PhaseSearchNode}
    (h : PermanentTailDischargeReturnCertificate target start parent) :
    ∃ rebase : CanonicalReturnRebaseCertificate h,
      PermanentTailCombinedCertificate target start rebase.rebased
        h.combinedMinimumTime h.combinedPredecessorFirstTime ∧
      a rebase.discharge.returnTime = rebase.rebased.anchorParent ∧
      rebase.discharge.returnTime = rebase.discharge.oldCrossingTime ∧
      CanonicalDischargeKernelResidual rebase.discharge := by
  rcases h.exists_canonicalReturnRebase with ⟨rebase⟩
  exact ⟨rebase, rebase.combined, rebase.same_anchor,
    rebase.same_crossing_time, rebase.stationary⟩

/-- More directly, a typed rebase always exists and its replay is not a
valid exit in the cursor-refined cycle. -/
theorem PermanentTailDischargeReturnCertificate.exists_rebase_with_noCycleExit
    {target start : Nat} {parent : PhaseSearchNode}
    (h : PermanentTailDischargeReturnCertificate target start parent) :
    ∃ rebase : CanonicalReturnRebaseCertificate h,
      ¬ TailCursorCycleProgress target
        ⟨rebase.rebased.anchorParent, rebase.discharge.returnTime,
          .crossing, rebase.discharge.returnTime,
          rebase.discharge.historicalMinimumTime⟩
        ⟨rebase.rebased.anchorParent, rebase.discharge.oldCrossingTime,
          .discharge, rebase.discharge.downTime + 1,
          rebase.discharge.historicalMinimumTime⟩ := by
  rcases h.exists_canonicalReturnRebase with ⟨rebase⟩
  refine ⟨rebase, ?_⟩
  rw [← rebase.same_crossing_time]
  exact tailCursorCycle_no_stationary_exit

end

end Recaman
