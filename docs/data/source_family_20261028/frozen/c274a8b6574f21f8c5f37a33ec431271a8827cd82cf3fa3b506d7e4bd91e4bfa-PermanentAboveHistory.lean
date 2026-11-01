import Recaman.PermanentAbovePotential

namespace Recaman

/-! # Historical descent from a permanent-tail minimum

The minimum certificate points to an earlier occurrence of the value just
below the minimum.  Starting from that historical point, there are exactly
two useful global possibilities.  A later downcross consumes a fresh value
below the target and strictly decreases `missingBelowCount`.  If there is no
downcross, the historical point itself starts a new strict-above tail, whose
minimum is strictly smaller than the old one.
-/

/-- The two proof-carrying witnesses forced by one hypothetical least-missing
tail, kept over the same target and start horizon. -/
structure PermanentTailCombinedCertificate
    (target start : Nat) (crossingNode : PhaseSearchNode)
    (minimumTime predecessorFirstTime : Nat) : Prop where
  tail : MissingPermanentAboveTail target start
  crossing : PermanentTailCrossingCertificate target start crossingNode
  minimum : PermanentTailMinimumCertificate target start minimumTime
    predecessorFirstTime

/-- A completed permanent-tail certificate simultaneously supplies the
zero-budget crossing obstruction and the historical minimum blocker. -/
theorem MissingPermanentAboveTail.exists_combinedCertificate
    {target start : Nat}
    (h : MissingPermanentAboveTail target start) :
    ∃ crossingNode minimumTime predecessorFirstTime,
      PermanentTailCombinedCertificate target start crossingNode
        minimumTime predecessorFirstTime := by
  rcases h.exists_crossingCertificate with ⟨crossingNode, hcrossing⟩
  rcases h.exists_minimumCertificate with
    ⟨minimumTime, predecessorFirstTime, hminimum⟩
  exact ⟨crossingNode, minimumTime, predecessorFirstTime, {
    tail := h
    crossing := hcrossing
    minimum := hminimum
  }⟩

/-- A least missing target therefore exposes the full combined obstruction,
not just an abstract eventual-above statement. -/
theorem LeastMissingTarget.exists_permanentTailCombinedCertificate
    {target : Nat}
    (h : LeastMissingTarget target) :
    ∃ start crossingNode minimumTime predecessorFirstTime,
      PermanentTailCombinedCertificate target start crossingNode
        minimumTime predecessorFirstTime := by
  rcases h.exists_missingPermanentAboveTail with ⟨start, htail⟩
  rcases htail.exists_combinedCertificate with
    ⟨crossingNode, minimumTime, predecessorFirstTime, hcombined⟩
  exact ⟨start, crossingNode, minimumTime, predecessorFirstTime, hcombined⟩

/-- Exact next alternatives after moving from a tail minimum to the first
occurrence of its predecessor value. -/
inductive HistoricalPredecessorOutcome
    (target start minimumTime predecessorFirstTime : Nat) : Prop
  | downcross (downTime : Nat)
      (step : FutureDowncrossStep target predecessorFirstTime downTime)
      (endpoint_first : FirstAt a (a (downTime + 1)) (downTime + 1))
      (endpoint_before_tail : downTime + 1 < start)
      (budget_drop :
        missingBelowCount target (downTime + 1) <
          missingBelowCount target predecessorFirstTime) :
      HistoricalPredecessorOutcome target start minimumTime
        predecessorFirstTime
  | renewed_tail (newMinimumTime newPredecessorFirstTime : Nat)
      (tail : MissingStrictAboveTail target predecessorFirstTime)
      (minimum : PermanentTailMinimumCertificate target
        predecessorFirstTime newMinimumTime newPredecessorFirstTime)
      (minimum_value_drop : a newMinimumTime < a minimumTime) :
      HistoricalPredecessorOutcome target start minimumTime
        predecessorFirstTime

/-- The historical predecessor either leads to a fresh below-target
downcross before the old tail, or starts a renewed strict tail with a smaller
minimum.  Thus the first-occurrence bridge always exposes a concrete finite
descent, although the two branches currently live in different measures. -/
theorem PermanentTailMinimumCertificate.historicalPredecessorOutcome
    {target start minimumTime predecessorFirstTime : Nat}
    (htail : MissingStrictAboveTail target start)
    (h : PermanentTailMinimumCertificate target start minimumTime
      predecessorFirstTime) :
    HistoricalPredecessorOutcome target start minimumTime
      predecessorFirstTime := by
  by_cases hdown : ∃ downTime,
      FutureDowncrossStep target predecessorFirstTime downTime
  · rcases hdown with ⟨downTime, hstep⟩
    have hcan : CanSubtract (downTime + 1) (stateAt downTime) := by
      by_cases hcan : CanSubtract (downTime + 1) (stateAt downTime)
      · exact hcan
      · have hadd := a_succ_of_not_canSubtract hcan
        have hsource := hstep.start_at_or_above
        have hendpoint := hstep.endpoint_below
        omega
    have hfirst := firstAt_succ_of_canSubtract hcan
    have hbefore : downTime + 1 < start := by
      by_cases hbefore : downTime + 1 < start
      · exact hbefore
      · have htailValue := htail.strictly_above (downTime + 1)
          (Nat.le_of_not_gt hbefore)
        have hendpoint := hstep.endpoint_below
        omega
    exact .downcross downTime hstep hfirst hbefore
      hstep.strict_budget_drop
  · have hfirstAbove : target < a predecessorFirstTime := by
      rw [h.predecessor_first.1]
      exact h.target_lt_predecessor
    have hatOrAbove : ∀ later, predecessorFirstTime ≤ later →
        target ≤ a later :=
      (no_futureDowncross_iff_tail_atOrAbove
        (Nat.le_of_lt hfirstAbove)).mp hdown
    have hrenewed : MissingStrictAboveTail target predecessorFirstTime := {
      target_positive := htail.target_positive
      target_missing := htail.target_missing
      strictly_above := by
        intro later hlater
        have hle := hatOrAbove later hlater
        have hne : target ≠ a later := by
          intro hequal
          exact htail.target_missing ⟨later, hequal.symm⟩
        exact Nat.lt_of_le_of_ne hle hne
    }
    rcases hrenewed.exists_minimumCertificate with
      ⟨newMinimumTime, newPredecessorFirstTime, hminimum⟩
    have hnewAtFirst := hminimum.minimum.minimal predecessorFirstTime
      (Nat.le_refl _)
    have hfirstValue := h.predecessor_first.1
    have hminimumDrop : a newMinimumTime < a minimumTime := by
      omega
    exact .renewed_tail newMinimumTime newPredecessorFirstTime
      hrenewed hminimum hminimumDrop

/-- Combined-certificate wrapper for the historical dichotomy. -/
theorem PermanentTailCombinedCertificate.historicalPredecessorOutcome
    {target start : Nat} {crossingNode : PhaseSearchNode}
    {minimumTime predecessorFirstTime : Nat}
    (h : PermanentTailCombinedCertificate target start crossingNode
      minimumTime predecessorFirstTime) :
    HistoricalPredecessorOutcome target start minimumTime
      predecessorFirstTime :=
  h.minimum.historicalPredecessorOutcome h.tail.toStrictAboveTail

/-- A finite endpoint of repeatedly renewing the tail at the historical
predecessor.  The endpoint is a genuine fresh downcross before one of the
strict tails in the descending chain. -/
def HistoricalTailDowncrossCertificate
    (target originalStart : Nat) : Prop :=
  ∃ tailStart minimumTime predecessorFirstTime downTime,
    tailStart ≤ originalStart ∧
    MissingStrictAboveTail target tailStart ∧
    PermanentTailMinimumCertificate target tailStart minimumTime
      predecessorFirstTime ∧
    FutureDowncrossStep target predecessorFirstTime downTime ∧
    FirstAt a (a (downTime + 1)) (downTime + 1) ∧
    downTime + 1 < tailStart ∧
    missingBelowCount target (downTime + 1) <
      missingBelowCount target predecessorFirstTime

/-- Repeatedly taking the minimum just below a no-downcross tail cannot
continue forever: its minimum value strictly decreases.  Hence every missing
strict-above tail has an earlier predecessor whose future contains a fresh
below-target downcross and a strict history-budget drop. -/
theorem MissingStrictAboveTail.exists_historicalDowncrossCertificate
    {target originalStart : Nat}
    (h : MissingStrictAboveTail target originalStart) :
    HistoricalTailDowncrossCertificate target originalStart := by
  rcases h.exists_minimumCertificate with
    ⟨minimumTime, predecessorFirstTime, hminimum⟩
  have descend : ∀ bound tailStart currentMinimumTime currentFirstTime,
      a currentMinimumTime = bound →
      tailStart ≤ originalStart →
      MissingStrictAboveTail target tailStart →
      PermanentTailMinimumCertificate target tailStart currentMinimumTime
        currentFirstTime →
      HistoricalTailDowncrossCertificate target originalStart := by
    intro bound
    induction bound using Nat.strongRecOn with
    | ind bound ih =>
        intro tailStart currentMinimumTime currentFirstTime hvalue
          htailStart htail hcertificate
        cases hcertificate.historicalPredecessorOutcome htail with
        | downcross downTime hstep hfirst hbefore hbudget =>
            exact ⟨tailStart, currentMinimumTime, currentFirstTime,
              downTime, htailStart, htail, hcertificate, hstep, hfirst,
              hbefore, hbudget⟩
        | renewed_tail newMinimumTime newFirstTime hrenewed hnewMinimum
            hminimumDrop =>
            have hnewBound : a newMinimumTime < bound := by
              omega
            have hnewStart : currentFirstTime ≤ originalStart :=
              Nat.le_trans
                (Nat.le_of_lt hcertificate.firstTime_before_tail)
                htailStart
            exact ih (a newMinimumTime) hnewBound currentFirstTime
              newMinimumTime newFirstTime rfl hnewStart hrenewed hnewMinimum
  exact descend (a minimumTime) originalStart minimumTime
    predecessorFirstTime rfl (Nat.le_refl _) h hminimum

/-- Completed-history wrapper for the finite historical downcross theorem. -/
theorem MissingPermanentAboveTail.exists_historicalDowncrossCertificate
    {target start : Nat}
    (h : MissingPermanentAboveTail target start) :
    HistoricalTailDowncrossCertificate target start :=
  h.toStrictAboveTail.exists_historicalDowncrossCertificate

/-- In a completed-history permanent tail, the finite descent above starts
at a genuinely positive historical budget and ends before the zero-budget
tail horizon.  This identifies an actual budget-consumption event separating
the historical blocker from the final crossing obstruction. -/
theorem MissingPermanentAboveTail.exists_positiveBudget_historicalDowncross
    {target start : Nat}
    (h : MissingPermanentAboveTail target start) :
    ∃ predecessorFirstTime downTime,
      FutureDowncrossStep target predecessorFirstTime downTime ∧
      FirstAt a (a (downTime + 1)) (downTime + 1) ∧
      downTime + 1 < start ∧
      0 < missingBelowCount target predecessorFirstTime ∧
      missingBelowCount target start = 0 := by
  rcases h.exists_historicalDowncrossCertificate with
    ⟨tailStart, minimumTime, predecessorFirstTime, downTime,
      htailStart, htail, hminimum, hdown, hfirst, hbefore, hbudget⟩
  have hbeforeStart : downTime + 1 < start :=
    Nat.lt_of_lt_of_le hbefore htailStart
  have hpositiveBudget :
      0 < missingBelowCount target predecessorFirstTime := by
    omega
  exact ⟨predecessorFirstTime, downTime, hdown, hfirst, hbeforeStart,
    hpositiveBudget, h.budget_zero⟩

/-- Exact residual when the upcrossing reconstructed after the historical
downcross does not lower the combined certificate's zero-budget crossing
anchor. -/
inductive HistoricalCycleGrowthResidual
    (target : Nat) (parent : PhaseSearchNode) : Prop
  | intro (predecessorFirstTime downTime crossingTime : Nat)
      (child : PhaseSearchNode)
      (downcross : FutureDowncrossStep target predecessorFirstTime downTime)
      (upcross : WeakUpcrossingStep target (downTime + 1) crossingTime)
      (ready_crossing : ReadyCrossingSearchInvariant target child)
      (same_horizon : child.horizon = parent.horizon)
      (anchor_nondecreasing : parent.anchorParent ≤ child.anchorParent)
      (no_progress : ¬ PhaseSearchProgress target child parent) :
      HistoricalCycleGrowthResidual target parent

/-- Reconstruct a strict upcrossing after the finite historical downcross and
place it at the same zero-budget horizon as the combined crossing.  A strict
anchor drop gives a valid refined crossing child.  The only remaining case
is the literal same-budget anchor-growth residual. -/
theorem PermanentTailCombinedCertificate.refinedStep_or_historicalCycleGrowth
    {target start : Nat} {parent : PhaseSearchNode}
    {minimumTime predecessorFirstTime : Nat}
    (h : PermanentTailCombinedCertificate target start parent minimumTime
      predecessorFirstTime) :
    (∃ child, OrbitReadyRefinedInvariant target child ∧
      PhaseSearchProgress target child parent) ∨
      HistoricalCycleGrowthResidual target parent := by
  rcases h.tail.exists_historicalDowncrossCertificate with
    ⟨tailStart, historicalMinimumTime, historicalFirstTime, downTime,
      htailStart, hhistoricalTail, hhistoricalMinimum, hdown, hdownFirst,
      hdownBefore, hbudgetDrop⟩
  have hfinishAbove := hhistoricalTail.strictly_above tailStart
    (Nat.le_refl _)
  rcases exists_weakUpcrossingStep_between
      (Nat.le_of_lt hdownBefore) hdown.endpoint_below
      (Nat.le_of_lt hfinishAbove) with
    ⟨crossingTime, hupcross, hupcrossBound⟩
  have hendpointNe : a (crossingTime + 1) ≠ target := by
    intro hequal
    exact h.tail.target_missing ⟨crossingTime + 1, hequal⟩
  have hendpointStrict : target < a (crossingTime + 1) :=
    Nat.lt_of_le_of_ne hupcross.endpoint_ge (Ne.symm hendpointNe)
  have htargetUnseen : target ∉ valuesThrough crossingTime := by
    intro hseen
    rcases mem_valuesThrough_iff.mp hseen with ⟨witness, _, hvalue⟩
    exact h.tail.target_missing ⟨witness, hvalue⟩
  rcases exists_coordinatesAt (n := crossingTime + 1) (by omega) with
    ⟨quotient, remainder, hcoordinates⟩
  let child : PhaseSearchNode :=
    ⟨parent.horizon, a crossingTime, .normal, a crossingTime⟩
  have hcrossingBefore : crossingTime + 1 < parent.horizon := by
    exact Nat.lt_of_le_of_lt hupcrossBound
      (Nat.lt_of_le_of_lt htailStart
        h.crossing.tail_strictly_before_horizon)
  have hrecovery : CrossingRecoveryInvariant target parent.horizon
      (a (crossingTime + 1)) crossingTime quotient remainder := {
    target_missing := htargetUnseen
    forced_addition := hupcross.forced_addition
    crossing := ⟨hupcross.below, hendpointStrict,
      a_succ_of_not_canSubtract hupcross.forced_addition⟩
    coordinates := hcoordinates
    crossing_before_horizon := hcrossingBefore
    predecessor_lt_anchor := Nat.lt_trans hupcross.below hendpointStrict
  }
  have hchildReady : ReadyCrossingSearchInvariant target child := {
    crossing := ⟨a (crossingTime + 1), crossingTime, quotient, remainder, {
      target_positive := h.tail.target_positive
      node_eq := rfl
      recovery := hrecovery
    }⟩
    horizon_ready := by
      simpa [child] using h.crossing.ready_crossing.horizon_ready
  }
  by_cases hanchorDrop : child.anchorParent < parent.anchorParent
  · left
    refine ⟨child, Or.inr (Or.inr hchildReady.crossing), ?_⟩
    rcases h.crossing.ready_crossing.crossing with
      ⟨oldAnchor, parentTime, parentQuotient, parentRemainder,
        hparentCertificate⟩
    have hanchorDrop' : a crossingTime < a parentTime := by
      have hparentAnchor : parent.anchorParent = a parentTime := by
        simpa using congrArg PhaseSearchNode.anchorParent
          hparentCertificate.node_eq
      simpa [child, hparentAnchor] using hanchorDrop
    have hprogress := phaseSearchProgress_of_horizonAndAnchor
      (target := target)
      (childHorizon := parent.horizon)
      (parentHorizon := parent.horizon)
      (childAnchor := a crossingTime)
      (parentAnchor := a parentTime)
      (childLocal := a crossingTime)
      (parentLocal := a parentTime)
      (Nat.le_refl _) hanchorDrop'
    rw [hparentCertificate.node_eq]
    simpa [child] using hprogress
  · right
    have hanchorGrowth : parent.anchorParent ≤ child.anchorParent :=
      Nat.le_of_not_gt hanchorDrop
    have hnoProgress : ¬ PhaseSearchProgress target child parent := by
      intro hprogress
      have hforcedDrop := crossing_zeroBudget_progress_forces_anchorDrop
        h.crossing.ready_crossing.crossing h.crossing.budget_zero
        hchildReady.crossing hprogress
      exact hanchorDrop hforcedDrop.2
    exact .intro historicalFirstTime downTime crossingTime child hdown
      hupcross hchildReady rfl hanchorGrowth hnoProgress

/-- The historical-cycle residual is not merely an interface possibility.
For every missing permanent tail, choose as parent the very upcrossing
reconstructed after the finite historical downcross.  Replaying that cycle
then returns the same numeric crossing node, with equal anchor and no rank
progress.  A proof must therefore constrain crossing selection or add a
genuinely new measure; this one-cycle construction cannot be iterated in the
current rank. -/
theorem MissingPermanentAboveTail.exists_stationaryHistoricalCycleResidual
    {target start : Nat}
    (h : MissingPermanentAboveTail target start) :
    ∃ parent minimumTime predecessorFirstTime,
      PermanentTailCombinedCertificate target start parent minimumTime
        predecessorFirstTime ∧
      HistoricalCycleGrowthResidual target parent := by
  rcases h.exists_historicalDowncrossCertificate with
    ⟨tailStart, historicalMinimumTime, historicalFirstTime, downTime,
      htailStart, hhistoricalTail, hhistoricalMinimum, hdown, hdownFirst,
      hdownBefore, hbudgetDrop⟩
  have hfinishAbove := hhistoricalTail.strictly_above tailStart
    (Nat.le_refl _)
  rcases exists_weakUpcrossingStep_between
      (Nat.le_of_lt hdownBefore) hdown.endpoint_below
      (Nat.le_of_lt hfinishAbove) with
    ⟨crossingTime, hupcross, hupcrossBound⟩
  have hendpointNe : a (crossingTime + 1) ≠ target := by
    intro hequal
    exact h.target_missing ⟨crossingTime + 1, hequal⟩
  have hendpointStrict : target < a (crossingTime + 1) :=
    Nat.lt_of_le_of_ne hupcross.endpoint_ge (Ne.symm hendpointNe)
  have htargetUnseen : target ∉ valuesThrough crossingTime := by
    intro hseen
    rcases mem_valuesThrough_iff.mp hseen with ⟨witness, _, hvalue⟩
    exact h.target_missing ⟨witness, hvalue⟩
  rcases exists_coordinatesAt (n := crossingTime + 1) (by omega) with
    ⟨quotient, remainder, hcoordinates⟩
  let horizon := max (start + 1) target
  let parent : PhaseSearchNode :=
    ⟨horizon, a crossingTime, .normal, a crossingTime⟩
  have hstartHorizon : start ≤ horizon := by
    exact Nat.le_trans (by omega) (Nat.le_max_left _ _)
  have hstartBeforeHorizon : start < horizon := by
    exact Nat.lt_of_lt_of_le (by omega) (Nat.le_max_left _ _)
  have hcrossingBefore : crossingTime + 1 < horizon := by
    exact Nat.lt_of_le_of_lt hupcrossBound
      (Nat.lt_of_le_of_lt htailStart hstartBeforeHorizon)
  have hrecovery : CrossingRecoveryInvariant target horizon
      (a (crossingTime + 1)) crossingTime quotient remainder := {
    target_missing := htargetUnseen
    forced_addition := hupcross.forced_addition
    crossing := ⟨hupcross.below, hendpointStrict,
      a_succ_of_not_canSubtract hupcross.forced_addition⟩
    coordinates := hcoordinates
    crossing_before_horizon := hcrossingBefore
    predecessor_lt_anchor := Nat.lt_trans hupcross.below hendpointStrict
  }
  have hready : ReadyCrossingSearchInvariant target parent := {
    crossing := ⟨a (crossingTime + 1), crossingTime, quotient, remainder, {
      target_positive := h.target_positive
      node_eq := rfl
      recovery := hrecovery
    }⟩
    horizon_ready := by
      change target ≤ horizon + 1
      have htargetHorizon : target ≤ horizon := by
        simpa only [horizon] using Nat.le_max_right (start + 1) target
      omega
  }
  have hbudgetLe := missingBelowCount_antitone
    (m := target) hstartHorizon
  have hbudget : missingBelowCount target horizon = 0 := by
    rw [h.budget_zero] at hbudgetLe
    omega
  have hhorizonAbove := h.strictly_above horizon hstartHorizon
  have hnoDowncross : ¬ ∃ time,
      FutureDowncrossStep target horizon time := by
    apply (no_futureDowncross_iff_tail_atOrAbove
      (Nat.le_of_lt hhorizonAbove)).mpr
    intro time htime
    exact Nat.le_of_lt (h.strictly_above time
      (Nat.le_trans hstartHorizon htime))
  have hcrossingCertificate :
      PermanentTailCrossingCertificate target start parent := {
    ready_crossing := hready
    horizon_in_tail := hstartHorizon
    tail_strictly_before_horizon := hstartBeforeHorizon
    budget_zero := hbudget
    horizon_strictly_above := hhorizonAbove
    no_future_downcross := hnoDowncross
  }
  rcases h.exists_minimumCertificate with
    ⟨minimumTime, predecessorFirstTime, hminimum⟩
  have hcombined : PermanentTailCombinedCertificate target start parent
      minimumTime predecessorFirstTime := {
    tail := h
    crossing := hcrossingCertificate
    minimum := hminimum
  }
  have hnoProgress : ¬ PhaseSearchProgress target parent parent := by
    intro hprogress
    have hdrop := crossing_zeroBudget_progress_forces_anchorDrop
      hready.crossing hbudget hready.crossing hprogress
    exact Nat.lt_irrefl _ hdrop.2
  have hresidual : HistoricalCycleGrowthResidual target parent :=
    .intro historicalFirstTime downTime crossingTime parent hdown hupcross
      hready rfl (Nat.le_refl _) hnoProgress
  exact ⟨parent, minimumTime, predecessorFirstTime, hcombined, hresidual⟩

end Recaman
