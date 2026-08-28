import Recaman.CrossingTailRefined
import Recaman.ReadyCurrentDebt

namespace Recaman

/-! # Local dynamics of a permanent above-target tail

If the orbit remains strictly above a positive target, every actual tail
state exposes a value-decreasing `CoverageStep` in at most two transitions.
A legal subtraction already lands at or above the target.  A forced addition
has a universal follow-up candidate: at the next step it is exactly one less
than the value before the addition.  Legal subtraction makes that candidate
fresh; another forced addition says it was already seen.  Either branch gives
a first occurrence below the original value.
-/

/-- A forced addition from a value strictly above a positive target exposes
coverage one transition later.  No coordinate or quotient assumption is
needed: the follow-up subtraction candidate is always `a n - 1`. -/
theorem forcedAddition_above_twoStep_coverage
    {target n : Nat}
    (htarget : 0 < target)
    (habove : target < a n)
    (hforced : ¬ CanSubtract (n + 1) (stateAt n)) :
    CoverageStep target (a n) n := by
  have hnext := a_succ_of_not_canSubtract hforced
  let candidate := a n - 1
  have hcandidate : a (n + 1) - (n + 2) = candidate := by
    simp only [candidate]
    omega
  have htargetCandidate : target ≤ candidate := by
    simp only [candidate]
    omega
  have hcandidateDrop : candidate < a n := by
    simp only [candidate]
    omega
  have hpositive : n + 2 < a (n + 1) := by
    omega
  by_cases hcanNext : CanSubtract (n + 2) (stateAt (n + 1))
  · have hnextNext := a_succ_of_canSubtract hcanNext
    have hvalueNext : a (n + 2) = candidate :=
      hnextNext.trans hcandidate
    have hfirstCandidate := firstAt_succ_of_canSubtract hcanNext
    exact Or.inr ⟨candidate, n + 2, htargetCandidate,
      by simpa [hvalueNext] using hfirstCandidate, hcandidateDrop⟩
  · rcases not_canSubtract_cases hcanNext with hnonpositive | hseen
    · exact False.elim (by omega)
    · have hcandidateSeen : candidate ∈ valuesThrough (n + 1) := by
        simpa only [hcandidate] using hseen
      rcases history_member_has_firstAt hcandidateSeen with
        ⟨firstTime, _, hfirstCandidate⟩
      exact Or.inr ⟨candidate, firstTime, htargetCandidate,
        hfirstCandidate, hcandidateDrop⟩

/-- Every state of a strictly above-target tail has a `CoverageStep` after
at most two real transitions. -/
theorem strictAboveTail_coverageStep
    {target start n : Nat}
    (htarget : 0 < target)
    (htail : ∀ time, start ≤ time → target < a time)
    (htime : start ≤ n) :
    CoverageStep target (a n) n := by
  by_cases hcan : CanSubtract (n + 1) (stateAt n)
  · exact subtraction_gives_coverageStep hcan
      (Nat.le_of_lt (htail (n + 1) (by omega)))
  · exact forcedAddition_above_twoStep_coverage htarget
      (htail n htime) hcan

/-- Proof-carrying form of the eventual behavior forced by a hypothetical
least missing target. -/
structure MissingPermanentAboveTail (target start : Nat) : Prop where
  target_positive : 0 < target
  target_missing : ¬ ∃ time, a time = target
  below_covered : ∀ value, value < target →
    value ∈ valuesThrough start
  strictly_above : ∀ time, start ≤ time → target < a time

/-- A least missing target supplies a permanent above-tail certificate at a
finite history horizon. -/
theorem LeastMissingTarget.exists_missingPermanentAboveTail
    {target : Nat} (h : LeastMissingTarget target) :
    ∃ start, MissingPermanentAboveTail target start := by
  have htargetPositive : 0 < target := by
    by_cases hzero : target = 0
    · subst target
      exact False.elim (h.target_missing ⟨0, rfl⟩)
    · omega
  rcases h.eventually_strictlyAbove with
    ⟨start, hcovered, habove⟩
  exact ⟨start, {
    target_positive := htargetPositive
    target_missing := h.target_missing
    below_covered := hcovered
    strictly_above := habove
  }⟩

/-- Every actual state in a certified missing-target tail has a local
value-decreasing coverage witness. -/
theorem MissingPermanentAboveTail.coverageStep_at
    {target start n : Nat}
    (h : MissingPermanentAboveTail target start)
    (htime : start ≤ n) :
    CoverageStep target (a n) n :=
  strictAboveTail_coverageStep h.target_positive h.strictly_above htime

/-- Once the tail clock is target-ready, its two-step coverage witness enters
the existing ready current/debt domain.  This is local closure at the tail
state; it does not by itself transport a rank edge back to an earlier
crossing node. -/
theorem MissingPermanentAboveTail.readyCurrentOrDebtStep_at
    {target start n : Nat}
    (h : MissingPermanentAboveTail target start)
    (htime : start ≤ n)
    (hclock : target ≤ n + 1) :
    ∃ child, ReadyCurrentOrDebtInvariant target child ∧
      PhaseSearchProgress target child (targetStartNode n) := by
  have hparent : CurrentCoverageParentCertificate target n := {
    target_positive := h.target_positive
    time_ready := hclock
    target_le_value := Nat.le_of_lt (h.strictly_above n htime)
  }
  rcases coverageStep_readyCurrentOrDebt hparent
      (h.coverageStep_at htime) with hoccurs | hchild
  · exact False.elim (h.target_missing hoccurs)
  · exact hchild

/-- Covering every value below a target is exactly enough to exhaust the
outer history budget used by the phase-search rank. -/
theorem missingBelowCount_eq_zero_of_belowCovered
    {target horizon : Nat}
    (hcovered : ∀ value, value < target →
      value ∈ valuesThrough horizon) :
    missingBelowCount target horizon = 0 := by
  induction target with
  | zero => rfl
  | succ target ih =>
      have hsmaller : ∀ value, value < target →
          value ∈ valuesThrough horizon := by
        intro value hvalue
        exact hcovered value (by omega)
      have htop : target ∈ valuesThrough horizon :=
        hcovered target (by omega)
      simp [missingBelowCount, ih hsmaller, htop]

/-- A missing permanent-above tail begins after the history rank's outer
budget has already reached its absolute minimum. -/
theorem MissingPermanentAboveTail.budget_zero
    {target start : Nat}
    (h : MissingPermanentAboveTail target start) :
    missingBelowCount target start = 0 :=
  missingBelowCount_eq_zero_of_belowCovered h.below_covered

/-- At zero history budget a crossing node cannot exit to any non-crossing
refined node.  Such an exit would have to make the natural-valued budget
strictly smaller than zero. -/
theorem crossing_zeroBudget_no_nonCrossing_progress
    {target : Nat} {parent child : PhaseSearchNode}
    (hparent : CrossingSearchInvariant target parent)
    (hbudget : missingBelowCount target parent.horizon = 0)
    (hchild : RefinedNonCrossingInvariant target child) :
    ¬ PhaseSearchProgress target child parent := by
  intro hprogress
  have hdrop := crossing_to_nonCrossing_progress_forces_budgetDrop
    hparent hchild hprogress
  rw [hbudget] at hdrop
  omega

/-- Between crossing nodes, zero outer budget leaves the below-target anchor
as the only rank component which can decrease. -/
theorem crossing_zeroBudget_progress_forces_anchorDrop
    {target : Nat} {parent child : PhaseSearchNode}
    (hparent : CrossingSearchInvariant target parent)
    (hbudget : missingBelowCount target parent.horizon = 0)
    (hchild : CrossingSearchInvariant target child)
    (hprogress : PhaseSearchProgress target child parent) :
    missingBelowCount target child.horizon = 0 ∧
      child.anchorParent < parent.anchorParent := by
  rcases hparent with
    ⟨oldAnchor, parentTime, parentQuotient, parentRemainder,
      hparentCertificate⟩
  rcases hchild with
    ⟨childOldAnchor, childTime, childQuotient, childRemainder,
      hchildCertificate⟩
  have hparentAnchor : parent.anchorParent = a parentTime := by
    simpa using congrArg PhaseSearchNode.anchorParent
      hparentCertificate.node_eq
  have hchildAnchor : child.anchorParent = a childTime := by
    simpa using congrArg PhaseSearchNode.anchorParent
      hchildCertificate.node_eq
  have hshape :
      missingBelowCount target child.horizon <
          missingBelowCount target parent.horizon ∨
        (missingBelowCount target child.horizon =
            missingBelowCount target parent.horizon ∧
          a childTime < a parentTime) := by
    rw [hparentCertificate.node_eq, hchildCertificate.node_eq] at hprogress
    exact crossingNumeric_progress_iff_budgetDrop_or_anchorDrop.mp hprogress
  rcases hshape with hdrop | ⟨hequal, hanchor⟩
  · rw [hbudget] at hdrop
    exact False.elim (by omega)
  · refine ⟨hequal.trans hbudget, ?_⟩
    rw [hchildAnchor, hparentAnchor]
    exact hanchor

/-- A crossing node located inside a certified missing tail is therefore
rank-trapped in the crossing component: every refined successor must itself
be another crossing. -/
theorem MissingPermanentAboveTail.crossing_refinedChild_is_crossing
    {target start : Nat}
    (h : MissingPermanentAboveTail target start)
    {parent child : PhaseSearchNode}
    (hparent : CrossingSearchInvariant target parent)
    (hhorizon : start ≤ parent.horizon)
    (hchild : OrbitReadyRefinedInvariant target child)
    (hprogress : PhaseSearchProgress target child parent) :
    CrossingSearchInvariant target child := by
  have hbudgetStart := h.budget_zero
  have hbudgetLe := missingBelowCount_antitone
    (m := target) hhorizon
  have hbudgetParent : missingBelowCount target parent.horizon = 0 := by
    omega
  rcases crossing_refinedChild_budgetDrop_or_crossing hparent hchild
      hprogress with hdrop | hcrossing
  · rw [hbudgetParent] at hdrop
    exact False.elim (by omega)
  · exact hcrossing

/-- Full zero-budget shape of any refined successor inside a missing tail:
it remains crossing, keeps budget zero, and strictly lowers the crossing
anchor. -/
theorem MissingPermanentAboveTail.crossing_refinedChild_shape
    {target start : Nat}
    (h : MissingPermanentAboveTail target start)
    {parent child : PhaseSearchNode}
    (hparent : CrossingSearchInvariant target parent)
    (hhorizon : start ≤ parent.horizon)
    (hchild : OrbitReadyRefinedInvariant target child)
    (hprogress : PhaseSearchProgress target child parent) :
    CrossingSearchInvariant target child ∧
      missingBelowCount target child.horizon = 0 ∧
      child.anchorParent < parent.anchorParent := by
  have hchildCrossing := h.crossing_refinedChild_is_crossing
    hparent hhorizon hchild hprogress
  have hbudgetLe := missingBelowCount_antitone
    (m := target) hhorizon
  have hparentBudget : missingBelowCount target parent.horizon = 0 := by
    rw [h.budget_zero] at hbudgetLe
    omega
  exact ⟨hchildCrossing,
    crossing_zeroBudget_progress_forces_anchorDrop hparent hparentBudget
      hchildCrossing hprogress⟩

/-- The exact ready-crossing state forced by a hypothetical permanent tail.
Its horizon lies inside the tail, its outer history budget is zero, and no
future downcross can discharge the crossing by consuming a new small value.
-/
structure PermanentTailCrossingCertificate
    (target start : Nat) (node : PhaseSearchNode) : Prop where
  ready_crossing : ReadyCrossingSearchInvariant target node
  horizon_in_tail : start ≤ node.horizon
  budget_zero : missingBelowCount target node.horizon = 0
  horizon_strictly_above : target < a node.horizon
  no_future_downcross : ¬ ∃ time,
    FutureDowncrossStep target node.horizon time

/-- Every missing permanent-above tail contains a ready crossing with zero
remaining history budget.  We obtain it from a finite upcross between the
initial zero and the tail, then move its stored horizon into the tail. -/
theorem MissingPermanentAboveTail.exists_crossingCertificate
    {target start : Nat}
    (h : MissingPermanentAboveTail target start) :
    ∃ node, PermanentTailCrossingCertificate target start node := by
  have hinitialBelow : a 0 < target := by
    simpa [a, stateAt, initial] using h.target_positive
  have hstartAbove := h.strictly_above start (Nat.le_refl _)
  rcases exists_weakUpcrossingStep_between
      (show 0 ≤ start by omega) hinitialBelow
      (Nat.le_of_lt hstartAbove) with
    ⟨crossingTime, hcrossing, hcrossingBound⟩
  have hendpointNe : a (crossingTime + 1) ≠ target := by
    intro hequal
    exact h.target_missing ⟨crossingTime + 1, hequal⟩
  have hendpointStrict : target < a (crossingTime + 1) :=
    Nat.lt_of_le_of_ne hcrossing.endpoint_ge (Ne.symm hendpointNe)
  have htargetUnseen : target ∉ valuesThrough crossingTime := by
    intro hseen
    rcases mem_valuesThrough_iff.mp hseen with ⟨witness, _, hvalue⟩
    exact h.target_missing ⟨witness, hvalue⟩
  rcases exists_coordinatesAt (n := crossingTime + 1) (by omega) with
    ⟨quotient, remainder, hcoordinates⟩
  let horizon := max (start + 1) target
  let node : PhaseSearchNode :=
    ⟨horizon, a crossingTime, .normal, a crossingTime⟩
  have hstartHorizon : start ≤ horizon := by
    exact Nat.le_trans (by omega) (Nat.le_max_left _ _)
  have hcrossingBefore : crossingTime + 1 < horizon := by
    have : crossingTime + 1 < start + 1 := by omega
    exact Nat.lt_of_lt_of_le this (Nat.le_max_left _ _)
  have hrecovery : CrossingRecoveryInvariant target horizon
      (a (crossingTime + 1)) crossingTime quotient remainder := {
    target_missing := htargetUnseen
    forced_addition := hcrossing.forced_addition
    crossing := ⟨hcrossing.below, hendpointStrict,
      a_succ_of_not_canSubtract hcrossing.forced_addition⟩
    coordinates := hcoordinates
    crossing_before_horizon := hcrossingBefore
    predecessor_lt_anchor := Nat.lt_trans hcrossing.below hendpointStrict
  }
  have hready : ReadyCrossingSearchInvariant target node := {
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
  have hbudgetStart := h.budget_zero
  have hbudgetLe := missingBelowCount_antitone
    (m := target) hstartHorizon
  have hbudgetHorizon : missingBelowCount target horizon = 0 := by
    omega
  have hhorizonAbove := h.strictly_above horizon hstartHorizon
  have hnoDowncross : ¬ ∃ time,
      FutureDowncrossStep target horizon time := by
    apply (no_futureDowncross_iff_tail_atOrAbove
      (Nat.le_of_lt hhorizonAbove)).mpr
    intro time htime
    exact Nat.le_of_lt (h.strictly_above time
      (Nat.le_trans hstartHorizon htime))
  exact ⟨node, {
    ready_crossing := hready
    horizon_in_tail := hstartHorizon
    budget_zero := hbudgetHorizon
    horizon_strictly_above := hhorizonAbove
    no_future_downcross := hnoDowncross
  }⟩

/-- A time realizes the minimum value of an infinite orbit tail. -/
structure TailMinimumAt (start time : Nat) : Prop where
  start_le_time : start ≤ time
  minimal : ∀ later, start ≤ later → a time ≤ a later

/-- Every natural-valued tail has a minimum, by well-founded induction on
the value at a chosen tail point. -/
theorem exists_tailMinimumAt (start : Nat) :
    ∃ time, TailMinimumAt start time := by
  classical
  have aux : ∀ bound,
      (∃ time, start ≤ time ∧ a time = bound) →
      ∃ time, TailMinimumAt start time := by
    intro bound
    induction bound using Nat.strongRecOn with
    | ind bound ih =>
        intro hwitness
        by_cases hlower : ∃ later, start ≤ later ∧ a later < bound
        · rcases hlower with ⟨later, htime, hbelow⟩
          exact ih (a later) hbelow ⟨later, htime, rfl⟩
        · rcases hwitness with ⟨time, htime, hvalue⟩
          exact ⟨time, {
            start_le_time := htime
            minimal := by
              intro later hlater
              rw [hvalue]
              by_cases hbound : bound ≤ a later
              · exact hbound
              · exact False.elim
                  (hlower ⟨later, hlater, Nat.lt_of_not_ge hbound⟩)
          }⟩
  exact aux (a start) ⟨start, Nat.le_refl _, rfl⟩

/-- At a minimum of a missing permanent-above tail, both the immediate step
and the follow-up step after its forced addition are forced additions.  The
unavailable follow-up candidate is exactly one below the tail minimum and
has its first occurrence strictly before the tail began. -/
structure PermanentTailMinimumCertificate
    (target start time firstTime : Nat) : Prop where
  minimum : TailMinimumAt start time
  first_forced : ¬ CanSubtract (time + 1) (stateAt time)
  first_addition : a (time + 1) = a time + (time + 1)
  followup_candidate : a (time + 1) - (time + 2) = a time - 1
  followup_forced : ¬ CanSubtract (time + 2) (stateAt (time + 1))
  predecessor_first : FirstAt a (a time - 1) firstTime
  firstTime_before_tail : firstTime < start
  target_lt_predecessor : target < a time - 1

/-- Every missing permanent-above tail exposes a finite historical blocker
immediately below its tail minimum. -/
theorem MissingPermanentAboveTail.exists_minimumCertificate
    {target start : Nat}
    (h : MissingPermanentAboveTail target start) :
    ∃ time firstTime,
      PermanentTailMinimumCertificate target start time firstTime := by
  rcases exists_tailMinimumAt start with ⟨time, hminimum⟩
  have habove := h.strictly_above time hminimum.start_le_time
  have htargetPositive := h.target_positive
  have hminimumPositive : 0 < a time := by omega
  have hfirstForced : ¬ CanSubtract (time + 1) (stateAt time) := by
    intro hcan
    have hstep := a_succ_of_canSubtract hcan
    have hnextTime : start ≤ time + 1 :=
      Nat.le_trans hminimum.start_le_time (by omega)
    have hnextMin := hminimum.minimal (time + 1) hnextTime
    have hpositive : time + 1 < a time := by
      simpa [a] using hcan.1
    omega
  have hfirstAddition := a_succ_of_not_canSubtract hfirstForced
  have hcandidate : a (time + 1) - (time + 2) = a time - 1 := by
    omega
  have hfollowupPositive : time + 2 < a (time + 1) := by
    omega
  have hfollowupForced :
      ¬ CanSubtract (time + 2) (stateAt (time + 1)) := by
    intro hcan
    have hstep := a_succ_of_canSubtract hcan
    have hnextTime : start ≤ time + 2 :=
      Nat.le_trans hminimum.start_le_time (by omega)
    have hnextMin := hminimum.minimal (time + 2) hnextTime
    have hnextValue : a (time + 2) = a time - 1 :=
      hstep.trans hcandidate
    omega
  rcases not_canSubtract_cases hfollowupForced with
    hnonpositive | hseen
  · exact False.elim (by omega)
  · have hpredecessorSeen : a time - 1 ∈ valuesThrough (time + 1) := by
      simpa only [hcandidate] using hseen
    rcases history_member_has_firstAt hpredecessorSeen with
      ⟨firstTime, _, hfirst⟩
    have hfirstTimeBefore : firstTime < start := by
      by_cases hbefore : firstTime < start
      · exact hbefore
      · have hstartFirst : start ≤ firstTime := Nat.le_of_not_gt hbefore
        have hfirstMin := hminimum.minimal firstTime hstartFirst
        have hfirstValue := hfirst.1
        omega
    have htargetPredecessor : target < a time - 1 := by
      have htargetLe : target ≤ a time - 1 := by omega
      have hne : a time - 1 ≠ target := by
        intro hequal
        exact h.target_missing ⟨firstTime, hfirst.1.trans hequal⟩
      omega
    exact ⟨time, firstTime, {
      minimum := hminimum
      first_forced := hfirstForced
      first_addition := hfirstAddition
      followup_candidate := hcandidate
      followup_forced := hfollowupForced
      predecessor_first := hfirst
      firstTime_before_tail := hfirstTimeBefore
      target_lt_predecessor := htargetPredecessor
    }⟩

end Recaman
