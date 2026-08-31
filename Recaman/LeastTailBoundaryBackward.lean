import Recaman.LeastTailDischarge

namespace Recaman

noncomputable section

/-!
# Backward dynamics at the least-tail coverage valley

The least-tail boundary fixes the transition into the final newly covered
low value.  Looking one transition farther backward gives a useful exact
trichotomy.  Either that transition is another subtraction and the preceding
value is explicitly high; the coverage clock lies within three of the low
value; or a second, adjacent first-occurrence valley is forced two clocks
earlier.  In the last case the below-target history budget is exactly two
immediately before the earlier valley.

This is a structural, clock-independent alternative to extending the finite
trace.  It exposes the first repeatable backward pattern of the canonical
coverage boundary.
-/

namespace LeastTailDischargeReturnCertificate.BoundaryCertificate

variable {target start : Nat} {parent : PhaseSearchNode}
variable {source : LeastTailDischargeReturnCertificate target start parent}

/-- The fully determined adjacent valley which appears when the transition
immediately before the canonical incoming high is a forced addition. -/
structure PreviousValleyCertificate (b : BoundaryCertificate source) : Prop
    where
  bridge_forced :
    ¬ CanSubtract (b.coverage - 1) (stateAt (b.coverage - 2))
  next_low_below : a b.coverage + 1 < target
  next_low_value : a (b.coverage - 2) = a b.coverage + 1
  next_low_first : FirstAt a (a b.coverage + 1) (b.coverage - 2)
  previous_subtraction :
    CanSubtract (b.coverage - 2) (stateAt (b.coverage - 3))
  previous_high_value :
    a (b.coverage - 3) = a b.coverage + b.coverage - 1
  two_missing_before :
    missingBelowCount target (b.coverage - 3) = 2

/-- Total one-step backward classification of the canonical valley. -/
inductive BackwardOutcome (b : BoundaryCertificate source) : Prop
  | high_predecessor
      (previous_subtraction :
        CanSubtract (b.coverage - 1) (stateAt (b.coverage - 2)))
      (previous_value :
        a (b.coverage - 2) = a b.coverage + 2 * b.coverage - 1) :
      BackwardOutcome b
  | narrow_gap
      (coverage_le_low_add_three :
        b.coverage ≤ a b.coverage + 3) :
      BackwardOutcome b
  | previous_valley
      (certificate : PreviousValleyCertificate b) :
      BackwardOutcome b

/-- The six possible relative placements of the missing target and coverage
clock when both lie within three of the last covered low. -/
def NarrowGapCases (b : BoundaryCertificate source) : Prop :=
    (target = a b.coverage + 1 ∧
        b.coverage = a b.coverage + 1) ∨
      (target = a b.coverage + 1 ∧
        b.coverage = a b.coverage + 2) ∨
      (target = a b.coverage + 1 ∧
        b.coverage = a b.coverage + 3) ∨
      (target = a b.coverage + 2 ∧
        b.coverage = a b.coverage + 2) ∨
      (target = a b.coverage + 2 ∧
        b.coverage = a b.coverage + 3) ∨
      (target = a b.coverage + 3 ∧
        b.coverage = a b.coverage + 3)

/-- In the narrow branch there are only six possible relative placements of
the missing target and the coverage clock above the last covered low. -/
theorem narrowGap_exactCases (b : BoundaryCertificate source)
    (hnarrow : b.coverage ≤ a b.coverage + 3) :
    NarrowGapCases b := by
  unfold NarrowGapCases
  have hbelow := b.predecessor_below
  have htargetCoverage := b.target_le_coverage
  omega

/-- A subtraction immediately before the incoming high makes that high a
first occurrence as well.  Thus the high-predecessor branch contains two
consecutive fresh subtraction landings. -/
theorem incomingFirst_of_previousSubtraction (b : BoundaryCertificate source)
    (hsub : CanSubtract (b.coverage - 1)
      (stateAt (b.coverage - 2))) :
    FirstAt a (a (b.coverage - 1)) (b.coverage - 1) := by
  have hcoverage : 3 < b.coverage := by
    have htarget := nineteen_le_of_target_missing
      source.discharge.combined.tail.target_missing
    have htargetCoverage := b.target_le_coverage
    omega
  have hclock : b.coverage - 2 + 1 = b.coverage - 1 := by
    omega
  have hsub' : CanSubtract (b.coverage - 2 + 1)
      (stateAt (b.coverage - 2)) := by
    rw [hclock]
    exact hsub
  simpa only [hclock] using firstAt_succ_of_canSubtract hsub'

/-- The backward trichotomy.  The non-subtracting, non-narrow branch forces
an earlier fresh low `a coverage + 1`, an incoming subtraction into it, and
two rather than one missing lower levels just before that event. -/
theorem backwardOutcome (b : BoundaryCertificate source) :
    BackwardOutcome b := by
  have hcoverage : 3 < b.coverage := by
    have htarget := nineteen_le_of_target_missing
      source.discharge.combined.tail.target_missing
    have htargetCoverage := b.target_le_coverage
    omega
  have hclockOne : b.coverage - 2 + 1 = b.coverage - 1 := by
    omega
  have hclockTwo : b.coverage - 3 + 1 = b.coverage - 2 := by
    omega
  by_cases hsub :
      CanSubtract (b.coverage - 1) (stateAt (b.coverage - 2))
  · have hsub' : CanSubtract (b.coverage - 2 + 1)
        (stateAt (b.coverage - 2)) := by
      rw [hclockOne]
      exact hsub
    have hstep := a_succ_of_canSubtract hsub'
    rw [hclockOne] at hstep
    have hpositive := hsub'.1
    change b.coverage - 2 + 1 < a (b.coverage - 2) at hpositive
    exact .high_predecessor hsub (by
      have hincoming := b.incoming_value
      omega)
  · by_cases hnarrow : b.coverage ≤ a b.coverage + 3
    · exact .narrow_gap hnarrow
    · have hsub' : ¬ CanSubtract (b.coverage - 2 + 1)
          (stateAt (b.coverage - 2)) := by
        rw [hclockOne]
        exact hsub
      have hbridge := a_succ_of_not_canSubtract hsub'
      rw [hclockOne] at hbridge
      have hnextValue :
          a (b.coverage - 2) = a b.coverage + 1 := by
        have hincoming := b.incoming_value
        omega
      have hnextBelow : a b.coverage + 1 < target := by
        have hle : a b.coverage + 1 ≤ target := by
          have hbelow := b.predecessor_below
          omega
        by_cases heq : a b.coverage + 1 = target
        · exact False.elim
            (source.discharge.combined.tail.target_missing
              ⟨b.coverage - 2, hnextValue.trans heq⟩)
        · omega
      have hnextFirst :
          FirstAt a (a b.coverage + 1) (b.coverage - 2) := by
        refine ⟨hnextValue, ?_⟩
        intro earlier hearlier hequal
        have hseen : a b.coverage + 1 ∈
            valuesThrough (b.coverage - 3) := by
          apply mem_valuesThrough_iff.mpr
          exact ⟨earlier, by omega, hequal⟩
        have hne := a_succ_ne_of_seen hseen (show
          a b.coverage + 1 < b.coverage - 3 + 1 by omega)
        apply hne
        rw [hclockTwo]
        exact hnextValue
      have hpreviousSub :
          CanSubtract (b.coverage - 2) (stateAt (b.coverage - 3)) := by
        by_cases hprevious :
            CanSubtract (b.coverage - 2) (stateAt (b.coverage - 3))
        · exact hprevious
        · have hprevious' : ¬ CanSubtract (b.coverage - 3 + 1)
              (stateAt (b.coverage - 3)) := by
            rw [hclockTwo]
            exact hprevious
          have hadd := a_succ_of_not_canSubtract hprevious'
          rw [hclockTwo] at hadd
          omega
      have hpreviousValue :
          a (b.coverage - 3) = a b.coverage + b.coverage - 1 := by
        have hpreviousSub' : CanSubtract (b.coverage - 3 + 1)
            (stateAt (b.coverage - 3)) := by
          rw [hclockTwo]
          exact hpreviousSub
        have hstep := a_succ_of_canSubtract hpreviousSub'
        rw [hclockTwo] at hstep
        have hpositive := hpreviousSub'.1
        change b.coverage - 3 + 1 < a (b.coverage - 3) at hpositive
        omega
      have hbudgetAfter :
          missingBelowCount target (b.coverage - 2) = 1 := by
        have hge : target ≤ a (b.coverage - 2 + 1) := by
          rw [hclockOne]
          exact Nat.le_of_lt b.incoming_above
        have hsame := missingBelowCount_succ_of_new_ge hge
        rw [hclockOne] at hsame
        have hbefore := b.budget_before_coverage
        exact hsame.symm.trans hbefore
      have hstrict :
          missingBelowCount target (b.coverage - 2) <
            missingBelowCount target (b.coverage - 3) := by
        exact missingBelowCount_strict_of_firstAt hnextBelow
          (by omega) hnextFirst
      have hstepCover := coveredBelowCount_step_le
        (b.coverage - 3) target
      rw [hclockTwo] at hstepCover
      have hpartitionBefore := coveredBelowCount_add_missingBelowCount
        (b.coverage - 3) target
      have hpartitionAfter := coveredBelowCount_add_missingBelowCount
        (b.coverage - 2) target
      have hbudgetBefore :
          missingBelowCount target (b.coverage - 3) = 2 := by
        omega
      exact .previous_valley {
        bridge_forced := hsub
        next_low_below := hnextBelow
        next_low_value := hnextValue
        next_low_first := hnextFirst
        previous_subtraction := hpreviousSub
        previous_high_value := hpreviousValue
        two_missing_before := hbudgetBefore
      }

/-- Fully expanded backward normal form.  The first branch records two
consecutive first-occurrence subtraction landings; the second is the exact
six-case narrow classification; the third is the preceding valley with its
two-unit missing budget. -/
theorem backwardNormalForm (b : BoundaryCertificate source) :
    (CanSubtract (b.coverage - 1) (stateAt (b.coverage - 2)) ∧
      a (b.coverage - 2) = a b.coverage + 2 * b.coverage - 1 ∧
        FirstAt a (a (b.coverage - 1)) (b.coverage - 1)) ∨
      NarrowGapCases b ∨ PreviousValleyCertificate b := by
  cases b.backwardOutcome with
  | high_predecessor hsub hvalue =>
      exact Or.inl ⟨hsub, hvalue,
        b.incomingFirst_of_previousSubtraction hsub⟩
  | narrow_gap hnarrow =>
      exact Or.inr (Or.inl (b.narrowGap_exactCases hnarrow))
  | previous_valley certificate =>
      exact Or.inr (Or.inr certificate)

end LeastTailDischargeReturnCertificate.BoundaryCertificate

/-! ## Source-free backward normal form -/

namespace LeastMissingCoverageValleyCertificate

variable {target : Nat}

/-- Source-free form of the adjacent earlier valley. -/
structure PreviousValleyCertificate
    (h : LeastMissingCoverageValleyCertificate target) : Prop where
  bridge_forced :
    ¬ CanSubtract (h.coverage - 1) (stateAt (h.coverage - 2))
  next_low_below : a h.coverage + 1 < target
  next_low_value : a (h.coverage - 2) = a h.coverage + 1
  next_low_first : FirstAt a (a h.coverage + 1) (h.coverage - 2)
  previous_subtraction :
    CanSubtract (h.coverage - 2) (stateAt (h.coverage - 3))
  previous_high_value :
    a (h.coverage - 3) = a h.coverage + h.coverage - 1
  two_missing_before :
    missingBelowCount target (h.coverage - 3) = 2

/-- Source-free one-step backward classification. -/
inductive BackwardOutcome
    (h : LeastMissingCoverageValleyCertificate target) : Prop
  | high_predecessor
      (previous_subtraction :
        CanSubtract (h.coverage - 1) (stateAt (h.coverage - 2)))
      (previous_value :
        a (h.coverage - 2) = a h.coverage + 2 * h.coverage - 1) :
      BackwardOutcome h
  | narrow_gap
      (coverage_le_low_add_three : h.coverage ≤ a h.coverage + 3) :
      BackwardOutcome h
  | previous_valley
      (certificate : PreviousValleyCertificate h) :
      BackwardOutcome h

/-- Source-free six-case narrow placement. -/
def NarrowGapCases
    (h : LeastMissingCoverageValleyCertificate target) : Prop :=
  (target = a h.coverage + 1 ∧ h.coverage = a h.coverage + 1) ∨
    (target = a h.coverage + 1 ∧ h.coverage = a h.coverage + 2) ∨
    (target = a h.coverage + 1 ∧ h.coverage = a h.coverage + 3) ∨
    (target = a h.coverage + 2 ∧ h.coverage = a h.coverage + 2) ∨
    (target = a h.coverage + 2 ∧ h.coverage = a h.coverage + 3) ∨
    (target = a h.coverage + 3 ∧ h.coverage = a h.coverage + 3)

theorem narrowGap_exactCases
    (h : LeastMissingCoverageValleyCertificate target)
    (hnarrow : h.coverage ≤ a h.coverage + 3) :
    h.NarrowGapCases := by
  unfold NarrowGapCases
  have hbelow := h.low_first.1
  have htargetCoverage := h.target_le_coverage
  omega

/-- Numeric form of the incoming subtraction, derived only from the
source-free valley fields. -/
theorem incoming_value
    (h : LeastMissingCoverageValleyCertificate target) :
    a (h.coverage - 1) = a h.coverage + h.coverage := by
  have hcoverage : 0 < h.coverage := by
    have htarget := nineteen_le_of_target_missing h.target_missing
    have htargetCoverage := h.target_le_coverage
    omega
  have hclock : h.coverage - 1 + 1 = h.coverage := by omega
  have hcan : CanSubtract (h.coverage - 1 + 1)
      (stateAt (h.coverage - 1)) := by
    rw [hclock]
    exact h.incoming_subtraction
  have hstep := a_succ_of_canSubtract hcan
  rw [hclock] at hstep
  have hpositive := hcan.1
  change h.coverage - 1 + 1 < a (h.coverage - 1) at hpositive
  omega

theorem incomingFirst_of_previousSubtraction
    (h : LeastMissingCoverageValleyCertificate target)
    (hsub : CanSubtract (h.coverage - 1)
      (stateAt (h.coverage - 2))) :
    FirstAt a (a (h.coverage - 1)) (h.coverage - 1) := by
  have hcoverage : 3 < h.coverage := by
    have htarget := nineteen_le_of_target_missing h.target_missing
    have htargetCoverage := h.target_le_coverage
    omega
  have hclock : h.coverage - 2 + 1 = h.coverage - 1 := by omega
  have hsub' : CanSubtract (h.coverage - 2 + 1)
      (stateAt (h.coverage - 2)) := by
    rw [hclock]
    exact hsub
  simpa only [hclock] using firstAt_succ_of_canSubtract hsub'

/-- The source-free backward trichotomy uses no terminal-discharge data. -/
theorem backwardOutcome
    (h : LeastMissingCoverageValleyCertificate target) :
    h.BackwardOutcome := by
  have hcoverage : 3 < h.coverage := by
    have htarget := nineteen_le_of_target_missing h.target_missing
    have htargetCoverage := h.target_le_coverage
    omega
  have hclockOne : h.coverage - 2 + 1 = h.coverage - 1 := by omega
  have hclockTwo : h.coverage - 3 + 1 = h.coverage - 2 := by omega
  by_cases hsub :
      CanSubtract (h.coverage - 1) (stateAt (h.coverage - 2))
  · have hsub' : CanSubtract (h.coverage - 2 + 1)
        (stateAt (h.coverage - 2)) := by
      rw [hclockOne]
      exact hsub
    have hstep := a_succ_of_canSubtract hsub'
    rw [hclockOne] at hstep
    have hpositive := hsub'.1
    change h.coverage - 2 + 1 < a (h.coverage - 2) at hpositive
    exact .high_predecessor hsub (by
      have hincoming := h.incoming_value
      omega)
  · by_cases hnarrow : h.coverage ≤ a h.coverage + 3
    · exact .narrow_gap hnarrow
    · have hsub' : ¬ CanSubtract (h.coverage - 2 + 1)
          (stateAt (h.coverage - 2)) := by
        rw [hclockOne]
        exact hsub
      have hbridge := a_succ_of_not_canSubtract hsub'
      rw [hclockOne] at hbridge
      have hnextValue :
          a (h.coverage - 2) = a h.coverage + 1 := by
        have hincoming := h.incoming_value
        omega
      have hnextBelow : a h.coverage + 1 < target := by
        have hle : a h.coverage + 1 ≤ target := by
          have hbelow := h.low_first.1
          omega
        by_cases heq : a h.coverage + 1 = target
        · exact False.elim
            (h.target_missing ⟨h.coverage - 2, hnextValue.trans heq⟩)
        · omega
      have hnextFirst :
          FirstAt a (a h.coverage + 1) (h.coverage - 2) := by
        refine ⟨hnextValue, ?_⟩
        intro earlier hearlier hequal
        have hseen : a h.coverage + 1 ∈
            valuesThrough (h.coverage - 3) := by
          apply mem_valuesThrough_iff.mpr
          exact ⟨earlier, by omega, hequal⟩
        have hne := a_succ_ne_of_seen hseen (show
          a h.coverage + 1 < h.coverage - 3 + 1 by omega)
        apply hne
        rw [hclockTwo]
        exact hnextValue
      have hpreviousSub :
          CanSubtract (h.coverage - 2) (stateAt (h.coverage - 3)) := by
        by_cases hprevious :
            CanSubtract (h.coverage - 2) (stateAt (h.coverage - 3))
        · exact hprevious
        · have hprevious' : ¬ CanSubtract (h.coverage - 3 + 1)
              (stateAt (h.coverage - 3)) := by
            rw [hclockTwo]
            exact hprevious
          have hadd := a_succ_of_not_canSubtract hprevious'
          rw [hclockTwo] at hadd
          omega
      have hpreviousValue :
          a (h.coverage - 3) = a h.coverage + h.coverage - 1 := by
        have hpreviousSub' : CanSubtract (h.coverage - 3 + 1)
            (stateAt (h.coverage - 3)) := by
          rw [hclockTwo]
          exact hpreviousSub
        have hstep := a_succ_of_canSubtract hpreviousSub'
        rw [hclockTwo] at hstep
        have hpositive := hpreviousSub'.1
        change h.coverage - 3 + 1 < a (h.coverage - 3) at hpositive
        omega
      have hbudgetAfter :
          missingBelowCount target (h.coverage - 2) = 1 := by
        have hge : target ≤ a (h.coverage - 2 + 1) := by
          rw [hclockOne]
          exact Nat.le_of_lt h.incoming_above
        have hsame := missingBelowCount_succ_of_new_ge hge
        rw [hclockOne] at hsame
        exact hsame.symm.trans h.budget_before
      have hstrict :
          missingBelowCount target (h.coverage - 2) <
            missingBelowCount target (h.coverage - 3) := by
        exact missingBelowCount_strict_of_firstAt hnextBelow
          (by omega) hnextFirst
      have hstepCover := coveredBelowCount_step_le
        (h.coverage - 3) target
      rw [hclockTwo] at hstepCover
      have hpartitionBefore := coveredBelowCount_add_missingBelowCount
        (h.coverage - 3) target
      have hpartitionAfter := coveredBelowCount_add_missingBelowCount
        (h.coverage - 2) target
      have hbudgetBefore :
          missingBelowCount target (h.coverage - 3) = 2 := by
        omega
      exact .previous_valley {
        bridge_forced := hsub
        next_low_below := hnextBelow
        next_low_value := hnextValue
        next_low_first := hnextFirst
        previous_subtraction := hpreviousSub
        previous_high_value := hpreviousValue
        two_missing_before := hbudgetBefore
      }

/-- The expanded source-free backward normal form as a reusable proposition. -/
def BackwardNormalForm
    (h : LeastMissingCoverageValleyCertificate target) : Prop :=
    (CanSubtract (h.coverage - 1) (stateAt (h.coverage - 2)) ∧
      a (h.coverage - 2) = a h.coverage + 2 * h.coverage - 1 ∧
        FirstAt a (a (h.coverage - 1)) (h.coverage - 1)) ∨
      h.NarrowGapCases ∨ h.PreviousValleyCertificate

/-- Every source-free valley has the expanded backward normal form. -/
theorem backwardNormalForm
    (h : LeastMissingCoverageValleyCertificate target) :
    h.BackwardNormalForm := by
  unfold BackwardNormalForm
  cases h.backwardOutcome with
  | high_predecessor hsub hvalue =>
      exact Or.inl ⟨hsub, hvalue,
        h.incomingFirst_of_previousSubtraction hsub⟩
  | narrow_gap hnarrow =>
      exact Or.inr (Or.inl (h.narrowGap_exactCases hnarrow))
  | previous_valley certificate =>
      exact Or.inr (Or.inr certificate)

end LeastMissingCoverageValleyCertificate

/-- Summit-facing form of the backward normal form.  A least missing target
supplies the canonical discharge, its least-coverage boundary, and the total
backward trichotomy without any replay or fixed-point hypothesis. -/
theorem LeastMissingTarget.exists_leastTailBoundaryBackwardOutcome
    {target : Nat} (h : LeastMissingTarget target) :
    ∃ (start : Nat) (parent : PhaseSearchNode)
      (source : LeastTailDischargeReturnCertificate target start parent)
      (boundary : source.BoundaryCertificate),
      boundary.BackwardOutcome := by
  rcases h.exists_leastTailDischargeReturnCertificate with
    ⟨start, parent, ⟨source⟩⟩
  rcases source.boundaryCertificate with ⟨boundary⟩
  exact ⟨start, parent, source, boundary, boundary.backwardOutcome⟩

/-- Summit-facing expanded form, ready for consumers which need the exact
six narrow configurations or the earlier two-budget valley directly. -/
theorem LeastMissingTarget.exists_leastTailBoundaryNormalForm
    {target : Nat} (h : LeastMissingTarget target) :
    ∃ (start : Nat) (parent : PhaseSearchNode)
      (source : LeastTailDischargeReturnCertificate target start parent)
      (boundary : source.BoundaryCertificate),
      (CanSubtract (boundary.coverage - 1)
          (stateAt (boundary.coverage - 2)) ∧
        a (boundary.coverage - 2) =
            a boundary.coverage + 2 * boundary.coverage - 1 ∧
        FirstAt a (a (boundary.coverage - 1))
          (boundary.coverage - 1)) ∨
        boundary.NarrowGapCases ∨ boundary.PreviousValleyCertificate := by
  rcases h.exists_leastTailDischargeReturnCertificate with
    ⟨start, parent, ⟨source⟩⟩
  rcases source.boundaryCertificate with ⟨boundary⟩
  exact ⟨start, parent, source, boundary, boundary.backwardNormalForm⟩

/-- Completely source-free summit form of the backward classification. -/
theorem LeastMissingTarget.exists_coverageValleyBackwardNormalForm
    {target : Nat} (h : LeastMissingTarget target) :
    ∃ certificate : LeastMissingCoverageValleyCertificate target,
      certificate.BackwardNormalForm := by
  rcases h.exists_coverageValleyCertificate with ⟨certificate⟩
  exact ⟨certificate, certificate.backwardNormalForm⟩

end

end Recaman
