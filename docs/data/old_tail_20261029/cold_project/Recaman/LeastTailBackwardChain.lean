import Recaman.LeastTailBoundaryBackward

namespace Recaman

noncomputable section

/-!
# Iterating the least-tail boundary backwards

The first backward step at the canonical coverage valley repeats.  At depth
`d`, either another subtraction produces an explicitly high fresh value, the
remaining clock has approached within three of the current low, or an earlier
valley appears.  In the last branch the low and the missing-below budget both
increase by one.  This module packages that pattern as a finite iteration
which is independent of any authenticated trace depth.
-/

namespace LeastMissingCoverageValleyCertificate

variable {target : Nat}

/-- The `depth`-th member of the alternating backward valley chain. -/
structure BackwardValleyStage
    (h : LeastMissingCoverageValleyCertificate target) (depth : Nat) where
  clock : Nat
  clock_depth_eq : clock + 2 * depth = h.coverage
  low_below : a h.coverage + depth < target
  low_value : a clock = a h.coverage + depth
  low_first : FirstAt a (a h.coverage + depth) clock
  incoming_subtraction : CanSubtract clock (stateAt (clock - 1))
  incoming_value : a (clock - 1) = a clock + clock
  incoming_above : target < a (clock - 1)
  budget_before :
    missingBelowCount target (clock - 1) = depth + 1

/-- Every positive-depth backward stage is an explicit strict edge in the
existing well-founded missing-history relation, directed forward from the
earlier stage cursor to the canonical boundary cursor. -/
theorem BackwardValleyStage.historyBudgetDrop_to_boundary
    {h : LeastMissingCoverageValleyCertificate target} {depth : Nat}
    (stage : h.BackwardValleyStage depth) (hdepth : 0 < depth) :
    TerminalHistoryBudgetDrop target (h.coverage - 1)
      (stage.clock - 1) := by
  unfold TerminalHistoryBudgetDrop
  rw [h.budget_before, stage.budget_before]
  omega

/-- The initial stage is exactly the canonical coverage valley. -/
def initialBackwardValleyStage
    (h : LeastMissingCoverageValleyCertificate target) :
    h.BackwardValleyStage 0 := {
  clock := h.coverage
  clock_depth_eq := by simp
  low_below := by simpa using h.low_first.1
  low_value := by simp
  low_first := by simpa using h.low_first.2
  incoming_subtraction := h.incoming_subtraction
  incoming_value := h.incoming_value
  incoming_above := h.incoming_above
  budget_before := by simpa using h.budget_before
}

/-- One generic backward step.  The extension branch needs exactly enough
global room to keep the new incoming high at or above the missing target;
equality is then excluded by target missingness. -/
inductive BackwardValleyStageOutcome
    {h : LeastMissingCoverageValleyCertificate target} {depth : Nat}
    (stage : h.BackwardValleyStage depth) : Prop
  | high_predecessor
      (previous_subtraction :
        CanSubtract (stage.clock - 1) (stateAt (stage.clock - 2)))
      (previous_value :
        a (stage.clock - 2) =
          a stage.clock + 2 * stage.clock - 1) :
      BackwardValleyStageOutcome stage
  | narrow_gap
      (clock_le_low_add_three :
        stage.clock ≤ a stage.clock + 3) :
      BackwardValleyStageOutcome stage
  | extend
      (next : h.BackwardValleyStage (depth + 1)) :
      BackwardValleyStageOutcome stage

/-- Generic extension of the alternating valley pattern. -/
theorem BackwardValleyStage.outcome
    {h : LeastMissingCoverageValleyCertificate target} {depth : Nat}
    (stage : h.BackwardValleyStage depth)
    (hroom : target + depth + 1 ≤ a h.coverage + h.coverage) :
    BackwardValleyStageOutcome stage := by
  by_cases hnarrow : stage.clock ≤ a stage.clock + 3
  · exact .narrow_gap hnarrow
  · have hclock : 3 < stage.clock := by omega
    have hclockOne : stage.clock - 2 + 1 = stage.clock - 1 := by omega
    have hclockTwo : stage.clock - 3 + 1 = stage.clock - 2 := by omega
    by_cases hsub :
        CanSubtract (stage.clock - 1) (stateAt (stage.clock - 2))
    · have hsub' : CanSubtract (stage.clock - 2 + 1)
          (stateAt (stage.clock - 2)) := by
        rw [hclockOne]
        exact hsub
      have hstep := a_succ_of_canSubtract hsub'
      rw [hclockOne] at hstep
      have hpositive := hsub'.1
      change stage.clock - 2 + 1 < a (stage.clock - 2) at hpositive
      exact .high_predecessor hsub (by
        have hincoming := stage.incoming_value
        omega)
    · have hsub' : ¬ CanSubtract (stage.clock - 2 + 1)
          (stateAt (stage.clock - 2)) := by
        rw [hclockOne]
        exact hsub
      have hbridge := a_succ_of_not_canSubtract hsub'
      rw [hclockOne] at hbridge
      have hnextValue :
          a (stage.clock - 2) = a stage.clock + 1 := by
        have hincoming := stage.incoming_value
        omega
      have hnextValueBase :
          a (stage.clock - 2) = a h.coverage + (depth + 1) := by
        rw [hnextValue, stage.low_value]
        omega
      have hnextBelow : a h.coverage + (depth + 1) < target := by
        have hle : a h.coverage + (depth + 1) ≤ target := by
          have hbelow := stage.low_below
          omega
        by_cases heq : a h.coverage + (depth + 1) = target
        · exact False.elim
            (h.target_missing ⟨stage.clock - 2,
              hnextValueBase.trans heq⟩)
        · omega
      have hnextFirst :
          FirstAt a (a h.coverage + (depth + 1))
            (stage.clock - 2) := by
        refine ⟨hnextValueBase, ?_⟩
        intro earlier hearlier hequal
        have hseen : a h.coverage + (depth + 1) ∈
            valuesThrough (stage.clock - 3) := by
          apply mem_valuesThrough_iff.mpr
          exact ⟨earlier, by omega, hequal⟩
        have hsmall :
            a h.coverage + (depth + 1) < stage.clock - 3 + 1 := by
          have hlowValue := stage.low_value
          omega
        have hne := a_succ_ne_of_seen hseen hsmall
        apply hne
        rw [hclockTwo]
        exact hnextValueBase
      have hpreviousSub :
          CanSubtract (stage.clock - 2)
            (stateAt (stage.clock - 3)) := by
        by_cases hprevious :
            CanSubtract (stage.clock - 2) (stateAt (stage.clock - 3))
        · exact hprevious
        · have hprevious' :
              ¬ CanSubtract (stage.clock - 3 + 1)
                (stateAt (stage.clock - 3)) := by
            rw [hclockTwo]
            exact hprevious
          have hadd := a_succ_of_not_canSubtract hprevious'
          rw [hclockTwo] at hadd
          omega
      have hpreviousValue :
          a (stage.clock - 3) =
            a (stage.clock - 2) + (stage.clock - 2) := by
        have hpreviousSub' : CanSubtract (stage.clock - 3 + 1)
            (stateAt (stage.clock - 3)) := by
          rw [hclockTwo]
          exact hpreviousSub
        have hstep := a_succ_of_canSubtract hpreviousSub'
        rw [hclockTwo] at hstep
        have hpositive := hpreviousSub'.1
        change stage.clock - 3 + 1 < a (stage.clock - 3) at hpositive
        omega
      have hpreviousAbove : target < a (stage.clock - 3) := by
        have hge : target ≤ a (stage.clock - 3) := by
          rw [hpreviousValue, hnextValueBase]
          have hclockDepth := stage.clock_depth_eq
          omega
        by_cases heq : a (stage.clock - 3) = target
        · exact False.elim
            (h.target_missing ⟨stage.clock - 3, heq⟩)
        · omega
      have hbudgetAfter :
          missingBelowCount target (stage.clock - 2) = depth + 1 := by
        have hge : target ≤ a (stage.clock - 2 + 1) := by
          rw [hclockOne]
          exact Nat.le_of_lt stage.incoming_above
        have hsame := missingBelowCount_succ_of_new_ge hge
        rw [hclockOne] at hsame
        exact hsame.symm.trans stage.budget_before
      have hstrict :
          missingBelowCount target (stage.clock - 2) <
            missingBelowCount target (stage.clock - 3) := by
        exact missingBelowCount_strict_of_firstAt hnextBelow
          (by omega) hnextFirst
      have hstepCover := coveredBelowCount_step_le
        (stage.clock - 3) target
      rw [hclockTwo] at hstepCover
      have hpartitionBefore := coveredBelowCount_add_missingBelowCount
        (stage.clock - 3) target
      have hpartitionAfter := coveredBelowCount_add_missingBelowCount
        (stage.clock - 2) target
      have hbudgetBefore :
          missingBelowCount target (stage.clock - 3) = depth + 2 := by
        omega
      exact .extend {
        clock := stage.clock - 2
        clock_depth_eq := by
          have hclockDepth := stage.clock_depth_eq
          omega
        low_below := hnextBelow
        low_value := hnextValueBase
        low_first := hnextFirst
        incoming_subtraction := hpreviousSub
        incoming_value := hpreviousValue
        incoming_above := hpreviousAbove
        budget_before := by
          rw [show stage.clock - 2 - 1 = stage.clock - 3 by omega]
          omega
      }

/-- Finite iteration result: an obstruction appears before `limit`, or the
alternating valley certificate reaches exactly that depth. -/
inductive BackwardValleyChainOutcome
    (h : LeastMissingCoverageValleyCertificate target) (limit : Nat) : Prop
  | high_predecessor
      (depth : Nat) (depth_lt : depth < limit)
      (stage : h.BackwardValleyStage depth)
      (previous_subtraction :
        CanSubtract (stage.clock - 1) (stateAt (stage.clock - 2)))
      (previous_value :
        a (stage.clock - 2) =
          a stage.clock + 2 * stage.clock - 1) :
      BackwardValleyChainOutcome h limit
  | narrow_gap
      (depth : Nat) (depth_lt : depth < limit)
      (stage : h.BackwardValleyStage depth)
      (clock_le_low_add_three : stage.clock ≤ a stage.clock + 3) :
      BackwardValleyChainOutcome h limit
  | reaches
      (stage : h.BackwardValleyStage limit) :
      BackwardValleyChainOutcome h limit

/-- Consumer-oriented expansion of a finite chain: a concrete high branch,
a global coverage/low gap bound, or a stage at the requested depth. -/
def ExpandedBackwardValleyChainOutcome
    (h : LeastMissingCoverageValleyCertificate target) (limit : Nat) : Prop :=
  (∃ (depth : Nat) (stage : h.BackwardValleyStage depth),
      depth < limit ∧
        CanSubtract (stage.clock - 1) (stateAt (stage.clock - 2)) ∧
        a (stage.clock - 2) =
          a stage.clock + 2 * stage.clock - 1) ∨
    h.coverage ≤ a h.coverage + 3 * limit ∨
    Nonempty (h.BackwardValleyStage limit)

/-- Forget the internal narrow depth while retaining its resulting global
coverage bound. -/
theorem BackwardValleyChainOutcome.expanded
    {h : LeastMissingCoverageValleyCertificate target} {limit : Nat}
    (outcome : h.BackwardValleyChainOutcome limit) :
    h.ExpandedBackwardValleyChainOutcome limit := by
  unfold ExpandedBackwardValleyChainOutcome
  cases outcome with
  | high_predecessor depth depth_lt stage hsub hvalue =>
      exact Or.inl ⟨depth, stage, depth_lt, hsub, hvalue⟩
  | narrow_gap depth depth_lt stage hnarrow =>
      right
      left
      have hclockDepth := stage.clock_depth_eq
      have hlowValue := stage.low_value
      omega
  | reaches stage =>
      exact Or.inr (Or.inr ⟨stage⟩)

/-- Numeric consumer form relative to an externally known low floor.  If a
finite chain reaches its requested depth, that floor plus the depth is still
strictly below the missing target. -/
def BackwardValleyChainFloorAlternative
    (h : LeastMissingCoverageValleyCertificate target)
    (floor limit : Nat) : Prop :=
  (∃ (depth : Nat) (stage : h.BackwardValleyStage depth),
      depth < limit ∧
        CanSubtract (stage.clock - 1) (stateAt (stage.clock - 2)) ∧
        a (stage.clock - 2) =
          a stage.clock + 2 * stage.clock - 1) ∨
    h.coverage ≤ a h.coverage + 3 * limit ∨
    floor + limit < target

theorem BackwardValleyChainOutcome.floorAlternative
    {h : LeastMissingCoverageValleyCertificate target}
    {floor limit : Nat} (outcome : h.BackwardValleyChainOutcome limit)
    (hfloor : floor ≤ a h.coverage) :
    h.BackwardValleyChainFloorAlternative floor limit := by
  unfold BackwardValleyChainFloorAlternative
  cases outcome with
  | high_predecessor depth depth_lt stage hsub hvalue =>
      exact Or.inl ⟨depth, stage, depth_lt, hsub, hvalue⟩
  | narrow_gap depth depth_lt stage hnarrow =>
      right
      left
      have hclockDepth := stage.clock_depth_eq
      have hlowValue := stage.low_value
      omega
  | reaches stage =>
      right
      right
      have hbelow := stage.low_below
      omega

/-- Finite-chain alternative retaining an explicit edge in the established
well-founded history-budget relation when the chain reaches positive depth. -/
def BackwardValleyChainHistoryAlternative
    (h : LeastMissingCoverageValleyCertificate target) (limit : Nat) : Prop :=
  (∃ (depth : Nat) (stage : h.BackwardValleyStage depth),
      depth < limit ∧
        CanSubtract (stage.clock - 1) (stateAt (stage.clock - 2)) ∧
        a (stage.clock - 2) =
          a stage.clock + 2 * stage.clock - 1) ∨
    (∃ (depth : Nat) (stage : h.BackwardValleyStage depth),
      depth < limit ∧ stage.clock ≤ a stage.clock + 3) ∨
    (∃ stage : h.BackwardValleyStage limit,
      TerminalHistoryBudgetDrop target (h.coverage - 1)
        (stage.clock - 1))

theorem BackwardValleyChainOutcome.historyAlternative
    {h : LeastMissingCoverageValleyCertificate target} {limit : Nat}
    (outcome : h.BackwardValleyChainOutcome limit) (hlimit : 0 < limit) :
    h.BackwardValleyChainHistoryAlternative limit := by
  unfold BackwardValleyChainHistoryAlternative
  cases outcome with
  | high_predecessor depth depth_lt stage hsub hvalue =>
      exact Or.inl ⟨depth, stage, depth_lt, hsub, hvalue⟩
  | narrow_gap depth depth_lt stage hnarrow =>
      exact Or.inr (Or.inl ⟨depth, stage, depth_lt, hnarrow⟩)
  | reaches stage =>
      exact Or.inr (Or.inr
        ⟨stage, stage.historyBudgetDrop_to_boundary hlimit⟩)

/-- Iterate whenever the requested depth fits in the exact global room
`low + coverage - target`. -/
theorem backwardValleyChainOutcome_of_room
    (h : LeastMissingCoverageValleyCertificate target) (limit : Nat)
    (hroom : target + limit ≤ a h.coverage + h.coverage) :
    h.BackwardValleyChainOutcome limit := by
  induction limit with
  | zero =>
      exact .reaches h.initialBackwardValleyStage
  | succ limit ih =>
      have hroomPrev : target + limit ≤
          a h.coverage + h.coverage := by omega
      cases ih hroomPrev with
      | high_predecessor depth depth_lt stage hsub hvalue =>
          exact .high_predecessor depth (by omega) stage hsub hvalue
      | narrow_gap depth depth_lt stage hnarrow =>
          exact .narrow_gap depth (by omega) stage hnarrow
      | reaches stage =>
          cases stage.outcome (by omega) with
          | high_predecessor hsub hvalue =>
              exact .high_predecessor limit (by omega) stage hsub hvalue
          | narrow_gap hnarrow =>
              exact .narrow_gap limit (by omega) stage hnarrow
          | extend next =>
              exact .reaches next

/-- Convenient sufficient condition: the original target/coverage bound
makes every depth up to the original low fit in the general room theorem. -/
theorem backwardValleyChainOutcome
    (h : LeastMissingCoverageValleyCertificate target) (limit : Nat)
    (hlimit : limit ≤ a h.coverage) :
    h.BackwardValleyChainOutcome limit := by
  apply h.backwardValleyChainOutcome_of_room limit
  have htargetCoverage := h.target_le_coverage
  omega

/-- Exact amount of depth supplied by the combined low/coverage surplus over
the missing target. -/
def backwardRoom (h : LeastMissingCoverageValleyCertificate target) : Nat :=
  a h.coverage + h.coverage - target

theorem target_add_backwardRoom
    (h : LeastMissingCoverageValleyCertificate target) :
    target + h.backwardRoom = a h.coverage + h.coverage := by
  unfold backwardRoom
  have htargetCoverage := h.target_le_coverage
  omega

/-- The apparent maximum-depth clock constraint has a subtraction-free
form: the target must lie at least halfway above twice the boundary low. -/
theorem two_mul_backwardRoom_le_coverage_iff
    (h : LeastMissingCoverageValleyCertificate target) :
    2 * h.backwardRoom ≤ h.coverage ↔
      h.coverage + 2 * a h.coverage ≤ 2 * target := by
  have hroom := h.target_add_backwardRoom
  omega

/-- Canonical maximal-depth chain supplied by the exact global room. -/
theorem maximalBackwardValleyChainOutcome
    (h : LeastMissingCoverageValleyCertificate target) :
    h.BackwardValleyChainOutcome h.backwardRoom := by
  apply h.backwardValleyChainOutcome_of_room h.backwardRoom
  exact Nat.le_of_eq h.target_add_backwardRoom

/-- Numeric reading of the maximal chain.  If neither explicit obstruction
appears, a stage at maximal depth forces twice the available room to fit
inside the coverage clock. -/
theorem maximalBackwardValleyNumericAlternative
    (h : LeastMissingCoverageValleyCertificate target) :
    (∃ (depth : Nat) (stage : h.BackwardValleyStage depth),
      depth < h.backwardRoom ∧
        CanSubtract (stage.clock - 1) (stateAt (stage.clock - 2)) ∧
        a (stage.clock - 2) =
          a stage.clock + 2 * stage.clock - 1) ∨
      h.coverage ≤ a h.coverage + 3 * h.backwardRoom ∨
      2 * h.backwardRoom ≤ h.coverage := by
  have hexpanded := h.maximalBackwardValleyChainOutcome.expanded
  rcases hexpanded with hhigh | hrest
  · exact Or.inl hhigh
  · rcases hrest with hnarrow | hstage
    · exact Or.inr (Or.inl hnarrow)
    · rcases hstage with ⟨stage⟩
      right
      right
      have hclockDepth := stage.clock_depth_eq
      omega

/-- Sharp maximal-chain trichotomy.  Unlike the coarse expanded form, the
narrow branch retains its actual depth and clock; the terminal branch is
converted to the clean ratio inequality
`coverage + 2*low ≤ 2*target`. -/
def MaximalBackwardSharpAlternative
    (h : LeastMissingCoverageValleyCertificate target) : Prop :=
  (∃ (depth : Nat) (stage : h.BackwardValleyStage depth),
      depth < h.backwardRoom ∧
        CanSubtract (stage.clock - 1) (stateAt (stage.clock - 2)) ∧
        a (stage.clock - 2) =
          a stage.clock + 2 * stage.clock - 1) ∨
    (∃ (depth : Nat) (stage : h.BackwardValleyStage depth),
      depth < h.backwardRoom ∧ stage.clock ≤ a stage.clock + 3) ∨
    h.coverage + 2 * a h.coverage ≤ 2 * target

theorem maximalBackwardSharpAlternative
    (h : LeastMissingCoverageValleyCertificate target) :
    h.MaximalBackwardSharpAlternative := by
  unfold MaximalBackwardSharpAlternative
  cases h.maximalBackwardValleyChainOutcome with
  | high_predecessor depth depth_lt stage hsub hvalue =>
      exact Or.inl ⟨depth, stage, depth_lt, hsub, hvalue⟩
  | narrow_gap depth depth_lt stage hnarrow =>
      exact Or.inr (Or.inl ⟨depth, stage, depth_lt, hnarrow⟩)
  | reaches stage =>
      right
      right
      apply h.two_mul_backwardRoom_le_coverage_iff.mp
      have hclockDepth := stage.clock_depth_eq
      omega

/-- Structural reading of the sharp trichotomy.  The terminal ratio branch
in particular forces the missing target to be at least twice the canonical
boundary low. -/
def MaximalBackwardStructuralAlternative
    (h : LeastMissingCoverageValleyCertificate target) : Prop :=
  (∃ (depth : Nat) (stage : h.BackwardValleyStage depth),
      depth < h.backwardRoom ∧
        CanSubtract (stage.clock - 1) (stateAt (stage.clock - 2)) ∧
        a (stage.clock - 2) =
          a stage.clock + 2 * stage.clock - 1) ∨
    (∃ (depth : Nat) (stage : h.BackwardValleyStage depth),
      depth < h.backwardRoom ∧
        stage.clock ≤ a stage.clock + 3 ∧
        target ≤ a h.coverage + 3 * depth + 3) ∨
    2 * a h.coverage ≤ target

theorem maximalBackwardStructuralAlternative
    (h : LeastMissingCoverageValleyCertificate target) :
    h.MaximalBackwardStructuralAlternative := by
  unfold MaximalBackwardStructuralAlternative
  rcases h.maximalBackwardSharpAlternative with hhigh | hnarrow | hratio
  · exact Or.inl hhigh
  · rcases hnarrow with ⟨depth, stage, hdepth, hgap⟩
    right
    left
    refine ⟨depth, stage, hdepth, hgap, ?_⟩
    have hclockDepth := stage.clock_depth_eq
    have hlowValue := stage.low_value
    have htargetCoverage := h.target_le_coverage
    omega
  · right
    right
    have htargetCoverage := h.target_le_coverage
    omega

/-- A consumer-supplied lower bound on the boundary low turns the terminal
ratio branch into a corresponding absolute target floor, without weakening
the explicit high or narrow witnesses. -/
def MaximalBackwardFloorAlternative
    (h : LeastMissingCoverageValleyCertificate target) (floor : Nat) : Prop :=
  (∃ (depth : Nat) (stage : h.BackwardValleyStage depth),
      depth < h.backwardRoom ∧
        CanSubtract (stage.clock - 1) (stateAt (stage.clock - 2)) ∧
        a (stage.clock - 2) =
          a stage.clock + 2 * stage.clock - 1) ∨
    (∃ (depth : Nat) (stage : h.BackwardValleyStage depth),
      depth < h.backwardRoom ∧
        stage.clock ≤ a stage.clock + 3 ∧
        target ≤ a h.coverage + 3 * depth + 3) ∨
    2 * floor ≤ target

theorem maximalBackwardFloorAlternative
    (h : LeastMissingCoverageValleyCertificate target) {floor : Nat}
    (hfloor : floor ≤ a h.coverage) :
    h.MaximalBackwardFloorAlternative floor := by
  unfold MaximalBackwardFloorAlternative
  rcases h.maximalBackwardStructuralAlternative with
    hhigh | hnarrow | hratio
  · exact Or.inl hhigh
  · exact Or.inr (Or.inl hnarrow)
  · exact Or.inr (Or.inr (by omega))

/-- Expanded finite-chain conclusion obtained directly from the valley. -/
theorem expandedBackwardValleyChainOutcome
    (h : LeastMissingCoverageValleyCertificate target) (limit : Nat)
    (hlimit : limit ≤ a h.coverage) :
    h.ExpandedBackwardValleyChainOutcome limit :=
  (h.backwardValleyChainOutcome limit hlimit).expanded

end LeastMissingCoverageValleyCertificate

end

end Recaman
