import Recaman.CrossingBelowRefined

namespace Recaman

/-! # The remaining above-target tail boundary

The below-horizon continuation can fail to lower the crossing anchor, but in
that exact residual its enlarged child horizon must be back at or above the
target.  Any later downcross then lowers the original parent's history budget
as well, bypassing the nondecreasing intermediate crossing.

What remains is therefore a genuine tail-recurrence statement: an orbit
which is at or above the target must either contain the target or later
return below it.  This module states that boundary explicitly and proves that
it is sufficient for a total ready-crossing refined step.
-/

/-- A later below-target state after an at-or-above start contains an
adjacent future downcross. -/
theorem exists_futureDowncrossStep_between
    {target start finish : Nat}
    (htime : start ≤ finish)
    (hstart : target ≤ a start)
    (hfinish : a finish < target) :
    ∃ time, FutureDowncrossStep target start time := by
  have aux : ∀ distance : Nat, a (start + distance) < target →
      ∃ time, FutureDowncrossStep target start time := by
    intro distance
    induction distance with
    | zero =>
        intro hbelow
        simp only [Nat.add_zero] at hbelow
        exact False.elim (by omega)
    | succ distance ih =>
        intro hbelow
        simp only [Nat.add_succ] at hbelow
        by_cases hprevious : target ≤ a (start + distance)
        · exact ⟨start + distance, {
            horizon_le_time := by omega
            start_at_or_above := hprevious
            endpoint_below := by simpa [Nat.add_assoc] using hbelow
          }⟩
        · exact ih (Nat.lt_of_not_ge hprevious)
  have hfinishEq : start + (finish - start) = finish := by omega
  have hresult := aux (finish - start)
  rw [hfinishEq] at hresult
  exact hresult hfinish

/-- Failure of every future downcross from an above-target start is exactly
permanent residence in the at-or-above half-line. -/
theorem no_futureDowncross_iff_tail_atOrAbove
    {target start : Nat} (hstart : target ≤ a start) :
    (¬ ∃ time, FutureDowncrossStep target start time) ↔
      ∀ time, start ≤ time → target ≤ a time := by
  constructor
  · intro hnone time htime
    by_cases habove : target ≤ a time
    · exact habove
    · have hbelow : a time < target := Nat.lt_of_not_ge habove
      exact False.elim
        (hnone (exists_futureDowncrossStep_between htime hstart hbelow))
  · intro habove ⟨time, hdown⟩
    have htail := habove (time + 1)
      (Nat.le_trans hdown.horizon_le_time (by omega))
    exact (Nat.not_lt_of_ge htail) hdown.endpoint_below

/-- A target is a least missing value when it is absent from the whole orbit
and every smaller natural occurs. -/
structure LeastMissingTarget (target : Nat) : Prop where
  target_missing : ¬ ∃ time, a time = target
  below_occurs : ∀ value, value < target → ∃ time, a time = value

/-- Finitely many individual occurrence witnesses below a target can be
collected into one history horizon. -/
theorem exists_historyHorizon_covering_below
    {target : Nat}
    (hbelow : ∀ value, value < target → ∃ time, a time = value) :
    ∃ horizon, ∀ value, value < target →
      value ∈ valuesThrough horizon := by
  induction target with
  | zero =>
      exact ⟨0, by intro value hvalue; omega⟩
  | succ target ih =>
      have hsmaller : ∀ value, value < target →
          ∃ time, a time = value := by
        intro value hvalue
        exact hbelow value (by omega)
      rcases ih hsmaller with ⟨horizon, hcovered⟩
      rcases hbelow target (by omega) with ⟨time, htarget⟩
      refine ⟨max horizon time, ?_⟩
      intro value hvalue
      rcases Nat.eq_or_lt_of_le (show value ≤ target by omega) with
        hequal | hstrict
      · subst value
        apply valuesThrough_mono (Nat.le_max_right horizon time)
        simpa [htarget] using current_mem_valuesThrough time
      · exact valuesThrough_mono (Nat.le_max_left horizon time)
          (hcovered value hstrict)

/-- Once every below-target value is already in the stored history, a future
downcross is impossible: its legal-subtraction endpoint would have to be
both fresh and already seen. -/
theorem no_futureDowncross_of_belowCovered
    {target start : Nat}
    (hcovered : ∀ value, value < target →
      value ∈ valuesThrough start) :
    ¬ ∃ time, FutureDowncrossStep target start time := by
  intro hfuture
  rcases hfuture with ⟨time, hdown⟩
  have hcan : CanSubtract (time + 1) (stateAt time) := by
    by_cases hcan : CanSubtract (time + 1) (stateAt time)
    · exact hcan
    · have hadd := a_succ_of_not_canSubtract hcan
      have hstart := hdown.start_at_or_above
      have hendpoint := hdown.endpoint_below
      omega
  have hstep := a_succ_of_canSubtract hcan
  have hfresh : a (time + 1) ∉ valuesThrough time := by
    rw [hstep]
    exact hcan.2
  apply hfresh
  exact valuesThrough_mono hdown.horizon_le_time
    (hcovered (a (time + 1)) hdown.endpoint_below)

/-- A hypothetical least missing target eventually lies strictly below the
entire remaining orbit.  This explains why the no-downcross branch is the
global core of the conjecture rather than a missing local crossing lemma. -/
theorem LeastMissingTarget.eventually_strictlyAbove
    {target : Nat} (h : LeastMissingTarget target) :
    ∃ start,
      (∀ value, value < target → value ∈ valuesThrough start) ∧
      ∀ time, start ≤ time → target < a time := by
  have htargetPositive : 0 < target := by
    by_cases hzero : target = 0
    · subst target
      exact False.elim (h.target_missing ⟨0, rfl⟩)
    · omega
  rcases exists_historyHorizon_covering_below h.below_occurs with
    ⟨historyHorizon, hcovered⟩
  have tailStrict : ∀ start,
      (∀ value, value < target → value ∈ valuesThrough start) →
      target ≤ a start →
      ∀ time, start ≤ time → target < a time := by
    intro start hcoveredAt habove time htime
    have hnone := no_futureDowncross_of_belowCovered hcoveredAt
    have htail :=
      (no_futureDowncross_iff_tail_atOrAbove habove).mp hnone time htime
    have hne : target ≠ a time := by
      intro hequal
      exact h.target_missing ⟨time, hequal.symm⟩
    exact Nat.lt_of_le_of_ne htail hne
  by_cases habove : target ≤ a historyHorizon
  · exact ⟨historyHorizon, hcovered,
      tailStrict historyHorizon hcovered habove⟩
  · rcases exists_weakUpcrossingStep_from_below htargetPositive
        (Nat.lt_of_not_ge habove) with ⟨time, hcrossing⟩
    have hcoveredLater : ∀ value, value < target →
        value ∈ valuesThrough (time + 1) := by
      intro value hvalue
      exact valuesThrough_mono
        (Nat.le_trans hcrossing.start_le (by omega))
        (hcovered value hvalue)
    exact ⟨time + 1, hcoveredLater,
      tailStrict (time + 1) hcoveredLater hcrossing.endpoint_ge⟩

/-- The precise long-term orbit statement needed by the remaining crossing
branch.  It does not assume a downcross after the target has already been
found. -/
def TargetTailReturnHypothesis (target : Nat) : Prop :=
  ∀ start, target ≤ a start →
    (∃ witness, a witness = target) ∨
      ∃ finish, start ≤ finish ∧ a finish < target

/-- Consequently a least missing target refutes the tail-return hypothesis.
Proving tail return for every positive target therefore rules out precisely
the eventual-above behavior forced by a hypothetical least counterexample. -/
theorem LeastMissingTarget.not_targetTailReturn
    {target : Nat} (h : LeastMissingTarget target) :
    ¬ TargetTailReturnHypothesis target := by
  intro hreturn
  rcases h.eventually_strictlyAbove with ⟨start, _, htail⟩
  have habove : target ≤ a start := Nat.le_of_lt
    (htail start (Nat.le_refl _))
  rcases hreturn start habove with
    hoccurs | ⟨finish, htime, hbelow⟩
  · exact h.target_missing hoccurs
  · exact (Nat.not_lt_of_ge (Nat.le_of_lt (htail finish htime))) hbelow

/-- Tail return for every target rules out the least missing value and hence
implies the full coverage conjecture. -/
theorem all_targetTailReturn_implies_surjective
    (hreturn : ∀ target, TargetTailReturnHypothesis target) :
    ∀ target, ∃ time, a time = target := by
  intro target
  induction target using Nat.strongRecOn with
  | ind target ih =>
      by_cases hoccurs : ∃ time, a time = target
      · exact hoccurs
      · have hleast : LeastMissingTarget target := {
          target_missing := hoccurs
          below_occurs := by
            intro value hvalue
            exact ih value hvalue
        }
        exact False.elim (hleast.not_targetTailReturn (hreturn target))

/-- Conversely, full coverage makes every target-tail return statement
immediate through its occurrence branch.  Thus the family of tail-return
hypotheses is equivalent to the original Recamán coverage conjecture. -/
theorem all_targetTailReturn_iff_surjective :
    (∀ target, TargetTailReturnHypothesis target) ↔
      ∀ target, ∃ time, a time = target := by
  constructor
  · exact all_targetTailReturn_implies_surjective
  · intro hsurjective target start habove
    exact Or.inl (hsurjective target)

/-- Ready-crossing form of the same tail boundary. -/
def ReadyCrossingTailDowncrossHypothesis (target : Nat) : Prop :=
  ∀ node, ReadyCrossingSearchInvariant target node →
    target ≤ a node.horizon →
    (∃ witness, a witness = target) ∨
      ∃ time, FutureDowncrossStep target node.horizon time

/-- A target-tail return supplies the downcross form used by crossing
recovery. -/
theorem readyCrossingTailDowncross_of_targetTailReturn
    {target : Nat} (hreturn : TargetTailReturnHypothesis target) :
    ReadyCrossingTailDowncrossHypothesis target := by
  intro node _ habove
  rcases hreturn node.horizon habove with
    hoccurs | ⟨finish, htime, hbelow⟩
  · exact Or.inl hoccurs
  · exact Or.inr
      (exists_futureDowncrossStep_between htime habove hbelow)

/-- The tail-downcross boundary is sufficient for a total refined step from
every ready crossing.  In the below-horizon growth residual, stable budget
forces the intermediate child horizon back above the target.  A downcross
from there strictly lowers that same budget and therefore gives a direct
rank edge to the original parent. -/
theorem ReadyCrossingSearchInvariant.refinedStep_of_tailDowncross
    {target : Nat} {node : PhaseSearchNode}
    (h : ReadyCrossingSearchInvariant target node)
    (htail : ReadyCrossingTailDowncrossHypothesis target) :
    (∃ witness, a witness = target) ∨
      ∃ child, OrbitReadyRefinedInvariant target child ∧
        PhaseSearchProgress target child node := by
  by_cases habove : target ≤ a node.horizon
  · rcases htail node h habove with hoccurs | ⟨time, hdown⟩
    · exact Or.inl hoccurs
    · exact h.refinedStep_of_futureDowncross hdown
  · have hbelow : a node.horizon < target := Nat.lt_of_not_ge habove
    rcases h.refinedStep_or_continuationGrowth_of_horizonBelow hbelow with
      hoccurs | hstep | hresidual
    · exact Or.inl hoccurs
    · exact Or.inr hstep
    · rcases hresidual with
        ⟨time, quotient, remainder, child, rfl, hcontinuation,
          hchild, hbudgetStable, hanchorNondecreasing, hnoProgress⟩
      have hchildAbove : target ≤ a (time + 2) := by
        by_cases haboveChild : target ≤ a (time + 2)
        · exact haboveChild
        · have hchildBelow : a (time + 2) < target :=
            Nat.lt_of_not_ge haboveChild
          have hdown : FutureDowncrossStep target node.horizon (time + 1) := {
            horizon_le_time := Nat.le_trans hcontinuation.start_le (by omega)
            start_at_or_above := hcontinuation.endpoint_ge
            endpoint_below := by simpa [Nat.add_assoc] using hchildBelow
          }
          have hdrop := hdown.strict_budget_drop
          have hstable :
              missingBelowCount target (time + 2) =
                missingBelowCount target node.horizon := by
            simpa using hbudgetStable
          change missingBelowCount target (time + 2) <
            missingBelowCount target node.horizon at hdrop
          rw [hstable] at hdrop
          exact False.elim (Nat.lt_irrefl _ hdrop)
      rcases htail ⟨time + 2, a time, .normal, a time⟩ hchild
          hchildAbove with hoccurs | ⟨downTime, hdown⟩
      · exact Or.inl hoccurs
      · rcases hchild.refinedStep_of_futureDowncross_withBudgetDrop hdown
          with hoccurs | ⟨next, hnext, hnextProgress, hbudgetDrop⟩
        · exact Or.inl hoccurs
        · have hbudgetDropParent :
              missingBelowCount target next.horizon <
                missingBelowCount target node.horizon := by
            rw [← hbudgetStable]
            exact hbudgetDrop
          exact Or.inr ⟨next, hnext,
            Prod.Lex.left _ _ hbudgetDropParent⟩

/-- The more orbit-oriented target-tail formulation therefore also closes
the ready-crossing local step. -/
theorem ReadyCrossingSearchInvariant.refinedStep_of_targetTailReturn
    {target : Nat} {node : PhaseSearchNode}
    (h : ReadyCrossingSearchInvariant target node)
    (hreturn : TargetTailReturnHypothesis target) :
    (∃ witness, a witness = target) ∨
      ∃ child, OrbitReadyRefinedInvariant target child ∧
        PhaseSearchProgress target child node := by
  exact h.refinedStep_of_tailDowncross
    (readyCrossingTailDowncross_of_targetTailReturn hreturn)

end Recaman
