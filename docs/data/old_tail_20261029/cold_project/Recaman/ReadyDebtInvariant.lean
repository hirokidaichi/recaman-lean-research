import Recaman.CoverageDebtBridge
import Recaman.HistoricalDebtBridge

namespace Recaman

/-! # Target-ready strong debt

`DebtInvariant` keeps a fixed history horizon while its local first-occurrence
time decreases, but it does not state that the horizon has reached the target
clock.  This module pairs the strong debt certificate with the missing
absolute-time condition.  Since ordinary debt continuation never changes the
horizon, readiness is preserved definitionally across every
`continue_debt` branch of `debtStep_classify_without_normalExit`.
-/

/-- Strong debt together with target readiness at its fixed history horizon.
-/
structure ReadyDebtInvariant
    (target : Nat) (node : PhaseSearchNode)
    (value firstTime : Nat) : Prop where
  debt : DebtInvariant target node value firstTime
  horizon_ready : target ≤ node.horizon + 1

/-- Forget readiness to recover the existing debt domain. -/
theorem ReadyDebtInvariant.toDebtInvariant
    {target value firstTime : Nat} {node : PhaseSearchNode}
    (h : ReadyDebtInvariant target node value firstTime) :
    DebtInvariant target node value firstTime :=
  h.debt

/-- Ready debt embeds in the existing semantic domain without any historical
normal conversion. -/
theorem ReadyDebtInvariant.toPhaseSemanticInvariant
    {target value firstTime : Nat} {node : PhaseSearchNode}
    (h : ReadyDebtInvariant target node value firstTime) :
    PhaseSemanticInvariant target node :=
  .debt value firstTime h.debt

/-- Ready debt also belongs to the refined current/debt domain. -/
theorem ReadyDebtInvariant.toCurrentOrDebtInvariant
    {target value firstTime : Nat} {node : PhaseSearchNode}
    (h : ReadyDebtInvariant target node value firstTime) :
    CurrentOrDebtInvariant target node :=
  Or.inr ⟨value, firstTime, h.debt⟩

/-- A coverage-produced debt child becomes ready from the current parent's
clock bound.  The bound is explicit because `CoverageDebtChildCertificate`
currently forgets the `CurrentCoverageParentCertificate` used to construct
it. -/
theorem CoverageDebtChildCertificate.toReadyDebtInvariant
    {target n value firstTime : Nat}
    (h : CoverageDebtChildCertificate target n value firstTime)
    (htimeReady : target ≤ n + 1) :
    ReadyDebtInvariant target
      ⟨n, a n, .debt, firstTime⟩ value firstTime := {
  debt := h.invariant
  horizon_ready := htimeReady
}

/-- The explicit clock hypothesis above is genuinely necessary for the
current certificate API.  At time nine, value twenty first occurred at time
seven and is below `a 9=21`; it supports target-nineteen strong debt although
the horizon nine clock is not target-ready. -/
theorem coverageDebtChildCertificate_does_not_imply_ready :
    CoverageDebtChildCertificate 19 9 20 7 ∧
      ¬ (19 ≤ 9 + 1) := by
  constructor
  · have hfirst : FirstAt a 20 7 := by
      constructor
      · decide
      · intro u hu
        have hcases : u = 0 ∨ u = 1 ∨ u = 2 ∨ u = 3 ∨ u = 4 ∨
            u = 5 ∨ u = 6 := by omega
        rcases hcases with h | h | h | h | h | h | h <;>
          subst u <;> decide
    have hdebt : DebtInvariant 19 ⟨9, a 9, .debt, 7⟩ 20 7 := {
      phase_eq := rfl
      local_eq := rfl
      target_le := by decide
      first := hfirst
      firstTime_lt_horizon := by decide
      value_lt_anchor := by decide
    }
    exact {
      target_lt_value := by decide
      first := hfirst
      first_time_lt_parent := by decide
      value_lt_parent := by decide
      invariant := hdebt
      semantic := .debt 20 7 hdebt
      progress := phaseSearch_enterDebt
    }
  · decide

/-- Proof-relevant ready-debt classification.  The crossing constructor is
exactly the existing `DebtStepObstruction`; no new obstruction is introduced
by adding horizon readiness. -/
inductive ReadyDebtClosedOutcome
    (target horizon anchor value firstTime : Nat) : Prop
  | target_occurs (witness : Nat) (value_eq : a witness = target) :
      ReadyDebtClosedOutcome target horizon anchor value firstTime
  | continue_debt (childValue childTime : Nat)
      (invariant : ReadyDebtInvariant target
        ⟨horizon, anchor, .debt, childTime⟩ childValue childTime)
      (progress : PhaseSearchProgress target
        ⟨horizon, anchor, .debt, childTime⟩
        ⟨horizon, anchor, .debt, firstTime⟩) :
      ReadyDebtClosedOutcome target horizon anchor value firstTime
  | crossing (obstruction : DebtStepObstruction
      target horizon anchor value firstTime) :
      ReadyDebtClosedOutcome target horizon anchor value firstTime

/-- Every `continue_debt` branch preserves readiness because the debt horizon
is fixed.  Target and obstruction branches are passed through unchanged. -/
theorem readyDebtStep_classify_without_normalExit
    {target horizon anchor value firstTime : Nat}
    (htarget : 0 < target)
    (hinv : ReadyDebtInvariant target
      ⟨horizon, anchor, .debt, firstTime⟩ value firstTime) :
    ReadyDebtClosedOutcome target horizon anchor value firstTime := by
  cases debtStep_classify_without_normalExit htarget hinv.debt with
  | target_occurs witness hvalue =>
      exact .target_occurs witness hvalue
  | continue_debt childValue childTime hchild hprogress =>
      exact .continue_debt childValue childTime {
        debt := hchild
        horizon_ready := by
          simpa using hinv.horizon_ready
      } hprogress
  | crossing hobstruction =>
      exact .crossing hobstruction

/-- Wrapper in the exact target/decreasing-ready-debt/existing-obstruction
shape needed by a refined restricted oracle. -/
theorem ReadyDebtClosedOutcome.toReadyDebtStep_or_obstruction
    {target horizon anchor value firstTime : Nat}
    (h : ReadyDebtClosedOutcome target horizon anchor value firstTime) :
    (∃ witness, a witness = target) ∨
      (∃ childValue childTime,
        ReadyDebtInvariant target
          ⟨horizon, anchor, .debt, childTime⟩ childValue childTime ∧
        PhaseSearchProgress target
          ⟨horizon, anchor, .debt, childTime⟩
          ⟨horizon, anchor, .debt, firstTime⟩) ∨
      DebtStepObstruction target horizon anchor value firstTime := by
  cases h with
  | target_occurs witness hvalue =>
      exact Or.inl ⟨witness, hvalue⟩
  | continue_debt childValue childTime hchild hprogress =>
      exact Or.inr (Or.inl
        ⟨childValue, childTime, hchild, hprogress⟩)
  | crossing hobstruction =>
      exact Or.inr (Or.inr hobstruction)

/-- Direct ready-debt local wrapper, combining classification and forgetting
its proof-relevant outcome in one call. -/
theorem ReadyDebtInvariant.step_or_obstruction
    {target horizon anchor value firstTime : Nat}
    (htarget : 0 < target)
    (h : ReadyDebtInvariant target
      ⟨horizon, anchor, .debt, firstTime⟩ value firstTime) :
    (∃ witness, a witness = target) ∨
      (∃ childValue childTime,
        ReadyDebtInvariant target
          ⟨horizon, anchor, .debt, childTime⟩ childValue childTime ∧
        PhaseSearchProgress target
          ⟨horizon, anchor, .debt, childTime⟩
          ⟨horizon, anchor, .debt, firstTime⟩) ∨
      DebtStepObstruction target horizon anchor value firstTime :=
  ReadyDebtClosedOutcome.toReadyDebtStep_or_obstruction
    (readyDebtStep_classify_without_normalExit htarget h)

end Recaman
