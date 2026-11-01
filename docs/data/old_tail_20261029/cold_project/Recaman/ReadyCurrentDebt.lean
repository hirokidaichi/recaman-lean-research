import Recaman.ReadyDebtInvariant

namespace Recaman

/-! # Refined ready-current/debt domain

Coverage from a target-ready current node has a sharp future/earlier split.
The future child is orbit-ready; the earlier child is strong debt at the
unchanged parent horizon.  This module passes the parent's clock certificate
to that debt child before the coverage outcome forgets its source.

Ready debt continuation then remains in the same domain because it keeps the
history horizon fixed.  Existing `DebtStepObstruction`s remain explicit.
-/

/-- Refined recursive domain containing actual target-ready current states
and strong debt states whose fixed history horizon is target-ready. -/
def ReadyCurrentOrDebtInvariant
    (target : Nat) (node : PhaseSearchNode) : Prop :=
  OrbitReadyNormalInvariant target node ∨
    ∃ value firstTime, ReadyDebtInvariant target node value firstTime

/-- Forgetting debt readiness embeds the refined domain in the earlier
current/debt domain. -/
theorem ReadyCurrentOrDebtInvariant.toCurrentOrDebtInvariant
    {target : Nat} {node : PhaseSearchNode}
    (h : ReadyCurrentOrDebtInvariant target node) :
    CurrentOrDebtInvariant target node := by
  rcases h with hcurrent | ⟨value, firstTime, hdebt⟩
  · exact Or.inl hcurrent
  · exact Or.inr ⟨value, firstTime, hdebt.debt⟩

/-- Every refined node belongs to the existing broad semantic domain. -/
theorem ReadyCurrentOrDebtInvariant.toPhaseSemanticInvariant
    {target : Nat} {node : PhaseSearchNode}
    (h : ReadyCurrentOrDebtInvariant target node) :
    PhaseSemanticInvariant target node := by
  rcases h with hcurrent | ⟨value, firstTime, hdebt⟩
  · exact hcurrent.toPhaseSemanticInvariant
  · exact hdebt.toPhaseSemanticInvariant

/-- Convert an already classified coverage outcome while the parent's clock
certificate is still in scope.  This is the integration point which prevents
the earlier debt child from losing readiness. -/
theorem CoverageCurrentDebtOutcome.toReadyCurrentOrDebtStep
    {target n : Nat}
    (hparent : CurrentCoverageParentCertificate target n)
    (h : CoverageCurrentDebtOutcome target n) :
    (∃ witness, a witness = target) ∨
      ∃ child, ReadyCurrentOrDebtInvariant target child ∧
        PhaseSearchProgress target child (targetStartNode n) := by
  cases h with
  | target_occurs witness hvalue =>
      exact Or.inl ⟨witness, hvalue⟩
  | current_child value firstTime hcurrent =>
      exact Or.inr ⟨targetStartNode firstTime,
        Or.inl hcurrent.invariant, hcurrent.progress⟩
  | debt_child value firstTime hdebt =>
      have hready : ReadyDebtInvariant target
          ⟨n, a n, .debt, firstTime⟩ value firstTime :=
        hdebt.toReadyDebtInvariant hparent.time_ready
      exact Or.inr ⟨⟨n, a n, .debt, firstTime⟩,
        Or.inr ⟨value, firstTime, hready⟩, hdebt.progress⟩

/-- Direct coverage bridge from a ready current-parent certificate.  Every
non-target branch is a strict step preserving the refined ready domain. -/
theorem coverageStep_readyCurrentOrDebt
    {target n : Nat}
    (hparent : CurrentCoverageParentCertificate target n)
    (hcoverage : CoverageStep target (a n) n) :
    (∃ witness, a witness = target) ∨
      ∃ child, ReadyCurrentOrDebtInvariant target child ∧
        PhaseSearchProgress target child (targetStartNode n) :=
  CoverageCurrentDebtOutcome.toReadyCurrentOrDebtStep hparent
    (coverageStep_currentOrDebt hparent hcoverage)

/-- Canonical target-start wrapper. -/
theorem coverageStep_targetStart_readyCurrentOrDebt
    {target n : Nat} (htarget : 0 < target)
    (hstart : TargetStartCertificate target n)
    (hcoverage : CoverageStep target (a n) n) :
    (∃ witness, a witness = target) ∨
      ∃ child, ReadyCurrentOrDebtInvariant target child ∧
        PhaseSearchProgress target child (targetStartNode n) :=
  coverageStep_readyCurrentOrDebt
    (hstart.toCurrentCoverageParentCertificate htarget) hcoverage

/-- Orbit-ready current-parent wrapper.  The actual node shape ensures that
the same horizon bound reaches any debt child. -/
theorem coverageStep_orbitReady_readyCurrentOrDebt
    {target n : Nat}
    (hparent : OrbitReadyNormalInvariant target (targetStartNode n))
    (hcoverage : CoverageStep target (a n) n) :
    (∃ witness, a witness = target) ∨
      ∃ child, ReadyCurrentOrDebtInvariant target child ∧
        PhaseSearchProgress target child (targetStartNode n) :=
  coverageStep_readyCurrentOrDebt
    hparent.toCurrentCoverageParentCertificate hcoverage

/-- Forget a ready-debt closed outcome to a refined-domain step while
retaining the existing crossing obstruction verbatim. -/
theorem ReadyDebtClosedOutcome.toReadyCurrentOrDebtStep_or_obstruction
    {target horizon anchor value firstTime : Nat}
    (h : ReadyDebtClosedOutcome target horizon anchor value firstTime) :
    (∃ witness, a witness = target) ∨
      (∃ child, ReadyCurrentOrDebtInvariant target child ∧
        PhaseSearchProgress target child
          ⟨horizon, anchor, .debt, firstTime⟩) ∨
      DebtStepObstruction target horizon anchor value firstTime := by
  cases h with
  | target_occurs witness hvalue =>
      exact Or.inl ⟨witness, hvalue⟩
  | continue_debt childValue childTime hchild hprogress =>
      exact Or.inr (Or.inl
        ⟨⟨horizon, anchor, .debt, childTime⟩,
          Or.inr ⟨childValue, childTime, hchild⟩, hprogress⟩)
  | crossing hobstruction =>
      exact Or.inr (Or.inr hobstruction)

/-- Ready debt local step in the refined ready-current/debt domain.  Ordinary
continuation preserves the domain; the three existing crossing shapes remain
the only residuals. -/
theorem ReadyDebtInvariant.readyCurrentOrDebtStep_or_obstruction
    {target horizon anchor value firstTime : Nat}
    (htarget : 0 < target)
    (h : ReadyDebtInvariant target
      ⟨horizon, anchor, .debt, firstTime⟩ value firstTime) :
    (∃ witness, a witness = target) ∨
      (∃ child, ReadyCurrentOrDebtInvariant target child ∧
        PhaseSearchProgress target child
          ⟨horizon, anchor, .debt, firstTime⟩) ∨
      DebtStepObstruction target horizon anchor value firstTime :=
  ReadyDebtClosedOutcome.toReadyCurrentOrDebtStep_or_obstruction
    (readyDebtStep_classify_without_normalExit htarget h)

end Recaman
