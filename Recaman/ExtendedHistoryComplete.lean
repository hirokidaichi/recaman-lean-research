import Recaman.EarlyRepresentativeComplete
import Recaman.ExtendedHistoryBudgetClosure

namespace Recaman

/-! # Complete extended-history normal step

The minimal extended-history classifier formerly had two residuals.
`EarlyRepresentativeComplete` closes failure of readiness at the
representative time, while `ExtendedHistoryBudgetClosure` turns a strict
history-budget gap into a future crossing-recovery child.  Combining them
gives a total semantic step with the existing phase-search rank.
-/

/-- Every extended-history normal certificate either witnesses the target or
produces a semantic child strictly below it in the existing rank. -/
theorem ExtendedHistoryNormalCertificate.phaseSemanticStep
    {target : Nat} {node : PhaseSearchNode}
    {representativeTime quotient remainder : Nat}
    (h : ExtendedHistoryNormalCertificate target node representativeTime
      quotient remainder) :
    (∃ witness, a witness = target) ∨
      ∃ child, PhaseSemanticInvariant target child ∧
        PhaseSearchProgress target child node := by
  rcases h.phaseSemanticStep_or_readiness with
    hoccurs | hstep | hreadiness
  · exact Or.inl hoccurs
  · exact Or.inr hstep
  · cases hreadiness with
    | representative_not_ready representativeTime quotient remainder
        certificate hnotReady habove =>
        exact
          ExtendedHistoryNormalResidual.representativeNotReady_phaseSemanticStep
            certificate hnotReady habove

/-- Existential packaging preserves totality without exposing the chosen
representative coordinates. -/
theorem ExtendedHistoryNormalInvariant.phaseSemanticStep
    {target : Nat} {node : PhaseSearchNode}
    (h : ExtendedHistoryNormalInvariant target node) :
    (∃ witness, a witness = target) ∨
      ∃ child, PhaseSemanticInvariant target child ∧
        PhaseSearchProgress target child node := by
  rcases h with ⟨representativeTime, quotient, remainder, hcertificate⟩
  exact hcertificate.phaseSemanticStep

/-- A typed historical certificate carries the extended-history data
directly.  Horizon readiness is the only additional premise needed by its
conversion, after which the complete theorem removes every residual. -/
theorem TypedHistoricalNormalCertificate.phaseSemanticStep_of_horizonReady
    {target : Nat} {node : PhaseSearchNode}
    (h : TypedHistoricalNormalCertificate target node)
    (hhorizonReady : target ≤ h.historyHorizon + 1) :
    (∃ witness, a witness = target) ∨
      ∃ child, PhaseSemanticInvariant target child ∧
        PhaseSearchProgress target child node :=
  (h.toExtendedHistory hhorizonReady).phaseSemanticStep

/-- Unified wrapper for all five mechanism-specific historical provenance
constructors.  The generated child is a strict successor of the historical
node itself; callers may compose it with the provenance's source edge when
they need progress from the producing parent. -/
theorem TypedHistoricalNormalProvenance.phaseSemanticStep_of_horizonReady
    {target : Nat} {parent child : PhaseSearchNode}
    (h : TypedHistoricalNormalProvenance target parent child)
    (hhorizonReady :
      target ≤ h.historicalCertificate.historyHorizon + 1) :
    (∃ witness, a witness = target) ∨
      ∃ next, PhaseSemanticInvariant target next ∧
        PhaseSearchProgress target next child :=
  h.historicalCertificate.phaseSemanticStep_of_horizonReady hhorizonReady

/-- Every mechanism-specific constructor retains its original source edge. -/
theorem TypedHistoricalNormalProvenance.sourceProgress
    {target : Nat} {parent child : PhaseSearchNode}
    (h : TypedHistoricalNormalProvenance target parent child) :
    PhaseSearchProgress target child parent := by
  cases h with
  | parent_drop hparent => exact hparent.rank_edge
  | coverage_anchor hcoverage => exact hcoverage.rank_edge
  | downcross_restart hdowncross => exact hdowncross.rank_edge
  | debt_exit hdebt => exact hdebt.rank_edge
  | crossing_frontier hcrossing => exact hcrossing.rank_edge

/-- Compose the complete historical step with the edge which produced the
historical node. -/
theorem TypedHistoricalNormalProvenance.phaseSemanticStep_from_source_of_horizonReady
    {target : Nat} {parent child : PhaseSearchNode}
    (h : TypedHistoricalNormalProvenance target parent child)
    (hhorizonReady :
      target ≤ h.historicalCertificate.historyHorizon + 1) :
    (∃ witness, a witness = target) ∨
      ∃ next, PhaseSemanticInvariant target next ∧
        PhaseSearchProgress target next parent := by
  rcases h.phaseSemanticStep_of_horizonReady hhorizonReady with
    hoccurs | ⟨next, hsemantic, hnext⟩
  · exact Or.inl hoccurs
  · exact Or.inr ⟨next, hsemantic, hnext.trans h.sourceProgress⟩

end Recaman
