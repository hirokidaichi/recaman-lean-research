import Recaman.EarlyRepresentativeClosure
import Recaman.EarlyForcedCandidateClosure

namespace Recaman

/-! # Complete early-representative semantic step

`EarlyRepresentativeCertificate.classify` has two successful child forms and
two formerly residual transitions.  Legal downcrossing now closes through a
future crossing recovery, and the blocked below-target candidate closes by
starting from its earlier occurrence and taking an upcrossing before the
representative.  Combining those results removes every residual from the
early-time chamber.
-/

/-- Complete local semantic step for a representative whose own clock is not
yet target-ready.  Every result is either an actual target occurrence or a
strict decrease in the existing phase-search rank carrying the existing
combined semantic invariant. -/
theorem EarlyRepresentativeCertificate.phaseSemanticStep
    {target : Nat} {node : PhaseSearchNode}
    {representativeTime quotient remainder : Nat}
    (h : EarlyRepresentativeCertificate target node representativeTime
      quotient remainder) :
    (∃ witness, a witness = target) ∨
      ∃ child, PhaseSemanticInvariant target child ∧
        PhaseSearchProgress target child node := by
  cases h.classify with
  | target_occurs witness hvalue =>
      exact Or.inl ⟨witness, hvalue⟩
  | forward_child child hforward =>
      exact Or.inr ⟨child, hforward.semantic, hforward.progress⟩
  | debt_child value firstTime child childEq hdebt hsemantic hprogress =>
      exact Or.inr ⟨child, hsemantic, hprogress⟩
  | residual hresidual =>
      cases hresidual with
      | legal_downcross representativeTime quotient remainder certificate
          legal hbelow hnextDrop hhistoryGap =>
          rcases EarlyRepresentativeResidual.legalDowncross_phaseSemanticStep
              certificate legal hbelow hnextDrop hhistoryGap with
            hoccurs | ⟨child, _hcrossing, hsemantic, hprogress⟩
          · exact Or.inl hoccurs
          · exact Or.inr ⟨child, hsemantic, hprogress⟩
      | forced_below_candidate representativeTime quotient remainder
          candidate certificate candidateEq candidatePositive candidateBelow
          candidateSeen forced nextValue =>
          exact EarlyRepresentativeResidual.forcedBelowCandidate_phaseSemanticStep
            certificate candidateEq candidatePositive candidateBelow
            candidateSeen forced nextValue

/-- Existentially packaged complete step. -/
theorem EarlyRepresentativeCertificate.completeSemanticStep
    {target : Nat} {node : PhaseSearchNode}
    {representativeTime quotient remainder : Nat}
    (h : EarlyRepresentativeCertificate target node representativeTime
      quotient remainder) :
    (∃ witness, a witness = target) ∨
      ∃ child, PhaseSemanticInvariant target child ∧
        PhaseSearchProgress target child node :=
  h.phaseSemanticStep

/-- Direct adapter for the `representative_not_ready` constructor of the
generic extended-history residual.  Its certificate and strict clock failure
are exactly an `EarlyRepresentativeCertificate`; the additional strict value
field is consistent with, but not needed by, the complete early classifier. -/
theorem ExtendedHistoryNormalResidual.representativeNotReady_phaseSemanticStep
    {target : Nat} {node : PhaseSearchNode}
    {representativeTime quotient remainder : Nat}
    (certificate : ExtendedHistoryNormalCertificate target node
      representativeTime quotient remainder)
    (not_ready : representativeTime + 1 < target)
    (_value_strictly_above : target < a representativeTime) :
    (∃ witness, a witness = target) ∨
      ∃ child, PhaseSemanticInvariant target child ∧
        PhaseSearchProgress target child node := by
  exact (show EarlyRepresentativeCertificate target node representativeTime
      quotient remainder from {
        extended := certificate
        not_ready := not_ready
      }).phaseSemanticStep

/-- Proof-relevant remainder after eliminating the not-ready constructor from
an arbitrary extended-history residual. -/
inductive RemainingExtendedHistoryBudgetTransport
    (target : Nat) (node : PhaseSearchNode) : Prop
  | budget_transport
      (representativeTime quotient remainder : Nat)
      (certificate : ExtendedHistoryNormalCertificate target node
        representativeTime quotient remainder)
      (representative_ready : target ≤ representativeTime + 1)
      (child : PhaseSearchNode)
      (semantic : PhaseSemanticInvariant target child)
      (local_progress : PhaseSearchProgress target child
        (extendedHistoryRepresentativeNode representativeTime))
      (budget_gap : missingBelowCount target node.horizon <
        missingBelowCount target representativeTime) :
      RemainingExtendedHistoryBudgetTransport target node

/-- Exhaustive adapter for the old extended-history residual: the early-clock
case now closes completely, leaving only the independent budget-transport
constructor. -/
theorem ExtendedHistoryNormalResidual.phaseSemanticStep_or_budgetTransport
    {target : Nat} {node : PhaseSearchNode}
    (h : ExtendedHistoryNormalResidual target node) :
    ((∃ witness, a witness = target) ∨
      ∃ child, PhaseSemanticInvariant target child ∧
        PhaseSearchProgress target child node) ∨
      RemainingExtendedHistoryBudgetTransport target node := by
  cases h with
  | representative_not_ready representativeTime quotient remainder
      certificate notReady valueAbove =>
      exact Or.inl
        (ExtendedHistoryNormalResidual.representativeNotReady_phaseSemanticStep
          certificate notReady valueAbove)
  | budget_transport representativeTime quotient remainder certificate
      representativeReady child semantic localProgress budgetGap =>
      exact Or.inr (.budget_transport representativeTime quotient remainder
        certificate representativeReady child semantic localProgress
        budgetGap)

end Recaman
