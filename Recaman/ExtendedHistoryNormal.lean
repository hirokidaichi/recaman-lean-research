import Recaman.OrbitReadyComplete
import Recaman.NormalProvenance

namespace Recaman

/-! # Extended-history ordinary normal nodes

An ordinary historical normal node uses an orbit value from a representative
time while measuring its history budget at a later horizon.  Keeping those
times separate exposes two independent preconditions for reusing the complete
orbit-ready local theorem:

* the target must already be time-ready at the representative time;
* the target-missing budget must not have fallen between the representative
  time and the later history horizon.

The final classification below is total for the minimal extended-history
certificate.  It either closes semantically or returns the exact failed
precondition, without treating a historical node as a current orbit state.
-/

/-- Numeric current-state node at the representative orbit time. -/
def extendedHistoryRepresentativeNode (time : Nat) : PhaseSearchNode :=
  ⟨time, a time, .normal, a time⟩

/-- Minimal data for a historical ordinary-normal node.

`representativeTime` is where the stored value and coordinates live;
`node.horizon` is where the missing-value budget is measured.  Only horizon
time-readiness is assumed here, because that is what historical producers
naturally preserve. -/
structure ExtendedHistoryNormalCertificate
    (target : Nat) (node : PhaseSearchNode)
    (representativeTime quotient remainder : Nat) : Prop where
  target_positive : 0 < target
  node_eq : node =
    ⟨node.horizon, a representativeTime, .normal, a representativeTime⟩
  representative_le_horizon : representativeTime ≤ node.horizon
  horizon_time_ready : target ≤ node.horizon + 1
  target_le_value : target ≤ a representativeTime
  coordinates : CoordinatesAt representativeTime quotient remainder

def ExtendedHistoryNormalInvariant
    (target : Nat) (node : PhaseSearchNode) : Prop :=
  ∃ representativeTime quotient remainder,
    ExtendedHistoryNormalCertificate target node representativeTime
      quotient remainder

/-- Once readiness at the representative time is supplied, its actual orbit
state is an orbit-ready normal node. -/
theorem ExtendedHistoryNormalCertificate.toOrbitReadyAtRepresentative
    {target : Nat} {node : PhaseSearchNode}
    {representativeTime quotient remainder : Nat}
    (h : ExtendedHistoryNormalCertificate target node representativeTime
      quotient remainder)
    (hready : target ≤ representativeTime + 1) :
    OrbitReadyNormalCertificate target
      (extendedHistoryRepresentativeNode representativeTime)
      representativeTime quotient remainder := {
  target_positive := h.target_positive
  node_eq := rfl
  time_ready := hready
  target_le_value := h.target_le_value
  coordinates := h.coordinates
}

/-- The minimal extended-history certificate is still a valid instance of
the broad ordinary-normal certificate.  First occurrence is reconstructed at
the representative time and then transported only by the proved time order,
not by pretending the value is current at the later horizon. -/
theorem ExtendedHistoryNormalCertificate.toNormalSearchInvariant
    {target : Nat} {node : PhaseSearchNode}
    {representativeTime quotient remainder : Nat}
    (h : ExtendedHistoryNormalCertificate target node representativeTime
      quotient remainder) :
    NormalSearchInvariant target node := by
  have htimePositive : 0 < representativeTime := by
    by_cases hzero : representativeTime = 0
    · subst representativeTime
      have htargetZero : target ≤ 0 := by
        simpa [a, stateAt, initial] using h.target_le_value
      exact False.elim
        ((Nat.not_lt_of_ge htargetZero) h.target_positive)
    · omega
  rcases history_member_has_firstAt
      (current_mem_valuesThrough representativeTime) with
    ⟨firstTime, hfirstTime, hfirst⟩
  have hfirstPositive : 0 < firstTime := by
    by_cases hzero : firstTime = 0
    · subst firstTime
      have hzeroValue := firstAt_time_zero_value hfirst
      have htargetValue := h.target_le_value
      have htargetPositive := h.target_positive
      omega
    · omega
  rcases exists_coordinatesAt hfirstPositive with
    ⟨firstQuotient, firstRemainder, hfirstCoordinates⟩
  exact ⟨a representativeTime, firstTime, firstQuotient, firstRemainder, {
    target_positive := h.target_positive
    node_eq := h.node_eq
    target_le := h.target_le_value
    first := hfirst
    firstTime_le_horizon :=
      Nat.le_trans hfirstTime h.representative_le_horizon
    coordinates := hfirstCoordinates
  }⟩

theorem ExtendedHistoryNormalCertificate.toPhaseSemanticInvariant
    {target : Nat} {node : PhaseSearchNode}
    {representativeTime quotient remainder : Nat}
    (h : ExtendedHistoryNormalCertificate target node representativeTime
      quotient remainder) :
    PhaseSemanticInvariant target node :=
  .normal h.toNormalSearchInvariant

/-- Equality of the history budgets is exactly enough to transport any local
rank decrease from the representative node to the historical node. -/
theorem ExtendedHistoryNormalCertificate.transportProgress_of_budgetStable
    {target : Nat} {node child : PhaseSearchNode}
    {representativeTime quotient remainder : Nat}
    (h : ExtendedHistoryNormalCertificate target node representativeTime
      quotient remainder)
    (hstable : missingBelowCount target node.horizon =
      missingBelowCount target representativeTime)
    (hprogress : PhaseSearchProgress target child
      (extendedHistoryRepresentativeNode representativeTime)) :
    PhaseSearchProgress target child node := by
  have hanchor : node.anchorParent = a representativeTime := by
    simpa using congrArg PhaseSearchNode.anchorParent h.node_eq
  have hphase : node.phase = .normal := by
    simpa using congrArg PhaseSearchNode.phase h.node_eq
  have hlocal : node.localMeasure = a representativeTime := by
    simpa using congrArg PhaseSearchNode.localMeasure h.node_eq
  change Prod.Lex Nat.lt (Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt))
    (phaseSearchRank target child)
    (missingBelowCount target node.horizon,
      (node.anchorParent, (node.phase.rank, node.localMeasure)))
  change Prod.Lex Nat.lt (Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt))
    (phaseSearchRank target child)
    (missingBelowCount target representativeTime,
      (a representativeTime,
        (SearchPhase.normal.rank, a representativeTime))) at hprogress
  simpa [hstable, hanchor, hphase, hlocal] using hprogress

/-- When the budget has fallen, the rank points in the opposite direction:
the historical node is already strictly below its representative current
node.  Thus a child known only to decrease from the representative node
cannot in general be transported through this gap. -/
theorem ExtendedHistoryNormalCertificate.progress_fromRepresentative_of_budgetGap
    {target : Nat} {node : PhaseSearchNode}
    {representativeTime quotient remainder : Nat}
    (_h : ExtendedHistoryNormalCertificate target node representativeTime
      quotient remainder)
    (hgap : missingBelowCount target node.horizon <
      missingBelowCount target representativeTime) :
    PhaseSearchProgress target node
      (extendedHistoryRepresentativeNode representativeTime) := by
  change Prod.Lex Nat.lt (Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt))
    (phaseSearchRank target node)
    (phaseSearchRank target
      (extendedHistoryRepresentativeNode representativeTime))
  exact Prod.Lex.left _ _ hgap

/-- Complete local closure when both extended-history transport conditions
hold.  This is the strongest direct reuse of the orbit-ready theorem: no
additional phase or rank is introduced. -/
theorem ExtendedHistoryNormalCertificate.phaseSemanticStep_of_ready_stable
    {target : Nat} {node : PhaseSearchNode}
    {representativeTime quotient remainder : Nat}
    (h : ExtendedHistoryNormalCertificate target node representativeTime
      quotient remainder)
    (hready : target ≤ representativeTime + 1)
    (hstable : missingBelowCount target node.horizon =
      missingBelowCount target representativeTime) :
    (∃ witness, a witness = target) ∨
      ∃ child, PhaseSemanticInvariant target child ∧
        PhaseSearchProgress target child node := by
  rcases (h.toOrbitReadyAtRepresentative hready).phaseSemanticStep with
    hoccurs | ⟨child, hsemantic, hprogress⟩
  · exact Or.inl hoccurs
  · exact Or.inr ⟨child, hsemantic,
      h.transportProgress_of_budgetStable hstable hprogress⟩

/-- Exact residuals of the minimal extended-history certificate.

The readiness residual occurs before the orbit-ready theorem can be called.
The budget residual retains the semantic local child and its genuine decrease
from the representative state, showing that only rank transport is missing. -/
inductive ExtendedHistoryNormalResidual
    (target : Nat) (node : PhaseSearchNode) : Prop
  | representative_not_ready
      (representativeTime quotient remainder : Nat)
      (certificate : ExtendedHistoryNormalCertificate target node
        representativeTime quotient remainder)
      (not_ready : representativeTime + 1 < target)
      (value_strictly_above : target < a representativeTime) :
      ExtendedHistoryNormalResidual target node
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
      ExtendedHistoryNormalResidual target node

/-- Total and honest local classification for a single extended-history
certificate.  If representative readiness holds, the complete orbit-ready
analysis is always run; target occurrence is retained even when the history
budget changed.  A non-occurrence child closes globally exactly when the
budget is stable, otherwise the literal transport gap is returned. -/
theorem ExtendedHistoryNormalCertificate.phaseSemanticStep_or_residual
    {target : Nat} {node : PhaseSearchNode}
    {representativeTime quotient remainder : Nat}
    (h : ExtendedHistoryNormalCertificate target node representativeTime
      quotient remainder) :
    (∃ witness, a witness = target) ∨
      (∃ child, PhaseSemanticInvariant target child ∧
        PhaseSearchProgress target child node) ∨
      ExtendedHistoryNormalResidual target node := by
  by_cases hcurrent : a representativeTime = target
  · exact Or.inl ⟨representativeTime, hcurrent⟩
  have habove : target < a representativeTime :=
    Nat.lt_of_le_of_ne h.target_le_value (Ne.symm hcurrent)
  by_cases hready : target ≤ representativeTime + 1
  · rcases (h.toOrbitReadyAtRepresentative hready).phaseSemanticStep with
      hoccurs | ⟨child, hsemantic, hprogress⟩
    · exact Or.inl hoccurs
    · by_cases hstable : missingBelowCount target node.horizon =
          missingBelowCount target representativeTime
      · exact Or.inr (Or.inl ⟨child, hsemantic,
          h.transportProgress_of_budgetStable hstable hprogress⟩)
      · have hbudgetLe := missingBelowCount_antitone
            (m := target) h.representative_le_horizon
        have hgap : missingBelowCount target node.horizon <
            missingBelowCount target representativeTime := by omega
        exact Or.inr (Or.inr (.budget_transport
          representativeTime quotient remainder h hready child hsemantic
          hprogress hgap))
  · exact Or.inr (Or.inr (.representative_not_ready
      representativeTime quotient remainder h (by omega) habove))

/-- Existential wrapper for the complete residual classification. -/
theorem ExtendedHistoryNormalInvariant.phaseSemanticStep_or_residual
    {target : Nat} {node : PhaseSearchNode}
    (h : ExtendedHistoryNormalInvariant target node) :
    (∃ witness, a witness = target) ∨
      (∃ child, PhaseSemanticInvariant target child ∧
        PhaseSearchProgress target child node) ∨
      ExtendedHistoryNormalResidual target node := by
  rcases h with ⟨representativeTime, quotient, remainder, hcert⟩
  exact hcert.phaseSemanticStep_or_residual

/-- Horizon readiness does not imply representative readiness.  The actual
state `a 3 = 6`, reused at horizon four for target five, is the smallest
simple example relevant to the epoch precondition. -/
theorem extendedHistory_horizonReady_not_representativeReady :
    ExtendedHistoryNormalCertificate 5
        ⟨4, a 3, .normal, a 3⟩ 3 2 0 ∧
      ¬ (5 ≤ 3 + 1) := by
  constructor
  · exact {
      target_positive := by decide
      node_eq := rfl
      representative_le_horizon := by decide
      horizon_time_ready := by decide
      target_le_value := by decide
      coordinates := by
        constructor <;> decide
    }
  · omega

/-- Budget transport is a genuine independent boundary.  For target four,
the representative state at time three is already time-ready, but extending
the history through time four discovers the previously missing value two and
strictly lowers the first rank component. -/
theorem extendedHistory_representativeReady_with_budgetGap :
    ExtendedHistoryNormalCertificate 4
        ⟨4, a 3, .normal, a 3⟩ 3 2 0 ∧
      4 ≤ 3 + 1 ∧
      missingBelowCount 4 4 < missingBelowCount 4 3 := by
  refine ⟨?_, by decide, by decide⟩
  exact {
    target_positive := by decide
    node_eq := rfl
    representative_le_horizon := by decide
    horizon_time_ready := by decide
    target_le_value := by decide
    coordinates := by
      constructor <;> decide
  }

end Recaman
