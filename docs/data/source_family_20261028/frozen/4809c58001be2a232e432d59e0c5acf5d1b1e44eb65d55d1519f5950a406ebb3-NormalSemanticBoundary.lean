import Recaman.NormalComplete

namespace Recaman

/-! # Ordinary-normal semantic boundary

`NormalSearchCertificate` certifies an anchor by one of its first
occurrences, but it does not assert that the node's history horizon represents
that anchor as the current orbit state.  Nor does it carry the absolute-time
bound required by the epoch APIs.  The examples and replacement certificate
below make this boundary explicit.
-/

/-- The ordinary certificate can pair the first occurrence of one with a
later horizon whose actual orbit value is three.  Its coordinates therefore
describe time one, not the node horizon. -/
theorem normalSearchInvariant_allows_horizon_value_mismatch :
    NormalSearchInvariant 1 ⟨2, 1, .normal, 1⟩ ∧
      a 2 ≠ 1 := by
  constructor
  · exact ⟨1, 1, 1, 0, {
      target_positive := by decide
      node_eq := rfl
      target_le := by decide
      first := by
        constructor
        · decide
        · intro u hu
          have : u = 0 := by omega
          subst u
          decide
      firstTime_le_horizon := by decide
      coordinates := by
        constructor <;> decide
    }⟩
  · decide

/-- More sharply, the quotient/remainder stored by that valid ordinary
certificate is not a quotient/remainder representation at its horizon. -/
theorem normalSearchCertificate_coordinates_not_at_horizon :
    NormalSearchCertificate 1 ⟨2, 1, .normal, 1⟩ 1 1 1 0 ∧
      ¬ CoordinatesAt 2 1 0 := by
  constructor
  · exact {
      target_positive := by decide
      node_eq := rfl
      target_le := by decide
      first := by
        constructor
        · decide
        · intro u hu
          have : u = 0 := by omega
          subst u
          decide
      firstTime_le_horizon := by decide
      coordinates := by
        constructor <;> decide
    }
  · intro hcoord
    have heq := hcoord.eqn
    have heq' : a 2 = 2 := by omega
    exact (by decide : a 2 ≠ 2) heq'

/-- Even when the node really is the current orbit state and its stored
coordinates happen to be current, the ordinary certificate need not satisfy
the epoch precondition `target ≤ horizon+1`.  The actual state `a 3 = 6`
certifies target six too early. -/
theorem normalSearchInvariant_does_not_imply_time_ready :
    NormalSearchInvariant 6 ⟨3, a 3, .normal, a 3⟩ ∧
      ¬ (6 ≤ 3 + 1) := by
  constructor
  · exact ⟨6, 3, 2, 0, {
      target_positive := by decide
      node_eq := by decide
      target_le := by decide
      first := by
        constructor
        · decide
        · intro u hu
          have hcases : u = 0 ∨ u = 1 ∨ u = 2 := by omega
          rcases hcases with h | h | h <;> subst u <;> decide
      firstTime_le_horizon := by decide
      coordinates := by
        constructor <;> decide
    }⟩
  · omega

/-- Minimal non-circular certificate for entering the epoch machinery from
an ordinary normal node.

It mentions only the actual sequence at the node horizon: canonical node
shape, target/time readiness, and current coordinates.  First-occurrence
evidence is deliberately omitted because it follows from the current history
and can be reconstructed below. -/
structure OrbitReadyNormalCertificate
    (target : Nat) (node : PhaseSearchNode) (time q r : Nat) : Prop where
  target_positive : 0 < target
  node_eq : node = ⟨time, a time, .normal, a time⟩
  time_ready : target ≤ time + 1
  target_le_value : target ≤ a time
  coordinates : CoordinatesAt time q r

def OrbitReadyNormalInvariant
    (target : Nat) (node : PhaseSearchNode) : Prop :=
  ∃ time q r, OrbitReadyNormalCertificate target node time q r

/-- Orbit readiness reconstructs the older ordinary-normal certificate from
the real history.  This direction is non-circular: first occurrence follows
from membership of the current value, and coordinates at that first time
follow from its positivity. -/
theorem OrbitReadyNormalCertificate.toNormalSearchInvariant
    {target : Nat} {node : PhaseSearchNode} {time q r : Nat}
    (h : OrbitReadyNormalCertificate target node time q r) :
    NormalSearchInvariant target node := by
  have htimePositive : 0 < time := by
    by_cases hzero : time = 0
    · subst time
      have htargetValue := h.target_le_value
      have htargetPositive := h.target_positive
      simp [a, stateAt, initial] at htargetValue
      omega
    · omega
  rcases history_member_has_firstAt (current_mem_valuesThrough time) with
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
    ⟨firstQ, firstR, hfirstCoordinates⟩
  refine ⟨a time, firstTime, firstQ, firstR, {
    target_positive := h.target_positive
    node_eq := ?_
    target_le := h.target_le_value
    first := hfirst
    firstTime_le_horizon := ?_
    coordinates := hfirstCoordinates
  }⟩
  · simp [h.node_eq]
  · simpa [h.node_eq] using hfirstTime

/-- The strengthened ordinary certificate embeds directly in the existing
combined semantic domain. -/
theorem OrbitReadyNormalCertificate.toPhaseSemanticInvariant
    {target : Nat} {node : PhaseSearchNode} {time q r : Nat}
    (h : OrbitReadyNormalCertificate target node time q r) :
    PhaseSemanticInvariant target node :=
  .normal h.toNormalSearchInvariant

theorem OrbitReadyNormalInvariant.toPhaseSemanticInvariant
    {target : Nat} {node : PhaseSearchNode}
    (h : OrbitReadyNormalInvariant target node) :
    PhaseSemanticInvariant target node := by
  rcases h with ⟨time, q, r, hcert⟩
  exact hcert.toPhaseSemanticInvariant

/-- In the negative chamber, orbit readiness supplies every field of the
strong normal-phase invariant without any additional history hypothesis.
Thus it is exactly the missing bridge to the existing negative-normal oracle
theorems. -/
theorem OrbitReadyNormalCertificate.toNormalPhaseInvariantAt
    {target : Nat} {node : PhaseSearchNode} {time q r : Nat}
    (h : OrbitReadyNormalCertificate target node time q r)
    (hnegative : potential q r < 0) :
    NormalPhaseInvariantAt target node time q r := by
  refine {
    node_eq := ?_
    time_ready := h.time_ready
    target_le_value := h.target_le_value
    value_le_anchor := ?_
    coordinates := h.coordinates
    negative := hnegative
  }
  · simp [h.node_eq]
  · have hanchor := congrArg PhaseSearchNode.anchorParent h.node_eq
    exact Nat.le_of_eq hanchor.symm

/-- For negative potential, the strengthened certificate is sufficient for
the complete semantic normal step already proved by the epoch analysis. -/
theorem OrbitReadyNormalCertificate.negative_phaseSemanticStep
    {target : Nat} {node : PhaseSearchNode} {time q r : Nat}
    (h : OrbitReadyNormalCertificate target node time q r)
    (hnegative : potential q r < 0) :
    (∃ witness, a witness = target) ∨
      ∃ child, PhaseSemanticInvariant target child ∧
        PhaseSearchProgress target child node := by
  have hinv := h.toNormalPhaseInvariantAt hnegative
  rw [h.node_eq] at hinv ⊢
  exact negativeNormal_phaseSemanticStep h.target_positive hinv

/-- The original ordinary invariant does not imply the strengthened one:
the horizon/value mismatch example fails the required canonical node shape.
This prevents silently treating all current normal semantic nodes as epoch
states. -/
theorem normalSearchInvariant_not_orbitReady :
    NormalSearchInvariant 1 ⟨2, 1, .normal, 1⟩ ∧
      ¬ OrbitReadyNormalInvariant 1 ⟨2, 1, .normal, 1⟩ := by
  refine ⟨normalSearchInvariant_allows_horizon_value_mismatch.1, ?_⟩
  rintro ⟨time, q, r, hready⟩
  have htime : time = 2 := by
    simpa using (congrArg PhaseSearchNode.horizon hready.node_eq).symm
  subst time
  have hanchor := congrArg PhaseSearchNode.anchorParent hready.node_eq
  exact (by decide : (1 : Nat) ≠ a 2) hanchor

end Recaman
