import Recaman.AnchorBoundary
import Recaman.CrossingRecovery
import Recaman.PhaseSearchStart

namespace Recaman

/-- Semantic evidence for an ordinary normal-search node.

The numeric tuple deliberately stores only the current anchor/value.  The
first-occurrence time and coordinates at that occurrence are retained
existentially here, together with the fact that the occurrence lies inside
the fixed history horizon. -/
structure NormalSearchCertificate
    (target : Nat) (node : PhaseSearchNode)
    (value firstTime q r : Nat) : Prop where
  target_positive : 0 < target
  node_eq : node =
    ⟨node.horizon, value, .normal, value⟩
  target_le : target ≤ value
  first : FirstAt a value firstTime
  firstTime_le_horizon : firstTime ≤ node.horizon
  coordinates : CoordinatesAt firstTime q r

def NormalSearchInvariant
    (target : Nat) (node : PhaseSearchNode) : Prop :=
  ∃ value firstTime q r,
    NormalSearchCertificate target node value firstTime q r

/-- A strict-crossing recovery node is numerically normal but is not an
ordinary normal-search node: its anchor is the below-target predecessor.
This wrapper remembers the old debt anchor, crossing time, and post-addition
coordinates which the numeric tuple itself cannot encode. -/
structure CrossingSearchCertificate
    (target : Nat) (node : PhaseSearchNode)
    (oldAnchor crossingTime quotient remainder : Nat) : Prop where
  target_positive : 0 < target
  node_eq : node =
    ⟨node.horizon, a crossingTime, .normal, a crossingTime⟩
  recovery : CrossingRecoveryInvariant target node.horizon oldAnchor
    crossingTime quotient remainder

def CrossingSearchInvariant
    (target : Nat) (node : PhaseSearchNode) : Prop :=
  ∃ oldAnchor crossingTime quotient remainder,
    CrossingSearchCertificate target node oldAnchor crossingTime
      quotient remainder

/-- The semantic domain for restricted phase search.

Each constructor is proof-carrying while `PhaseSearchNode` remains a small
numeric rank key.  Canonical starts, ordinary normal nodes, debt nodes, and
strict-crossing recovery nodes can therefore coexist without pretending that
their local invariants are interchangeable. -/
inductive PhaseSemanticInvariant
    (target : Nat) (node : PhaseSearchNode) : Prop
  | canonical_start
      (certificate : TargetStartInvariant target node) :
      PhaseSemanticInvariant target node
  | normal
      (certificate : NormalSearchInvariant target node) :
      PhaseSemanticInvariant target node
  | debt
      (value firstTime : Nat)
      (certificate : DebtInvariant target node value firstTime) :
      PhaseSemanticInvariant target node
  | crossing_recovery
      (certificate : CrossingSearchInvariant target node) :
      PhaseSemanticInvariant target node

/-- Every certified canonical start belongs to the combined semantic domain. -/
theorem targetStartInvariant_phaseSemantic
    {target : Nat} {node : PhaseSearchNode}
    (hstart : TargetStartInvariant target node) :
    PhaseSemanticInvariant target node :=
  .canonical_start hstart

/-- A positive canonical start also carries the generic normal-search
certificate.  In particular, its current value's first occurrence has
canonical coordinates even when it is earlier than the selected start time. -/
theorem targetStartInvariant_normal
    {target : Nat} (htarget : 0 < target) {node : PhaseSearchNode}
    (hstart : TargetStartInvariant target node) :
    NormalSearchInvariant target node := by
  rcases hstart with ⟨n, rfl, hcert⟩
  have htargetValue : target ≤ a n := hcert.value_ready
  rcases hcert.witnesses with ⟨q, r, f, hcoord, hf, hfirst⟩
  have hfPositive : 0 < f := by
    by_cases hfzero : f = 0
    · subst f
      have hvalueZero := firstAt_time_zero_value hfirst
      exact False.elim (by omega)
    · omega
  rcases exists_coordinatesAt hfPositive with ⟨qf, rf, hcoordf⟩
  exact ⟨a n, f, qf, rf, {
    target_positive := htarget
    node_eq := rfl
    target_le := hcert.value_ready
    first := hfirst
    firstTime_le_horizon := hf
    coordinates := hcoordf
  }⟩

/-- Consequently a canonical start can enter the ordinary-normal part of the
same semantic domain without changing its numeric node. -/
theorem targetStartInvariant_phaseSemantic_normal
    {target : Nat} (htarget : 0 < target) {node : PhaseSearchNode}
    (hstart : TargetStartInvariant target node) :
    PhaseSemanticInvariant target node :=
  .normal (targetStartInvariant_normal htarget hstart)

/-- Strong debt always has a domain-preserving self-exit: restart normal
search from the debt value itself.  Its first occurrence is already inside
the fixed horizon, and `value < anchorParent` supplies the strict rank drop.

This theorem makes explicit that any future restriction on such an exit must
be stated as an additional normal invariant; it is not present in the current
numeric rank or semantic certificates. -/
theorem debtInvariant_selfExit_phaseSemantic
    {target value firstTime : Nat} {node : PhaseSearchNode}
    (htarget : 0 < target)
    (hinv : DebtInvariant target node value firstTime) :
    let child : PhaseSearchNode :=
      ⟨node.horizon, value, .normal, value⟩
    PhaseSemanticInvariant target child ∧
      PhaseSearchProgress target child node := by
  let child : PhaseSearchNode :=
    ⟨node.horizon, value, .normal, value⟩
  have htimePositive := debt_firstTime_pos htarget hinv
  rcases exists_coordinatesAt htimePositive with ⟨q, r, hcoord⟩
  have hnormal : NormalSearchInvariant target child := ⟨value, firstTime, q, r, {
    target_positive := htarget
    node_eq := rfl
    target_le := hinv.target_le
    first := hinv.first
    firstTime_le_horizon := Nat.le_of_lt hinv.firstTime_lt_horizon
    coordinates := hcoord
  }⟩
  refine ⟨.normal hnormal, ?_⟩
  rcases node with ⟨horizon, anchor, phase, loc⟩
  have hphase : phase = .debt := hinv.phase_eq
  have hlocal : loc = firstTime := hinv.local_eq
  subst phase
  subst loc
  exact phaseSearch_exitDebt_of_anchorDrop hinv.value_lt_anchor

/-- The length-one `anchor = value+1` boundary is closed inside the semantic
domain.  Equality with the target is a witness; otherwise the landing value
becomes a certified normal child with a strict anchor decrease. -/
theorem anchorBoundary_phaseSemantic_closure
    {target horizon anchor value firstTime : Nat}
    (htarget : 0 < target)
    (hinv : DebtInvariant target
      ⟨horizon, anchor, .debt, firstTime⟩ value firstTime)
    (hanchor : anchor = value + 1) :
    (∃ t, a t = target) ∨
      ∃ child : PhaseSearchNode,
        PhaseSemanticInvariant target child ∧
        PhaseSearchProgress target child
          ⟨horizon, anchor, .debt, firstTime⟩ := by
  rcases anchorBoundary_target_or_exitNormal
      hinv.target_le hinv.first hanchor with hoccurs |
      ⟨_, _, hprogress⟩
  · exact Or.inl hoccurs
  · let child : PhaseSearchNode :=
      ⟨horizon, value, .normal, value⟩
    have htimePositive := debt_firstTime_pos htarget hinv
    rcases exists_coordinatesAt htimePositive with ⟨q, r, hcoord⟩
    have hnormal : NormalSearchInvariant target child :=
      ⟨value, firstTime, q, r, {
      target_positive := htarget
      node_eq := rfl
      target_le := hinv.target_le
      first := hinv.first
      firstTime_le_horizon := Nat.le_of_lt hinv.firstTime_lt_horizon
      coordinates := hcoord
    }⟩
    exact Or.inr ⟨child, .normal hnormal, hprogress⟩

/-- The existing strict-crossing transition preserves the combined semantic
domain by entering its dedicated recovery constructor. -/
theorem debtCrossing_enters_phaseSemantic
    {target horizon anchor value n : Nat}
    (htarget : 0 < target)
    (hinv : DebtInvariant target
      ⟨horizon, anchor, .debt, n + 1⟩ value (n + 1))
    (hnot : ¬ CanSubtract (n + 1) (stateAt n))
    (hbelow : a n < target) :
    (∃ t, a t = target) ∨
      ∃ child : PhaseSearchNode,
        PhaseSemanticInvariant target child ∧
        PhaseSearchProgress target child
          ⟨horizon, anchor, .debt, n + 1⟩ := by
  rcases debtCrossing_enters_recovery hinv hnot hbelow with hoccurs |
      ⟨q, r, hrecovery, hprogress⟩
  · exact Or.inl hoccurs
  · let child : PhaseSearchNode :=
      ⟨horizon, a n, .normal, a n⟩
    have hcrossing : CrossingSearchInvariant target child :=
      ⟨anchor, n, q, r, {
      target_positive := htarget
      node_eq := rfl
      recovery := hrecovery
    }⟩
    exact Or.inr ⟨child, .crossing_recovery hcrossing, hprogress⟩

/-- The combined semantic invariant is directly suitable as the restricted
oracle domain, and every positive target has a node in that domain. -/
theorem exists_phaseSemantic_start
    {target : Nat} (htarget : 0 < target) :
    ∃ node, PhaseSemanticInvariant target node := by
  rcases exists_targetStartNode htarget with ⟨node, hstart⟩
  exact ⟨node, .canonical_start hstart⟩

/-- The concrete restricted-oracle obligation induced by the combined
semantic domain. -/
def SemanticPhaseSearchOracle (target : Nat) : Prop :=
  RestrictedPhaseSearchOracle target (PhaseSemanticInvariant target)

/-- A semantic oracle needs to handle only the four certified node forms
above.  The canonical start theorem then turns it into target occurrence. -/
theorem semanticPhaseSearchOracle_implies_occurs
    {target : Nat} (htarget : 0 < target)
    (horacle : SemanticPhaseSearchOracle target) :
    ∃ t, a t = target := by
  exact targetStart_reaches_of_restrictedOracle htarget
    (PhaseSemanticInvariant target)
    (fun _ hstart => .canonical_start hstart)
    horacle

end Recaman
