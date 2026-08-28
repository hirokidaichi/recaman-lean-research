import Recaman.NormalSemanticBoundary
import Recaman.PhaseProgress

namespace Recaman

/-! # Provenance-aware ordinary normal nodes

`NormalSearchInvariant` is a useful certificate for a historical anchor, but
it does not say that the anchor is the actual orbit value at the node horizon.
This module separates the two legitimate ways in which an ordinary normal
node enters the search:

* a current node carries `OrbitReadyNormalInvariant`, and hence represents the
  actual orbit state at its horizon;
* a historical node carries both its ordinary certificate and provenance from
  a trusted semantic root or an earlier provenance-aware normal node, together
  with the strict phase-search rank step by which it was reached.

Thus a bare historical `NormalSearchInvariant` is not enough to enter the
refined domain.  The construction is intentionally only a domain API; it does
not assert that every provenance-aware node has a semantic successor.
-/

/-- Non-normal semantic nodes which may legitimately produce a historical
normal child.  Ordinary normal nodes are deliberately absent: their recursive
closure is represented by `ProvenancedNormalInvariant.historical_from_normal`
below, so a weak `NormalSearchInvariant` can never serve as its own root. -/
inductive NormalProvenanceRoot
    (target : Nat) (node : PhaseSearchNode) : Prop
  | canonical_start
      (certificate : TargetStartInvariant target node) :
      NormalProvenanceRoot target node
  | debt
      (value firstTime : Nat)
      (certificate : DebtInvariant target node value firstTime) :
      NormalProvenanceRoot target node
  | crossing_recovery
      (certificate : CrossingSearchInvariant target node) :
      NormalProvenanceRoot target node

/-- Exact data retained by one provenance-producing normal transition.

The child is an ordinary semantic normal node, and the parent-to-child edge is
an actual decrease of the global phase-search rank. -/
structure HistoricalNormalStep
    (target : Nat) (parent child : PhaseSearchNode) : Prop where
  certificate : NormalSearchInvariant target child
  progress : PhaseSearchProgress target child parent

/-- Refined ordinary-normal domain.

This is the least domain containing orbit-ready current nodes and normal
children reached by a finite chain of certified rank steps from either such a
node or a non-normal semantic root. -/
inductive ProvenancedNormalInvariant
    (target : Nat) : PhaseSearchNode → Prop
  | current {node : PhaseSearchNode}
      (certificate : OrbitReadyNormalInvariant target node) :
      ProvenancedNormalInvariant target node
  | historical_from_root {parent child : PhaseSearchNode}
      (source : NormalProvenanceRoot target parent)
      (step : HistoricalNormalStep target parent child) :
      ProvenancedNormalInvariant target child
  | historical_from_normal {parent child : PhaseSearchNode}
      (source : ProvenancedNormalInvariant target parent)
      (step : HistoricalNormalStep target parent child) :
      ProvenancedNormalInvariant target child

/-- Every trusted non-normal root is already a member of the existing
combined semantic domain. -/
theorem NormalProvenanceRoot.toPhaseSemanticInvariant
    {target : Nat} {node : PhaseSearchNode}
    (h : NormalProvenanceRoot target node) :
    PhaseSemanticInvariant target node := by
  cases h with
  | canonical_start hstart => exact .canonical_start hstart
  | debt value firstTime hdebt => exact .debt value firstTime hdebt
  | crossing_recovery hcrossing => exact .crossing_recovery hcrossing

/-- The target positivity retained by every historical transition. -/
theorem HistoricalNormalStep.target_positive
    {target : Nat} {parent child : PhaseSearchNode}
    (h : HistoricalNormalStep target parent child) :
    0 < target := by
  rcases h.certificate with ⟨value, firstTime, q, r, hcert⟩
  exact hcert.target_positive

/-- A historical transition embeds its child in the old semantic domain, but
only after its provenance has separately justified admission to the refined
domain. -/
theorem HistoricalNormalStep.toPhaseSemanticInvariant
    {target : Nat} {parent child : PhaseSearchNode}
    (h : HistoricalNormalStep target parent child) :
    PhaseSemanticInvariant target child :=
  .normal h.certificate

/-- Forgetting provenance recovers exactly the older ordinary-normal
certificate. -/
theorem ProvenancedNormalInvariant.toNormalSearchInvariant
    {target : Nat} {node : PhaseSearchNode}
    (h : ProvenancedNormalInvariant target node) :
    NormalSearchInvariant target node := by
  cases h with
  | current hcurrent =>
      rcases hcurrent with ⟨time, q, r, hcert⟩
      exact hcert.toNormalSearchInvariant
  | historical_from_root _ hstep => exact hstep.certificate
  | historical_from_normal _ hstep => exact hstep.certificate

/-- Target positivity is an invariant of the entire refined normal domain,
including every recursively provenance-tagged historical child. -/
theorem ProvenancedNormalInvariant.target_positive
    {target : Nat} {node : PhaseSearchNode}
    (h : ProvenancedNormalInvariant target node) :
    0 < target := by
  rcases h.toNormalSearchInvariant with
    ⟨value, firstTime, q, r, hcert⟩
  exact hcert.target_positive

/-- The refined normal domain is a conservative strengthening of the normal
constructor of `PhaseSemanticInvariant`. -/
theorem ProvenancedNormalInvariant.toPhaseSemanticInvariant
    {target : Nat} {node : PhaseSearchNode}
    (h : ProvenancedNormalInvariant target node) :
    PhaseSemanticInvariant target node :=
  .normal h.toNormalSearchInvariant

/-- Every orbit-ready current node enters the refined domain directly. -/
theorem OrbitReadyNormalInvariant.toProvenancedNormalInvariant
    {target : Nat} {node : PhaseSearchNode}
    (h : OrbitReadyNormalInvariant target node) :
    ProvenancedNormalInvariant target node :=
  .current h

/-- Canonical starts are orbit-ready: their start certificate already stores
the actual node shape, time bound, value bound, and current coordinates. -/
theorem TargetStartInvariant.toOrbitReadyNormalInvariant
    {target : Nat} (htarget : 0 < target) {node : PhaseSearchNode}
    (h : TargetStartInvariant target node) :
    OrbitReadyNormalInvariant target node := by
  rcases h with ⟨time, rfl, hstart⟩
  rcases hstart.witnesses with ⟨q, r, firstTime, hcoord, _, _⟩
  exact ⟨time, q, r, {
    target_positive := htarget
    node_eq := rfl
    time_ready := hstart.time_ready
    target_le_value := hstart.value_ready
    coordinates := hcoord
  }⟩

/-- In particular, every positive canonical start belongs to the refined
ordinary-normal domain without passing through a historical constructor. -/
theorem TargetStartInvariant.toProvenancedNormalInvariant
    {target : Nat} (htarget : 0 < target) {node : PhaseSearchNode}
    (h : TargetStartInvariant target node) :
    ProvenancedNormalInvariant target node :=
  .current (h.toOrbitReadyNormalInvariant htarget)

/-- Package a first-occurring anchor and an already proved rank decrease as a
single historical-normal transition. -/
theorem historicalNormalStep_of_firstAt
    {target : Nat} (htarget : 0 < target)
    {parent : PhaseSearchNode} {horizon value firstTime : Nat}
    (htargetValue : target ≤ value)
    (hfirst : FirstAt a value firstTime)
    (htime : firstTime ≤ horizon)
    (hprogress : PhaseSearchProgress target
      ⟨horizon, value, .normal, value⟩ parent) :
    HistoricalNormalStep target parent
      ⟨horizon, value, .normal, value⟩ := {
  certificate := firstAt_normalSearchInvariant htarget htargetValue
    hfirst htime
  progress := hprogress
}

/-- A certified debt self-exit is a representative historical entry: it keeps
the first-occurring debt value as anchor at the debt horizon, and its debt
certificate is retained as the non-normal provenance root. -/
theorem DebtInvariant.selfExit_provenancedNormal
    {target value firstTime : Nat} {parent : PhaseSearchNode}
    (htarget : 0 < target)
    (h : DebtInvariant target parent value firstTime) :
    let child : PhaseSearchNode :=
      ⟨parent.horizon, value, .normal, value⟩
    ProvenancedNormalInvariant target child := by
  let child : PhaseSearchNode :=
    ⟨parent.horizon, value, .normal, value⟩
  have hsemantic := debtInvariant_selfExit_phaseSemantic htarget h
  have hstep : HistoricalNormalStep target parent child := {
    certificate := by
      have htime : firstTime ≤ parent.horizon :=
        Nat.le_of_lt h.firstTime_lt_horizon
      exact firstAt_normalSearchInvariant htarget h.target_le h.first htime
    progress := hsemantic.2
  }
  exact .historical_from_root (.debt value firstTime h) hstep

/-- A normal parent-drop retains enough first-occurrence information to enter
the refined domain from a provenance-aware current/history chain. -/
theorem NormalParentDropEvidence.toProvenancedNormal
    {target n activeParent horizon value firstTime : Nat}
    (htarget : 0 < target)
    (hparent : ProvenancedNormalInvariant target
      ⟨n, activeParent, .normal, a n⟩)
    (h : NormalParentDropEvidence target horizon value firstTime
      ⟨n, activeParent, .normal, a n⟩
      ⟨horizon, value, .normal, a horizon⟩) :
    let child : PhaseSearchNode :=
      ⟨max horizon firstTime, value, .normal, value⟩
    ProvenancedNormalInvariant target child := by
  let child : PhaseSearchNode :=
    ⟨max horizon firstTime, value, .normal, value⟩
  have hclosure := normalParentDrop_phaseSemantic htarget h
  have hstep : HistoricalNormalStep target
      ⟨n, activeParent, .normal, a n⟩ child := {
    certificate := firstAt_normalSearchInvariant htarget
      h.target_le_anchor h.anchor_first (Nat.le_max_right _ _)
    progress := hclosure.2
  }
  exact .historical_from_normal hparent hstep

/-- The concrete mismatch from `NormalSemanticBoundary` cannot enter through
the current-state constructor.  If it ever belongs to the refined domain, its
proof must expose an explicit historical parent and rank-decreasing edge. -/
theorem horizonMismatch_provenance_is_historical
    (h : ProvenancedNormalInvariant 1 ⟨2, 1, .normal, 1⟩) :
    (∃ parent,
      NormalProvenanceRoot 1 parent ∧
        HistoricalNormalStep 1 parent ⟨2, 1, .normal, 1⟩) ∨
      ∃ parent,
        ProvenancedNormalInvariant 1 parent ∧
          HistoricalNormalStep 1 parent ⟨2, 1, .normal, 1⟩ := by
  cases h with
  | current hcurrent =>
      exact False.elim
        (normalSearchInvariant_not_orbitReady.2 hcurrent)
  | historical_from_root source step =>
      exact Or.inl ⟨_, source, step⟩
  | historical_from_normal source step =>
      exact Or.inr ⟨_, source, step⟩

end Recaman
