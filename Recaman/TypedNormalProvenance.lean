import Recaman.ExtendedHistoryNormal
import Recaman.CrossingFrontier

namespace Recaman

noncomputable section

/-! # Mechanism-specific provenance for historical normal nodes

An ordinary `NormalSearchInvariant` remembers only a first occurrence inside
the node horizon.  The local orbit analysis needed by a future total oracle
also needs to know *which actual orbit state* the node represents.  The two
times need not agree: a downcross restart keeps the old orbit state as its
representative while extending the history horizon past the crossing.

`TypedHistoricalNormalCertificate` therefore separates:

* `historyHorizon`, used by the first component of `phaseSearchRank`;
* `representativeTime`, whose actual value and coordinates are analysed;
* `firstTime`, which certifies that the represented value occurs in history.

The five mechanism-specific structures below retain the evidence by which a
historical child was produced.  They provide admission to
`ProvenancedNormalInvariant`, but intentionally do not assert a local
successor theorem.  Such a theorem is the separate extended-history task.
-/

/-- Full orbit data hidden by a bare historical `NormalSearchInvariant`.

The node is anchored at the actual value at `representativeTime`, while its
rank is evaluated at the possibly later `historyHorizon`. -/
structure TypedHistoricalNormalCertificate
    (target : Nat) (node : PhaseSearchNode) : Type where
  historyHorizon : Nat
  representativeTime : Nat
  value : Nat
  firstTime : Nat
  quotient : Nat
  remainder : Nat
  node_eq : node =
    ⟨historyHorizon, value, .normal, value⟩
  value_eq : value = a representativeTime
  target_positive : 0 < target
  target_le_value : target ≤ value
  first : FirstAt a value firstTime
  firstTime_le_history : firstTime ≤ historyHorizon
  representativeTime_le_history : representativeTime ≤ historyHorizon
  coordinates : CoordinatesAt representativeTime quotient remainder

/-- The exact numeric node shape, stated only in terms of the representative
orbit state and the separate history horizon. -/
theorem TypedHistoricalNormalCertificate.node_eq_representative
    {target : Nat} {node : PhaseSearchNode}
    (h : TypedHistoricalNormalCertificate target node) :
    node = ⟨h.historyHorizon, a h.representativeTime, .normal,
      a h.representativeTime⟩ := by
  rcases h with
    ⟨historyHorizon, representativeTime, value, firstTime, quotient,
      remainder, hnode, hvalue, htarget, htargetValue, hfirst,
      hfirstHistory, hrepresentativeHistory, hcoordinates⟩
  simp only
  subst value
  exact hnode

/-- A represented above-target value cannot first occur at time zero. -/
theorem TypedHistoricalNormalCertificate.firstTime_positive
    {target : Nat} {node : PhaseSearchNode}
    (h : TypedHistoricalNormalCertificate target node) :
    0 < h.firstTime := by
  by_cases hzero : h.firstTime = 0
  · have hfirstZero : FirstAt a h.value 0 := by
      simpa [hzero] using h.first
    have hvalue := firstAt_time_zero_value hfirstZero
    have htarget := h.target_positive
    have htargetValue := h.target_le_value
    omega
  · omega

/-- Forgetting representative-state data recovers the old ordinary normal
certificate.  Coordinates at the first occurrence exist independently of
the coordinates retained at the representative state. -/
theorem TypedHistoricalNormalCertificate.toNormalSearchInvariant
    {target : Nat} {node : PhaseSearchNode}
    (h : TypedHistoricalNormalCertificate target node) :
    NormalSearchInvariant target node := by
  rcases exists_coordinatesAt h.firstTime_positive with
    ⟨firstQuotient, firstRemainder, hfirstCoordinates⟩
  rcases h with
    ⟨historyHorizon, representativeTime, value, firstTime, quotient,
      remainder, rfl, hvalue, htarget, htargetValue, hfirst,
      hfirstHistory, hrepresentativeHistory, hcoordinates⟩
  exact ⟨value, firstTime, firstQuotient, firstRemainder, {
    target_positive := htarget
    node_eq := rfl
    target_le := htargetValue
    first := hfirst
    firstTime_le_horizon := hfirstHistory
    coordinates := hfirstCoordinates
  }⟩

/-- Typed historical data conservatively embeds into the old semantic
domain. -/
theorem TypedHistoricalNormalCertificate.toPhaseSemanticInvariant
    {target : Nat} {node : PhaseSearchNode}
    (h : TypedHistoricalNormalCertificate target node) :
    PhaseSemanticInvariant target node :=
  .normal h.toNormalSearchInvariant

/-- The typed package supplies all data required by the minimal
extended-history certificate except its horizon clock bound.  That bound is
kept explicit because strong debt and crossing roots do not currently imply
it. -/
theorem TypedHistoricalNormalCertificate.toExtendedHistory
    {target : Nat} {node : PhaseSearchNode}
    (h : TypedHistoricalNormalCertificate target node)
    (hhorizonReady : target ≤ h.historyHorizon + 1) :
    ExtendedHistoryNormalCertificate target node h.representativeTime
      h.quotient h.remainder := by
  exact {
    target_positive := h.target_positive
    node_eq := by
      have hshape := h.node_eq_representative
      have hhorizon : node.horizon = h.historyHorizon := by
        simpa using congrArg PhaseSearchNode.horizon hshape
      simpa [hhorizon] using hshape
    representative_le_horizon := by
      have hhorizon : node.horizon = h.historyHorizon := by
        simpa using congrArg PhaseSearchNode.horizon
          h.node_eq_representative
      simpa [hhorizon] using h.representativeTime_le_history
    horizon_time_ready := by
      have hhorizon : node.horizon = h.historyHorizon := by
        simpa using congrArg PhaseSearchNode.horizon
          h.node_eq_representative
      simpa [hhorizon] using hhorizonReady
    target_le_value := by simpa [← h.value_eq] using h.target_le_value
    coordinates := h.coordinates
  }

/-- Honest local classification inherited from the extended-history audit.
The result may retain a representative-readiness or budget-transport
residual; no unconditional successor is claimed. -/
theorem TypedHistoricalNormalCertificate.phaseSemanticStep_or_residual
    {target : Nat} {node : PhaseSearchNode}
    (h : TypedHistoricalNormalCertificate target node)
    (hhorizonReady : target ≤ h.historyHorizon + 1) :
    (∃ witness, a witness = target) ∨
      (∃ child, PhaseSemanticInvariant target child ∧
        PhaseSearchProgress target child node) ∨
      ExtendedHistoryNormalResidual target node :=
  (h.toExtendedHistory hhorizonReady).phaseSemanticStep_or_residual

/-- Pair typed historical data with its exact parent-to-child rank edge. -/
theorem TypedHistoricalNormalCertificate.toHistoricalNormalStep
    {target : Nat} {parent child : PhaseSearchNode}
    (h : TypedHistoricalNormalCertificate target child)
    (hprogress : PhaseSearchProgress target child parent) :
    HistoricalNormalStep target parent child := {
  certificate := h.toNormalSearchInvariant
  progress := hprogress
}

/-- A current representative can be promoted to the orbit-ready domain once
the missing clock bound is supplied explicitly. -/
theorem TypedHistoricalNormalCertificate.toOrbitReady_of_current
    {target : Nat} {node : PhaseSearchNode}
    (h : TypedHistoricalNormalCertificate target node)
    (hcurrent : h.representativeTime = h.historyHorizon)
    (htimeReady : target ≤ h.representativeTime + 1) :
    OrbitReadyNormalInvariant target node := by
  rcases h with
    ⟨historyHorizon, representativeTime, value, firstTime, quotient,
      remainder, hnode, hvalue, htarget, htargetValue, hfirst,
      hfirstHistory, hrepresentativeHistory, hcoordinates⟩
  simp only at hcurrent htimeReady
  subst historyHorizon
  subst value
  exact ⟨representativeTime, quotient, remainder, {
    target_positive := htarget
    node_eq := hnode
    time_ready := htimeReady
    target_le_value := htargetValue
    coordinates := hcoordinates
  }⟩

/-! ## Parent-drop provenance -/

/-- A historical child generated by the parent-anchor descent branch. -/
structure ParentDropNormalProvenance
    (target : Nat) (parent child : PhaseSearchNode) : Type where
  source : ProvenancedNormalInvariant target parent
  certificate : TypedHistoricalNormalCertificate target child
  rawHorizon : Nat
  evidence : NormalParentDropEvidence target rawHorizon certificate.value
    certificate.firstTime parent
    ⟨rawHorizon, certificate.value, .normal, a rawHorizon⟩
  rank_edge : PhaseSearchProgress target child parent

/-- The existing `NormalParentDropEvidence` produces the typed parent-drop
constructor.  Its first occurrence is used as the representative state; the
rank horizon is enlarged independently. -/
noncomputable def parentDropNormalProvenance_of_evidence
    {target parentTime activeParent rawHorizon value firstTime : Nat}
    (htarget : 0 < target)
    (hsource : ProvenancedNormalInvariant target
      ⟨parentTime, activeParent, .normal, a parentTime⟩)
    (hevidence : NormalParentDropEvidence target rawHorizon value firstTime
      ⟨parentTime, activeParent, .normal, a parentTime⟩
      ⟨rawHorizon, value, .normal, a rawHorizon⟩) :
    let child : PhaseSearchNode :=
      ⟨max rawHorizon firstTime, value, .normal, value⟩
    ParentDropNormalProvenance target
      ⟨parentTime, activeParent, .normal, a parentTime⟩ child := by
  let child : PhaseSearchNode :=
    ⟨max rawHorizon firstTime, value, .normal, value⟩
  have hfirstPositive : 0 < firstTime := by
    by_cases hzero : firstTime = 0
    · subst firstTime
      have hvalueZero := firstAt_time_zero_value hevidence.anchor_first
      have htargetValue := hevidence.target_le_anchor
      omega
    · omega
  have hexists := exists_coordinatesAt hfirstPositive
  let q := Classical.choose hexists
  let r := Classical.choose (Classical.choose_spec hexists)
  have hcoordinates : CoordinatesAt firstTime q r :=
    Classical.choose_spec (Classical.choose_spec hexists)
  have hclosure := normalParentDrop_phaseSemantic htarget hevidence
  exact {
    source := hsource
    certificate := {
      historyHorizon := max rawHorizon firstTime
      representativeTime := firstTime
      value := value
      firstTime := firstTime
      quotient := q
      remainder := r
      node_eq := rfl
      value_eq := hevidence.anchor_first.1.symm
      target_positive := htarget
      target_le_value := hevidence.target_le_anchor
      first := hevidence.anchor_first
      firstTime_le_history := Nat.le_max_right _ _
      representativeTime_le_history := Nat.le_max_right _ _
      coordinates := hcoordinates
    }
    rawHorizon := rawHorizon
    evidence := hevidence
    rank_edge := hclosure.2
  }

theorem ParentDropNormalProvenance.toProvenancedNormalInvariant
    {target : Nat} {parent child : PhaseSearchNode}
    (h : ParentDropNormalProvenance target parent child) :
    ProvenancedNormalInvariant target child :=
  .historical_from_normal h.source
    (h.certificate.toHistoricalNormalStep h.rank_edge)

/-! ## Coverage-anchor provenance -/

/-- A selected non-target branch of `CoverageStep`.  The intermediate
covered value is retained separately from the smaller historical anchor. -/
structure CoverageAnchorNormalProvenance
    (target : Nat) (parent child : PhaseSearchNode) : Type where
  source : ProvenancedNormalInvariant target parent
  certificate : TypedHistoricalNormalCertificate target child
  coveredValue : Nat
  coveredTime : Nat
  target_le_anchor : target ≤ certificate.value
  anchor_first : FirstAt a certificate.value certificate.firstTime
  anchor_lt_covered : certificate.value < coveredValue
  covered_le_parent_anchor : coveredValue ≤ parent.anchorParent
  parentHorizon_le_history : parent.horizon ≤ certificate.historyHorizon
  rank_edge : PhaseSearchProgress target child parent

/-- Build coverage provenance at an enlarged horizon from the blocker branch
of `CoverageStep`.  The old normal parent supplies the strict anchor edge. -/
noncomputable def coverageAnchorNormalProvenance_of_blocker
    {target parentHorizon parentAnchor parentLocal coveredValue value
      firstTime : Nat}
    (htarget : 0 < target)
    (hsource : ProvenancedNormalInvariant target
      ⟨parentHorizon, parentAnchor, .normal, parentLocal⟩)
    (htargetValue : target ≤ value)
    (hfirst : FirstAt a value firstTime)
    (hvalueCovered : value < coveredValue)
    (hcoveredAnchor : coveredValue ≤ parentAnchor) :
    let child : PhaseSearchNode :=
      ⟨max parentHorizon firstTime, value, .normal, value⟩
    CoverageAnchorNormalProvenance target
      ⟨parentHorizon, parentAnchor, .normal, parentLocal⟩ child := by
  let child : PhaseSearchNode :=
    ⟨max parentHorizon firstTime, value, .normal, value⟩
  have hfirstPositive : 0 < firstTime := by
    by_cases hzero : firstTime = 0
    · subst firstTime
      have hvalueZero := firstAt_time_zero_value hfirst
      omega
    · omega
  have hexists := exists_coordinatesAt hfirstPositive
  let q := Classical.choose hexists
  let r := Classical.choose (Classical.choose_spec hexists)
  have hcoordinates : CoordinatesAt firstTime q r :=
    Classical.choose_spec (Classical.choose_spec hexists)
  have hanchorDrop : value < parentAnchor :=
    Nat.lt_of_lt_of_le hvalueCovered hcoveredAnchor
  exact {
    source := hsource
    certificate := {
      historyHorizon := max parentHorizon firstTime
      representativeTime := firstTime
      value := value
      firstTime := firstTime
      quotient := q
      remainder := r
      node_eq := rfl
      value_eq := hfirst.1.symm
      target_positive := htarget
      target_le_value := htargetValue
      first := hfirst
      firstTime_le_history := Nat.le_max_right _ _
      representativeTime_le_history := Nat.le_max_right _ _
      coordinates := hcoordinates
    }
    coveredValue := coveredValue
    coveredTime := parentHorizon
    target_le_anchor := htargetValue
    anchor_first := hfirst
    anchor_lt_covered := hvalueCovered
    covered_le_parent_anchor := hcoveredAnchor
    parentHorizon_le_history := Nat.le_max_left _ _
    rank_edge := phaseSearchProgress_of_horizonAndAnchor
      (Nat.le_max_left _ _) hanchorDrop
  }

theorem CoverageAnchorNormalProvenance.toProvenancedNormalInvariant
    {target : Nat} {parent child : PhaseSearchNode}
    (h : CoverageAnchorNormalProvenance target parent child) :
    ProvenancedNormalInvariant target child :=
  .historical_from_normal h.source
    (h.certificate.toHistoricalNormalStep h.rank_edge)

/-! ## Downcross-restart provenance -/

/-- A forward orbit segment crossed from an above-target representative to a
below-target endpoint.  The child keeps the old representative value but uses
the later endpoint as its history horizon; strict budget decrease is the
rank edge. -/
structure DowncrossRestartNormalProvenance
    (target : Nat) (parent child : PhaseSearchNode) : Type where
  source : ProvenancedNormalInvariant target parent
  certificate : TypedHistoricalNormalCertificate target child
  parent_eq : parent =
    ⟨certificate.representativeTime, parent.anchorParent, .normal,
      a certificate.representativeTime⟩
  endpoint_below_target : a certificate.historyHorizon < target
  budget_drop :
    missingBelowCount target certificate.historyHorizon <
      missingBelowCount target certificate.representativeTime
  rank_edge : PhaseSearchProgress target child parent

/-- Package the budget-drop branch of `orbit_downcrossing_occurs_or_budgetDrop`.
Unlike coverage provenance, the representative coordinates are coordinates
at the old orbit state rather than at its first occurrence. -/
noncomputable def downcrossRestartNormalProvenance_of_budgetDrop
    {target representativeTime historyHorizon parentAnchor firstTime q r : Nat}
    (htarget : 0 < target)
    (hsource : ProvenancedNormalInvariant target
      ⟨representativeTime, parentAnchor, .normal, a representativeTime⟩)
    (htargetValue : target ≤ a representativeTime)
    (hfirst : FirstAt a (a representativeTime) firstTime)
    (hfirstTime : firstTime ≤ representativeTime)
    (hcoordinates : CoordinatesAt representativeTime q r)
    (htime : representativeTime ≤ historyHorizon)
    (hbelow : a historyHorizon < target)
    (hbudget : missingBelowCount target historyHorizon <
      missingBelowCount target representativeTime) :
    let child : PhaseSearchNode :=
      ⟨historyHorizon, a representativeTime, .normal, a representativeTime⟩
    DowncrossRestartNormalProvenance target
      ⟨representativeTime, parentAnchor, .normal, a representativeTime⟩
      child := by
  let child : PhaseSearchNode :=
    ⟨historyHorizon, a representativeTime, .normal, a representativeTime⟩
  exact {
    source := hsource
    certificate := {
      historyHorizon := historyHorizon
      representativeTime := representativeTime
      value := a representativeTime
      firstTime := firstTime
      quotient := q
      remainder := r
      node_eq := rfl
      value_eq := rfl
      target_positive := htarget
      target_le_value := htargetValue
      first := hfirst
      firstTime_le_history := Nat.le_trans hfirstTime htime
      representativeTime_le_history := htime
      coordinates := hcoordinates
    }
    parent_eq := rfl
    endpoint_below_target := hbelow
    budget_drop := hbudget
    rank_edge := Prod.Lex.left _ _ hbudget
  }

theorem DowncrossRestartNormalProvenance.toProvenancedNormalInvariant
    {target : Nat} {parent child : PhaseSearchNode}
    (h : DowncrossRestartNormalProvenance target parent child) :
    ProvenancedNormalInvariant target child :=
  .historical_from_normal h.source
    (h.certificate.toHistoricalNormalStep h.rank_edge)

/-! ## Debt-exit provenance -/

/-- A strong debt node exits at its stored first-occurring value. -/
structure DebtExitNormalProvenance
    (target : Nat) (parent child : PhaseSearchNode) : Type where
  historyHorizon : Nat
  anchor : Nat
  value : Nat
  firstTime : Nat
  target_positive : 0 < target
  parent_eq : parent =
    ⟨historyHorizon, anchor, .debt, firstTime⟩
  source : DebtInvariant target
    ⟨historyHorizon, anchor, .debt, firstTime⟩ value firstTime
  child_eq : child =
    ⟨historyHorizon, value, .normal, value⟩
  root : NormalProvenanceRoot target parent
  rank_edge : PhaseSearchProgress target child parent

noncomputable def DebtExitNormalProvenance.certificate
    {target : Nat} {parent child : PhaseSearchNode}
    (h : DebtExitNormalProvenance target parent child) :
    TypedHistoricalNormalCertificate target child := by
  have hfirstPositive := debt_firstTime_pos h.target_positive h.source
  have hexists := exists_coordinatesAt hfirstPositive
  let q := Classical.choose hexists
  let r := Classical.choose (Classical.choose_spec hexists)
  have hcoordinates : CoordinatesAt h.firstTime q r :=
    Classical.choose_spec (Classical.choose_spec hexists)
  exact {
    historyHorizon := h.historyHorizon
    representativeTime := h.firstTime
    value := h.value
    firstTime := h.firstTime
    quotient := q
    remainder := r
    node_eq := h.child_eq
    value_eq := h.source.first.1.symm
    target_positive := h.target_positive
    target_le_value := h.source.target_le
    first := h.source.first
    firstTime_le_history := Nat.le_of_lt h.source.firstTime_lt_horizon
    representativeTime_le_history := Nat.le_of_lt
      h.source.firstTime_lt_horizon
    coordinates := hcoordinates
  }

/-- Adapter from every existing strong debt certificate. -/
noncomputable def debtExitNormalProvenance_of_invariant
    {target historyHorizon anchor value firstTime : Nat}
    (htarget : 0 < target)
    (hsource : DebtInvariant target
      ⟨historyHorizon, anchor, .debt, firstTime⟩ value firstTime) :
    DebtExitNormalProvenance target
      ⟨historyHorizon, anchor, .debt, firstTime⟩
      ⟨historyHorizon, value, .normal, value⟩ := {
  historyHorizon := historyHorizon
  anchor := anchor
  value := value
  firstTime := firstTime
  target_positive := htarget
  parent_eq := rfl
  source := hsource
  child_eq := rfl
  root := .debt value firstTime hsource
  rank_edge := phaseSearch_exitDebt_of_anchorDrop hsource.value_lt_anchor
}

theorem DebtExitNormalProvenance.toProvenancedNormalInvariant
    {target : Nat} {parent child : PhaseSearchNode}
    (h : DebtExitNormalProvenance target parent child) :
    ProvenancedNormalInvariant target child := by
  apply ProvenancedNormalInvariant.historical_from_root
    h.root
  exact h.certificate.toHistoricalNormalStep h.rank_edge

/-! ## Crossing-frontier provenance -/

/-- A processed crossing frontier supplied a first-occurring value below the
old debt anchor.  The frontier occurrence may lie beyond the debt horizon, so
the child horizon is the maximum of the two. -/
structure CrossingFrontierNormalProvenance
    (target : Nat) (parent child : PhaseSearchNode) : Type where
  historyHorizon : Nat
  debtAnchor : Nat
  debtValue : Nat
  debtTime : Nat
  frontierValue : Nat
  frontierFirstTime : Nat
  target_positive : 0 < target
  parent_eq : parent =
    ⟨historyHorizon, debtAnchor, .debt, debtTime⟩
  source : DebtInvariant target
    ⟨historyHorizon, debtAnchor, .debt, debtTime⟩ debtValue debtTime
  target_le_frontier : target ≤ frontierValue
  frontier_first : FirstAt a frontierValue frontierFirstTime
  frontier_lt_anchor : frontierValue < debtAnchor
  child_eq : child =
    ⟨max historyHorizon frontierFirstTime, frontierValue, .normal,
      frontierValue⟩
  root : NormalProvenanceRoot target parent
  rank_edge : PhaseSearchProgress target child parent

noncomputable def CrossingFrontierNormalProvenance.certificate
    {target : Nat} {parent child : PhaseSearchNode}
    (h : CrossingFrontierNormalProvenance target parent child) :
    TypedHistoricalNormalCertificate target child := by
  have hfirstPositive : 0 < h.frontierFirstTime := by
    by_cases hzero : h.frontierFirstTime = 0
    · have hfirstZero : FirstAt a h.frontierValue 0 := by
        simpa [hzero] using h.frontier_first
      have hvalueZero := firstAt_time_zero_value hfirstZero
      have htarget := h.target_positive
      have htargetValue := h.target_le_frontier
      omega
    · omega
  have hexists := exists_coordinatesAt hfirstPositive
  let q := Classical.choose hexists
  let r := Classical.choose (Classical.choose_spec hexists)
  have hcoordinates : CoordinatesAt h.frontierFirstTime q r :=
    Classical.choose_spec (Classical.choose_spec hexists)
  exact {
    historyHorizon := max h.historyHorizon h.frontierFirstTime
    representativeTime := h.frontierFirstTime
    value := h.frontierValue
    firstTime := h.frontierFirstTime
    quotient := q
    remainder := r
    node_eq := h.child_eq
    value_eq := h.frontier_first.1.symm
    target_positive := h.target_positive
    target_le_value := h.target_le_frontier
    first := h.frontier_first
    firstTime_le_history := Nat.le_max_right _ _
    representativeTime_le_history := Nat.le_max_right _ _
    coordinates := hcoordinates
  }

/-- Adapter for every successful first-occurrence branch of the processed
crossing frontier. -/
noncomputable def crossingFrontierNormalProvenance_of_firstAt
    {target historyHorizon debtAnchor debtValue debtTime frontierValue
      frontierFirstTime : Nat}
    (htarget : 0 < target)
    (hsource : DebtInvariant target
      ⟨historyHorizon, debtAnchor, .debt, debtTime⟩ debtValue debtTime)
    (htargetFrontier : target ≤ frontierValue)
    (hfirst : FirstAt a frontierValue frontierFirstTime)
    (hanchor : frontierValue < debtAnchor) :
    CrossingFrontierNormalProvenance target
      ⟨historyHorizon, debtAnchor, .debt, debtTime⟩
      ⟨max historyHorizon frontierFirstTime, frontierValue, .normal,
        frontierValue⟩ := {
  historyHorizon := historyHorizon
  debtAnchor := debtAnchor
  debtValue := debtValue
  debtTime := debtTime
  frontierValue := frontierValue
  frontierFirstTime := frontierFirstTime
  target_positive := htarget
  parent_eq := rfl
  source := hsource
  target_le_frontier := htargetFrontier
  frontier_first := hfirst
  frontier_lt_anchor := hanchor
  child_eq := rfl
  root := .debt debtValue debtTime hsource
  rank_edge := phaseSearch_exitDebt_of_extendedHorizonAndAnchor
    (Nat.le_max_left _ _) hanchor
}

theorem CrossingFrontierNormalProvenance.toProvenancedNormalInvariant
    {target : Nat} {parent child : PhaseSearchNode}
    (h : CrossingFrontierNormalProvenance target parent child) :
    ProvenancedNormalInvariant target child := by
  apply ProvenancedNormalInvariant.historical_from_root
    h.root
  exact h.certificate.toHistoricalNormalStep h.rank_edge

/-! ## Unified typed historical domain -/

/-- Proof-relevant union of the five admitted historical mechanisms.

There is deliberately no constructor from a bare `NormalSearchInvariant`.
Every inhabitant exposes both representative-state data and its concrete
generation mechanism. -/
inductive TypedHistoricalNormalProvenance
    (target : Nat) (parent child : PhaseSearchNode) : Type
  | parent_drop
      (certificate : ParentDropNormalProvenance target parent child) :
      TypedHistoricalNormalProvenance target parent child
  | coverage_anchor
      (certificate : CoverageAnchorNormalProvenance target parent child) :
      TypedHistoricalNormalProvenance target parent child
  | downcross_restart
      (certificate : DowncrossRestartNormalProvenance target parent child) :
      TypedHistoricalNormalProvenance target parent child
  | debt_exit
      (certificate : DebtExitNormalProvenance target parent child) :
      TypedHistoricalNormalProvenance target parent child
  | crossing_frontier
      (certificate : CrossingFrontierNormalProvenance target parent child) :
      TypedHistoricalNormalProvenance target parent child

/-- Recover the common representative/history package from any mechanism. -/
noncomputable def TypedHistoricalNormalProvenance.historicalCertificate
    {target : Nat} {parent child : PhaseSearchNode}
    (h : TypedHistoricalNormalProvenance target parent child) :
    TypedHistoricalNormalCertificate target child := by
  cases h with
  | parent_drop hparent => exact hparent.certificate
  | coverage_anchor hcoverage => exact hcoverage.certificate
  | downcross_restart hdowncross => exact hdowncross.certificate
  | debt_exit hdebt => exact hdebt.certificate
  | crossing_frontier hcrossing => exact hcrossing.certificate

theorem TypedHistoricalNormalProvenance.toNormalSearchInvariant
    {target : Nat} {parent child : PhaseSearchNode}
    (h : TypedHistoricalNormalProvenance target parent child) :
    NormalSearchInvariant target child :=
  h.historicalCertificate.toNormalSearchInvariant

theorem TypedHistoricalNormalProvenance.toPhaseSemanticInvariant
    {target : Nat} {parent child : PhaseSearchNode}
    (h : TypedHistoricalNormalProvenance target parent child) :
    PhaseSemanticInvariant target child :=
  h.historicalCertificate.toPhaseSemanticInvariant

theorem TypedHistoricalNormalProvenance.toProvenancedNormalInvariant
    {target : Nat} {parent child : PhaseSearchNode}
    (h : TypedHistoricalNormalProvenance target parent child) :
    ProvenancedNormalInvariant target child := by
  cases h with
  | parent_drop hparent => exact hparent.toProvenancedNormalInvariant
  | coverage_anchor hcoverage =>
      exact hcoverage.toProvenancedNormalInvariant
  | downcross_restart hdowncross =>
      exact hdowncross.toProvenancedNormalInvariant
  | debt_exit hdebt => exact hdebt.toProvenancedNormalInvariant
  | crossing_frontier hcrossing =>
      exact hcrossing.toProvenancedNormalInvariant

/-- Unified extended-history classification.  Horizon readiness remains an
explicit caller obligation and both honest residuals remain possible. -/
theorem TypedHistoricalNormalProvenance.phaseSemanticStep_or_residual
    {target : Nat} {parent child : PhaseSearchNode}
    (h : TypedHistoricalNormalProvenance target parent child)
    (hhorizonReady :
      target ≤ h.historicalCertificate.historyHorizon + 1) :
    (∃ witness, a witness = target) ∨
      (∃ next, PhaseSemanticInvariant target next ∧
        PhaseSearchProgress target next child) ∨
      ExtendedHistoryNormalResidual target child :=
  h.historicalCertificate.phaseSemanticStep_or_residual hhorizonReady

end

end Recaman
