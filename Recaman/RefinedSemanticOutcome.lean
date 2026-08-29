import Recaman.SemanticOracleRecursion
import Recaman.PermanentAboveCorridorTerminalSuccessor

namespace Recaman

noncomputable section

/-! # A semantic branch which cannot be manufactured

`PermanentTailTerminalSuccessorOutcome.semantic_progress` stores a broad
`PhaseSemanticInvariant` child together with an existentially quantified step
parent.  Both halves of that payload are free: `exists_phaseSearchProgress_parent`
builds a strictly larger parent above any node by raising its anchor
component, and `exists_phaseSemantic_start` supplies a semantic node for every
positive target.  The branch therefore survives into the summit theorem while
carrying nothing that the outer recursion can consume.

This module keeps every existing type untouched and adds a parallel outcome
whose semantic branches are pinned:

* the child lives in the refined recursion domain
  `OrbitReadyRefinedInvariant`, so it is a legal *start* of the well-founded
  restricted oracle;
* the step parent is not existentially quantified at all.  Each refined
  branch names its parent as a function of the certificate's own clocks —
  the post-valley representative, the blocker predecessor, or the discharge
  parent itself.

All four generating branches of
`PermanentTailDischargeReturnCertificate.terminalSuccessorOutcome` are
recovered.  Three of them already had a refined local step available at the
point where the broad step was called; the immediate valley branch is
re-derived here through the extended-history representative at the parent
horizon, because its own orbit clock is too small for the current-state
route.
-/

/-! ## Why the anchor bump cannot manufacture a refined parent -/

/-- Structural signature of the refined recursion domain: a refined node is
either in the debt phase or stores its anchor and local measure as the same
orbit value.  Every constructor pins the numeric tuple to an actual orbit
state, so the two fields can never drift apart. -/
theorem OrbitReadyRefinedInvariant.debt_or_anchor_eq_local
    {target : Nat} {node : PhaseSearchNode}
    (h : OrbitReadyRefinedInvariant target node) :
    node.phase = .debt ∨ node.anchorParent = node.localMeasure := by
  rcases h with (⟨time, quotient, remainder, hcertificate⟩ |
      ⟨value, firstTime, hready⟩) | hextended | hcrossing
  · right
    rw [hcertificate.node_eq]
  · left
    exact hready.debt.phase_eq
  · rcases hextended with
      ⟨representativeTime, quotient, remainder, hcertificate⟩
    right
    rw [hcertificate.node_eq]
  · rcases hcrossing with ⟨oldAnchor, crossingTime, quotient, remainder,
      hcertificate⟩
    right
    rw [hcertificate.node_eq]

/-- Anchors in the refined domain are pinned to the target: only a crossing
recovery may store an anchor strictly below it.  Every other constructor
records an actual orbit value which is at or above the target. -/
theorem OrbitReadyRefinedInvariant.crossing_of_anchor_lt_target
    {target : Nat} {node : PhaseSearchNode}
    (h : OrbitReadyRefinedInvariant target node)
    (hanchor : node.anchorParent < target) :
    CrossingSearchInvariant target node := by
  rcases h with (⟨time, quotient, remainder, hcertificate⟩ |
      ⟨value, firstTime, hready⟩) | hextended | hcrossing
  · have hvalue : node.anchorParent = a time := by
      rw [hcertificate.node_eq]
    have habove := hcertificate.target_le_value
    omega
  · have habove := hready.debt.target_le
    have hdrop := hready.debt.value_lt_anchor
    omega
  · rcases hextended with
      ⟨representativeTime, quotient, remainder, hcertificate⟩
    have hvalue : node.anchorParent = a representativeTime := by
      rw [hcertificate.node_eq]
    have habove := hcertificate.target_le_value
    omega
  · exact hcrossing

/-- The fabrication used by `exists_phaseSearchProgress_parent` raises the
anchor of a normal node by one while leaving the local measure alone.  The
result therefore breaks `debt_or_anchor_eq_local` and is never a refined
node.  This is the precise field at which the manufactured step parent
fails. -/
theorem anchorBump_not_orbitReadyRefined
    {target : Nat} {node : PhaseSearchNode}
    (hnormal : node.phase = .normal)
    (hanchor : node.anchorParent = node.localMeasure) :
    ¬ OrbitReadyRefinedInvariant target
      ⟨node.horizon, node.anchorParent + 1, node.phase, node.localMeasure⟩ := by
  intro h
  rcases h.debt_or_anchor_eq_local with hdebt | heq
  · have hdebt' : node.phase = SearchPhase.debt := hdebt
    rw [hnormal] at hdebt'
    exact absurd hdebt' (by decide)
  · have heq' : node.anchorParent + 1 = node.localMeasure := heq
    omega

/-- Applied to a refined normal node, the anchor bump always leaves the
domain.  Hence the manufactured step parent of the broad semantic branch is
rejected by the refined branch below. -/
theorem refinedNormal_anchorBump_not_orbitReadyRefined
    {target : Nat} {node : PhaseSearchNode}
    (h : OrbitReadyRefinedInvariant target node)
    (hnormal : node.phase = .normal) :
    ¬ OrbitReadyRefinedInvariant target
      ⟨node.horizon, node.anchorParent + 1, node.phase, node.localMeasure⟩ := by
  refine anchorBump_not_orbitReadyRefined hnormal ?_
  rcases h.debt_or_anchor_eq_local with hdebt | heq
  · rw [hnormal] at hdebt
    exact absurd hdebt (by decide)
  · exact heq

/-- Nothing precedes the all-zero tuple in the four-component lexicographic
order. -/
theorem not_natQuadLex_allZero
    {p : Nat × (Nat × (Nat × Nat))} :
    ¬ Prod.Lex Nat.lt (Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt)) p
        (0, (0, (0, 0))) := by
  intro h
  cases h with
  | left _ _ hlt => exact absurd hlt (Nat.not_lt_zero _)
  | right _ hrest =>
      cases hrest with
      | left _ _ hlt => exact absurd hlt (Nat.not_lt_zero _)
      | right _ hinner =>
          cases hinner with
          | left _ _ hlt => exact absurd hlt (Nat.not_lt_zero _)
          | right _ hlt => exact absurd hlt (Nat.not_lt_zero _)

/-- A second, independent obstruction to manufacturing: once the below-target
history budget is exhausted, the debt node with anchor and local measure zero
has the least possible phase-search rank, so nothing at all steps into it.
A branch whose parent is fixed by the analysis can therefore not be closed by
producing some child for every parent. -/
theorem no_phaseSearchProgress_into_zeroRank
    {target horizon : Nat}
    (hbudget : missingBelowCount target horizon = 0)
    (child : PhaseSearchNode) :
    ¬ PhaseSearchProgress target child ⟨horizon, 0, .debt, 0⟩ := by
  intro hprogress
  have hrank : phaseSearchRank target
      (⟨horizon, 0, .debt, 0⟩ : PhaseSearchNode) = (0, (0, (0, 0))) := by
    simp [phaseSearchRank, SearchPhase.rank, hbudget]
  have hlex : Prod.Lex Nat.lt (Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt))
      (phaseSearchRank target child) (0, (0, (0, 0))) := by
    rw [← hrank]
    exact hprogress
  exact not_natQuadLex_allZero hlex

/-- Consequently the naive strengthening "every parent owns a child" is
false, whatever the target. -/
theorem not_forall_exists_phaseSearchProgress_child
    {target horizon : Nat}
    (hbudget : missingBelowCount target horizon = 0) :
    ¬ ∀ parent : PhaseSearchNode,
        ∃ child, PhaseSearchProgress target child parent := by
  intro hall
  rcases hall ⟨horizon, 0, .debt, 0⟩ with ⟨child, hprogress⟩
  exact no_phaseSearchProgress_into_zeroRank hbudget child hprogress

/-! ## The refined representative of an immediate terminal valley -/

/-- The discharge parent itself is a refined node: its permanent-tail
crossing certificate is exactly a ready crossing recovery. -/
theorem PermanentTailDischargeReturnCertificate.parent_orbitReadyRefined
    {target start : Nat} {parent : PhaseSearchNode}
    (source : PermanentTailDischargeReturnCertificate target start parent) :
    OrbitReadyRefinedInvariant target parent :=
  Or.inr (Or.inr source.combined.crossing.ready_crossing.crossing)

/-- The discharge parent stores the old crossing predecessor, which is
strictly below the missing target. -/
theorem PermanentTailDischargeReturnCertificate.parent_anchor_lt_target
    {target start : Nat} {parent : PhaseSearchNode}
    (source : PermanentTailDischargeReturnCertificate target start parent) :
    parent.anchorParent < target := by
  rcases source.combined.crossing.ready_crossing.crossing with
    ⟨oldAnchor, oldTime, quotient, remainder, hcertificate⟩
  have hanchor : parent.anchorParent = a oldTime := by
    rw [hcertificate.node_eq]
  have hbelow := hcertificate.recovery.crossing.1
  omega

/-- Sharpest form of the anti-fabrication statement for the crossing branch.
Its child shares the parent horizon, so the strict edge must come from an
anchor drop below `parent.anchorParent`, which is already below the target.
By `crossing_of_anchor_lt_target` the child can then only be an actual
crossing recovery: a genuine strict upcrossing of the real orbit, never a
syntactic adjustment of the parent tuple. -/
theorem crossingChild_anchorDrop_forces_crossingRecovery
    {target : Nat} {parent : PhaseSearchNode} {crossingTime : Nat}
    (hparent : parent.anchorParent < target)
    (hdrop : a crossingTime < parent.anchorParent)
    (hrefined : OrbitReadyRefinedInvariant target
      (terminalPredecessorCrossingNode parent crossingTime)) :
    CrossingSearchInvariant target
      (terminalPredecessorCrossingNode parent crossingTime) := by
  refine hrefined.crossing_of_anchor_lt_target ?_
  simp only [terminalPredecessorCrossingNode]
  omega

/-- The immediate valley closes two steps after its downcross with
`a (downTime + 2) = a downTime + 1`, which is strictly above the target.
Its own orbit clock need not have reached the target, so the current-state
route is unavailable; storing the same value at the parent's zero-budget
horizon gives a horizon-ready extended-history representative instead. -/
theorem PermanentTailDischargeReturnCertificate.immediateValley_extended
    {target start : Nat} {parent : PhaseSearchNode}
    (source : PermanentTailDischargeReturnCertificate target start parent)
    (valley : ImmediateHistoricalValleyCertificate target source.downTime
      source.returnTime)
    (quotient remainder : Nat)
    (hcoordinates : CoordinatesAt (source.downTime + 2) quotient remainder) :
    ExtendedHistoryNormalCertificate target
      (terminalHistoricalPredecessorNode parent (source.downTime + 2))
      (source.downTime + 2) quotient remainder := {
  target_positive := source.combined.tail.target_positive
  node_eq := rfl
  representative_le_horizon := by
    have hreturn := valley.return_eq
    have hhorizon := source.return_before_parentHorizon
    simp only [terminalHistoricalPredecessorNode]
    omega
  horizon_time_ready := by
    simpa [terminalHistoricalPredecessorNode] using
      source.combined.crossing.ready_crossing.horizon_ready
  target_le_value := by
    have hsource := valley.source_above
    have hvalley := valley.valley_equation
    omega
  coordinates := hcoordinates
}

/-! ## The refined successor outcome -/

/-- Refinement of `PermanentTailTerminalSuccessorOutcome`.

The single broad `semantic_progress` constructor is replaced by four pinned
constructors.  In each of them the step parent is a named node built from the
certificate's own data, and the child is proved to lie in the refined
recursion domain.  The remaining constructors are unchanged. -/
inductive PermanentTailRefinedSuccessorOutcome
    {target start : Nat} {parent : PhaseSearchNode}
    (source : PermanentTailDischargeReturnCertificate target start parent) :
    Prop
  | target_occurs
      (witness : Nat) (value_eq : a witness = target) :
      PermanentTailRefinedSuccessorOutcome source
  | history_progress
      (childTime parentTime : Nat)
      (progress : TerminalChronologyHistoryProgress target childTime
        parentTime) :
      PermanentTailRefinedSuccessorOutcome source
  | immediate_refined
      (valley : ImmediateHistoricalValleyCertificate target source.downTime
        source.returnTime)
      (representative : ExtendedHistoryNormalInvariant target
        (terminalHistoricalPredecessorNode parent (source.downTime + 2)))
      (child : PhaseSearchNode)
      (refined : OrbitReadyRefinedInvariant target child)
      (progress : PhaseSearchProgress target child
        (terminalHistoricalPredecessorNode parent (source.downTime + 2))) :
      PermanentTailRefinedSuccessorOutcome source
  | early_refined
      (freshEndpoint candidate firstTime : Nat)
      (historical : TerminalOuterHistoricalBlockerCertificate source
        freshEndpoint candidate firstTime)
      (representative : ExtendedHistoryNormalInvariant target
        (terminalHistoricalPredecessorNode parent (firstTime - 1)))
      (child : PhaseSearchNode)
      (refined : OrbitReadyRefinedInvariant target child)
      (progress : PhaseSearchProgress target child
        (terminalHistoricalPredecessorNode parent (firstTime - 1))) :
      PermanentTailRefinedSuccessorOutcome source
  | ready_refined
      (freshEndpoint candidate firstTime : Nat)
      (historical : TerminalOuterHistoricalBlockerCertificate source
        freshEndpoint candidate firstTime)
      (representative : OrbitReadyNormalInvariant target
        (terminalCurrentPredecessorNode (firstTime - 1)))
      (child : PhaseSearchNode)
      (refined : OrbitReadyRefinedInvariant target child)
      (progress : PhaseSearchProgress target child
        (terminalCurrentPredecessorNode (firstTime - 1))) :
      PermanentTailRefinedSuccessorOutcome source
  | crossing_refined
      (crossingTime : Nat)
      (refined : OrbitReadyRefinedInvariant target
        (terminalPredecessorCrossingNode parent crossingTime))
      (progress : PhaseSearchProgress target
        (terminalPredecessorCrossingNode parent crossingTime) parent) :
      PermanentTailRefinedSuccessorOutcome source
  | installed_successor
      (freshEndpoint candidate firstTime predecessor predecessorFirstTime
        crossingTime quotient remainder : Nat)
      (historical : TerminalOuterHistoricalBlockerCertificate source
        freshEndpoint candidate firstTime)
      (below : BelowTargetHistoricalPredecessorCertificate
        (predecessor := predecessor)
        (predecessorFirstTime := predecessorFirstTime) historical)
      (crossing : TerminalBelowPredecessorCrossingCertificate below
        crossingTime quotient remainder)
      (install : TerminalSelectedCrossingInstallCertificate crossing)
      (next : Nonempty (TerminalSelectedCrossingDischargeCertificate install))
      (progress : TailInstalledCycleProgress target
        ⟨parent.horizon, a crossingTime, crossingTime, firstTime - 1,
          .crossing, firstTime - 1, 0⟩
        ⟨parent.horizon, parent.anchorParent, source.oldCrossingTime,
          firstTime, .discharge, firstTime, 0⟩) :
      PermanentTailRefinedSuccessorOutcome source

/-- Every discharge certificate has the refined successor outcome.  No
generating branch is lost: the three historical branches reuse the refined
local steps which were already available where the broad step was taken, and
the immediate valley branch is closed through its extended-history
representative. -/
theorem PermanentTailDischargeReturnCertificate.refinedSuccessorOutcome
    {target start : Nat} {parent : PhaseSearchNode}
    (source : PermanentTailDischargeReturnCertificate target start parent) :
    PermanentTailRefinedSuccessorOutcome source := by
  cases source.terminalFiniteClosedOutcome with
  | history_progress childTime parentTime progress =>
      exact .history_progress childTime parentTime progress
  | immediate_semantic valley _insufficient _outcome =>
      rcases exists_coordinatesAt (n := source.downTime + 2) (by omega) with
        ⟨quotient, remainder, hcoordinates⟩
      have hextended := source.immediateValley_extended valley quotient
        remainder hcoordinates
      rcases hextended.refinedStep with ⟨witness, hvalue⟩ |
        ⟨child, hchild, hprogress⟩
      · exact .target_occurs witness hvalue
      · exact .immediate_refined valley
          ⟨source.downTime + 2, quotient, remainder, hextended⟩
          child hchild hprogress
  | historical_complete freshEndpoint candidate firstTime historical
      outcome =>
      cases outcome with
      | target_occurs witness value_eq =>
          exact .target_occurs witness value_eq
      | early_step _predecessor _predecessorFirstTime quotient remainder
          _predecessorCertificate early _child _semantic _progress
          _backtrack =>
          rcases early.refinedStep with ⟨witness, hvalue⟩ |
            ⟨child, hchild, hprogress⟩
          · exact .target_occurs witness hvalue
          · exact .early_refined freshEndpoint candidate firstTime historical
              ⟨firstTime - 1, quotient, remainder, early.extended⟩
              child hchild hprogress
      | ready_step _predecessor _predecessorFirstTime quotient remainder
          _predecessorCertificate ready _child _semantic _progress
          _backtrack =>
          rcases ready.refinedStep with ⟨witness, hvalue⟩ |
            ⟨child, hchild, hprogress⟩
          · exact .target_occurs witness hvalue
          · exact .ready_refined freshEndpoint candidate firstTime historical
              ⟨firstTime - 1, quotient, remainder, ready⟩
              child hchild hprogress
      | below_master predecessor predecessorFirstTime below master =>
          cases master with
          | phase_exit crossingTime quotient remainder certificate
              progress =>
              exact .crossing_refined crossingTime certificate.refined
                progress
          | master_progress crossingTime quotient remainder certificate
              progress =>
              let install := certificate.install
              exact .installed_successor freshEndpoint candidate firstTime
                predecessor predecessorFirstTime crossingTime quotient
                remainder historical below certificate install
                install.exists_nextDischarge progress

/-! ## Forgetting the pinned parent -/

/-- Uniform shape of the four refined branches: a strict phase-search edge
whose *both* endpoints lie in the refined recursion domain. -/
def RefinedDomainEdge (target : Nat) : Prop :=
  ∃ stepParent child : PhaseSearchNode,
    OrbitReadyRefinedInvariant target stepParent ∧
      OrbitReadyRefinedInvariant target child ∧
        PhaseSearchProgress target child stepParent

/-- Any refined edge is immediately a legal start of the well-founded
restricted oracle recursion, so descent from it terminates at the target or
at a crossing node. -/
theorem RefinedDomainEdge.occurs_or_crossing
    {target : Nat} (htarget : 0 < target)
    (h : RefinedDomainEdge target) :
    (∃ witness, a witness = target) ∨
      ∃ stuck, CrossingSearchInvariant target stuck := by
  rcases h with ⟨_, child, _, hchild, _⟩
  exact orbitReadyRefined_occurs_or_crossing htarget hchild

/-- With the already isolated crossing-local step the same edge reaches the
target. -/
theorem RefinedDomainEdge.reaches_of_crossingRefinedStep
    {target : Nat} (htarget : 0 < target)
    (hcrossing : CrossingRefinedStepHypothesis target)
    (h : RefinedDomainEdge target) :
    ∃ witness, a witness = target := by
  rcases h with ⟨_, child, _, hchild, _⟩
  exact restrictedPhaseSearchOracle_reaches_from
    (refinedPhaseSearchOracle_of_crossing htarget hcrossing) hchild

/-- Collapsing the refined outcome.  Only the pinned parents differ between
the four semantic branches, and each of them is itself refined. -/
theorem PermanentTailRefinedSuccessorOutcome.toEdge
    {target start : Nat} {parent : PhaseSearchNode}
    {source : PermanentTailDischargeReturnCertificate target start parent}
    (h : PermanentTailRefinedSuccessorOutcome source) :
    (∃ witness, a witness = target) ∨
      (∃ childTime parentTime,
        TerminalChronologyHistoryProgress target childTime parentTime) ∨
      RefinedDomainEdge target ∨
      (∃ installedChild installedParent : TailInstalledCycleSearchNode,
        TailInstalledCycleProgress target installedChild installedParent) := by
  cases h with
  | target_occurs witness value_eq =>
      exact Or.inl ⟨witness, value_eq⟩
  | history_progress childTime parentTime progress =>
      exact Or.inr (Or.inl ⟨childTime, parentTime, progress⟩)
  | immediate_refined _valley representative child refined progress =>
      exact Or.inr (Or.inr (Or.inl
        ⟨_, child, Or.inr (Or.inl representative), refined, progress⟩))
  | early_refined _freshEndpoint _candidate _firstTime _historical
      representative child refined progress =>
      exact Or.inr (Or.inr (Or.inl
        ⟨_, child, Or.inr (Or.inl representative), refined, progress⟩))
  | ready_refined _freshEndpoint _candidate _firstTime _historical
      representative child refined progress =>
      exact Or.inr (Or.inr (Or.inl
        ⟨_, child, Or.inl (Or.inl representative), refined, progress⟩))
  | crossing_refined _crossingTime refined progress =>
      exact Or.inr (Or.inr (Or.inl
        ⟨parent, _, source.parent_orbitReadyRefined, refined, progress⟩))
  | installed_successor _freshEndpoint _candidate _firstTime _predecessor
      _predecessorFirstTime _crossingTime _quotient _remainder _historical
      _below _crossing _install _next progress =>
      exact Or.inr (Or.inr (Or.inr ⟨_, _, progress⟩))

/-! ## Refined summit at the discharge level -/

/-- Every least missing target produces a discharge certificate carrying the
refined outcome.  This is the summit statement the analysis actually
supports without rebuilding the mounted-iteration chain. -/
theorem LeastMissingTarget.exists_refinedSuccessorOutcome
    {target : Nat} (h : LeastMissingTarget target) :
    ∃ (start : Nat) (parent : PhaseSearchNode)
      (source : PermanentTailDischargeReturnCertificate target start parent),
      PermanentTailRefinedSuccessorOutcome source := by
  rcases h.exists_missingPermanentAboveTail with ⟨start, htail⟩
  rcases htail.exists_combinedCertificate with
    ⟨crossingNode, minimumTime, predecessorFirstTime, hcombined⟩
  rcases hcombined.exists_dischargeReturnCertificate with ⟨source⟩
  exact ⟨start, crossingNode, source, source.refinedSuccessorOutcome⟩

/-- Refined summit.  A least missing target hands the outer recursion a
history edge, a refined phase edge with both endpoints in the recursion
domain, or an installed-cycle edge.  The anchor-bump fabrication does not
satisfy the refined disjunct, but a different construction does: see
`probe_refinedDomainEdge_of_pos`, which derives the refined edge from
positivity of the target alone.  This statement therefore carries no more
information than `0 < target`, and downstream consumers must use the
certificate-carrying `RefinedSemanticEdge` instead. -/
theorem LeastMissingTarget.historyEdge_or_refinedEdge_or_installedEdge
    {target : Nat} (h : LeastMissingTarget target) :
    (∃ childTime parentTime,
      TerminalChronologyHistoryProgress target childTime parentTime) ∨
    RefinedDomainEdge target ∨
    (∃ installedChild installedParent : TailInstalledCycleSearchNode,
      TailInstalledCycleProgress target installedChild installedParent) := by
  rcases h.exists_refinedSuccessorOutcome with
    ⟨_start, _parent, source, houtcome⟩
  rcases houtcome.toEdge with hoccurs | hhistory | hrefined | hinstalled
  · exact False.elim (h.target_missing hoccurs)
  · exact Or.inl hhistory
  · exact Or.inr (Or.inl hrefined)
  · exact Or.inr (Or.inr hinstalled)

/-- The refined edge of the summit feeds the well-founded recursion at
once. -/
theorem LeastMissingTarget.stuckCrossing_of_refinedEdge
    {target : Nat} (h : LeastMissingTarget target)
    (hedge : RefinedDomainEdge target) :
    ∃ stuck, CrossingSearchInvariant target stuck := by
  rcases hedge.occurs_or_crossing h.target_pos with hoccurs | hstuck
  · exact False.elim (h.target_missing hoccurs)
  · exact hstuck

end

end Recaman
