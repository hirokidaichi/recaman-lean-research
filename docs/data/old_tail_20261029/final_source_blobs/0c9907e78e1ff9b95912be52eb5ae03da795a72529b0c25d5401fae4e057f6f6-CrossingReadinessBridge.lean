import Recaman.SemanticOracleRecursion
import Recaman.CrossingTailRefined

namespace Recaman

noncomputable section

/-! # Bridging the readiness gap between crossing and ready-crossing nodes

`ReadyRefinedInvariant.step_or_readyCrossing` produces a *ready* crossing
residual, while every refined child is returned through the bare
`OrbitReadyRefinedInvariant`.  The descent therefore leaks whenever some
child is a crossing node whose stored history horizon has fallen back below
the target clock.  This module analyses that leak.

Three separate facts come out of the analysis.

* Unready crossing certificates are not vacuous: an explicit node of the
  actual orbit carries one.  The leak can therefore never be closed by
  proving that no such node exists; it has to be closed by showing that the
  recursion never *reaches* one.
* Reachability is heavily constrained.  A budget-dropping rank edge always
  raises the history horizon, so readiness is inherited automatically.  Only
  budget-stable, horizon-lowering edges can leak, and they must land in the
  crossing constructor.
* Every audited producer of a crossing child in fact keeps the parent's
  horizon, so the leak is empty for them.  The producers are re-proved here
  with the clock field retained.
-/

/-! ## The leak target is inhabited -/

set_option maxRecDepth 10000 in
/-- The actual orbit crosses twelve at time five: `a 5 = 7` is below and
`a 6 = 13` is above, the crossing is a forced addition, and twelve has not
occurred by time five.  Storing this crossing at the smallest legal history
horizon produces a crossing certificate whose clock is far behind the
target. -/
theorem crossingSearchInvariant_twelve_unready :
    CrossingSearchInvariant 12 ⟨7, a 5, .normal, a 5⟩ ∧
      (⟨7, a 5, .normal, a 5⟩ : PhaseSearchNode).horizon + 1 < 12 := by
  refine ⟨⟨13, 5, 2, 1, ?_⟩, by decide⟩
  exact {
    target_positive := by decide
    node_eq := rfl
    recovery := {
      target_missing := by decide
      forced_addition := by decide
      crossing := ⟨by decide, by decide, by decide⟩
      coordinates := ⟨by decide, by decide⟩
      crossing_before_horizon := by decide
      predecessor_lt_anchor := by decide
    }
  }

/-- Consequently the unready-crossing residual of
`occurs_or_unreadyCrossing_of_readyCrossingStep` is satisfiable, and at
target twelve it is outright true. -/
theorem exists_unreadyCrossing_twelve :
    ∃ unready, CrossingSearchInvariant 12 unready ∧
      unready.horizon + 1 < 12 :=
  ⟨_, crossingSearchInvariant_twelve_unready.1,
    crossingSearchInvariant_twelve_unready.2⟩

/-- Hence the residual cannot be discharged by a nonexistence theorem: the
crossing constructor genuinely fails to imply its own horizon clock. -/
theorem not_forall_crossing_horizonReady :
    ¬ ∀ node : PhaseSearchNode, CrossingSearchInvariant 12 node →
      12 ≤ node.horizon + 1 := by
  intro hall
  have hcounter := crossingSearchInvariant_twelve_unready
  have hready := hall _ hcounter.1
  have hunready := hcounter.2
  omega

/-! ## Readiness transfer along a rank edge -/

/-- A strict history-budget drop can only come from a strictly larger
history horizon, because the budget is antitone in time. -/
theorem horizon_lt_of_budgetDrop
    {target childHorizon parentHorizon : Nat}
    (hdrop : missingBelowCount target childHorizon <
      missingBelowCount target parentHorizon) :
    parentHorizon < childHorizon := by
  by_cases hle : childHorizon ≤ parentHorizon
  · have hanti := missingBelowCount_antitone (m := target) hle
    exact False.elim (by omega)
  · omega

/-- Non-crossing refined nodes always carry the target clock. -/
theorem RefinedNonCrossingInvariant.horizon_ready
    {target : Nat} {node : PhaseSearchNode}
    (h : RefinedNonCrossingInvariant target node) :
    target ≤ node.horizon + 1 := by
  rcases h with hready | hextended
  · exact hready.horizon_ready
  · exact hextended.horizon_ready

/-- Structural description of the horizon-ready refined domain: readiness is
free outside the crossing constructor, and inside it is exactly the field
that `ReadyCrossingSearchInvariant` adds. -/
theorem readyRefinedInvariant_iff
    {target : Nat} {node : PhaseSearchNode} :
    ReadyRefinedInvariant target node ↔
      RefinedNonCrossingInvariant target node ∨
        ReadyCrossingSearchInvariant target node := by
  constructor
  · intro h
    rcases h.1 with hready | hextended | hcrossing
    · exact Or.inl (Or.inl hready)
    · exact Or.inl (Or.inr hextended)
    · exact Or.inr ⟨hcrossing, h.2⟩
  · intro h
    rcases h with hnon | hcrossing
    · refine ⟨?_, hnon.horizon_ready⟩
      rcases hnon with hready | hextended
      · exact Or.inl hready
      · exact Or.inr (Or.inl hextended)
    · exact ⟨Or.inr (Or.inr hcrossing.crossing), hcrossing.horizon_ready⟩

/-- Non-crossing refined children are horizon-ready with no side condition. -/
theorem RefinedNonCrossingInvariant.toReadyRefinedInvariant
    {target : Nat} {node : PhaseSearchNode}
    (h : RefinedNonCrossingInvariant target node) :
    ReadyRefinedInvariant target node :=
  readyRefinedInvariant_iff.mpr (Or.inl h)

/-- Ready crossings are horizon-ready refined nodes. -/
theorem ReadyCrossingSearchInvariant.toReadyRefinedInvariant
    {target : Nat} {node : PhaseSearchNode}
    (h : ReadyCrossingSearchInvariant target node) :
    ReadyRefinedInvariant target node :=
  readyRefinedInvariant_iff.mpr (Or.inr h)

/-- Readiness is inherited by any refined child whose stored history horizon
did not fall behind its parent's. -/
theorem readyRefined_of_horizon_le
    {target : Nat} {parent child : PhaseSearchNode}
    (hparent : target ≤ parent.horizon + 1)
    (hchild : OrbitReadyRefinedInvariant target child)
    (hhorizon : parent.horizon ≤ child.horizon) :
    ReadyRefinedInvariant target child :=
  ⟨hchild, by omega⟩

/-- In particular a budget-dropping rank edge always preserves readiness. -/
theorem readyRefined_of_budgetDrop
    {target : Nat} {parent child : PhaseSearchNode}
    (hparent : target ≤ parent.horizon + 1)
    (hchild : OrbitReadyRefinedInvariant target child)
    (hdrop : missingBelowCount target child.horizon <
      missingBelowCount target parent.horizon) :
    ReadyRefinedInvariant target child :=
  readyRefined_of_horizon_le hparent hchild
    (Nat.le_of_lt (horizon_lt_of_budgetDrop hdrop))

/-- Exact shape of a leaking child.  From a horizon-ready parent, a refined
child which loses readiness is necessarily a crossing node reached by a
budget-stable edge which strictly lowers the history horizon and does not
raise the anchor.  Every mechanism which advances the history horizon is
therefore incapable of leaking. -/
theorem unreadyRefinedChild_shape
    {target : Nat} {parent child : PhaseSearchNode}
    (hparent : target ≤ parent.horizon + 1)
    (hchild : OrbitReadyRefinedInvariant target child)
    (hprogress : PhaseSearchProgress target child parent)
    (hunready : child.horizon + 1 < target) :
    CrossingSearchInvariant target child ∧
      child.horizon < parent.horizon ∧
      missingBelowCount target child.horizon =
        missingBelowCount target parent.horizon ∧
      child.anchorParent ≤ parent.anchorParent := by
  have hcrossing : CrossingSearchInvariant target child := by
    rcases hchild.horizonReady_or_crossing with hready | hcross
    · exact False.elim (by omega)
    · exact hcross
  have hhorizon : child.horizon < parent.horizon := by omega
  have hanti := missingBelowCount_antitone (m := target)
    (Nat.le_of_lt hhorizon)
  unfold PhaseSearchProgress phaseSearchRank at hprogress
  rcases Prod.lex_def.mp hprogress with hbudget | ⟨hbudgetEq, hrest⟩
  · have hbudget' : missingBelowCount target child.horizon <
        missingBelowCount target parent.horizon := by simpa using hbudget
    exact False.elim (by omega)
  · have hbudgetEq' : missingBelowCount target child.horizon =
        missingBelowCount target parent.horizon := by simpa using hbudgetEq
    refine ⟨hcrossing, hhorizon, hbudgetEq', ?_⟩
    rcases Prod.lex_def.mp hrest with hanchor | ⟨hanchorEq, _⟩
    · have hanchor' : child.anchorParent < parent.anchorParent := by
        simpa using hanchor
      omega
    · have hanchorEq' : child.anchorParent = parent.anchorParent := by
        simpa using hanchorEq
      omega

/-! ## Ready debt never leaks -/

/-- Typed extended-history exit of a ready debt node.  This is the ready
form of `ReadyDebtInvariant.extendedHistoryExit`: the child constructor is
retained instead of being widened to the refined union, so its clock field
survives. -/
theorem ReadyDebtInvariant.readyExtendedHistoryExit
    {target horizon anchor value firstTime : Nat}
    (htarget : 0 < target)
    (h : ReadyDebtInvariant target
      ⟨horizon, anchor, .debt, firstTime⟩ value firstTime) :
    ∃ child, ExtendedHistoryNormalInvariant target child ∧
      PhaseSearchProgress target child
        ⟨horizon, anchor, .debt, firstTime⟩ := by
  have htimePositive := debt_firstTime_pos htarget h.debt
  rcases exists_coordinatesAt htimePositive with
    ⟨quotient, remainder, hcoordinates⟩
  let child : PhaseSearchNode :=
    ⟨horizon, a firstTime, .normal, a firstTime⟩
  have hextended : ExtendedHistoryNormalInvariant target child :=
    ⟨firstTime, quotient, remainder, {
      target_positive := htarget
      node_eq := rfl
      representative_le_horizon := Nat.le_of_lt h.debt.firstTime_lt_horizon
      horizon_time_ready := by
        simpa [child] using h.horizon_ready
      target_le_value := by
        rw [h.debt.first.1]
        exact h.debt.target_le
      coordinates := hcoordinates
    }⟩
  have hanchorDrop : a firstTime < anchor := by
    rw [h.debt.first.1]
    exact h.debt.value_lt_anchor
  exact ⟨child, hextended, phaseSearch_exitDebt_of_anchorDrop hanchorDrop⟩

/-- Ready form of `ReadyDebtInvariant.obstruction_refinedStep`.  Both
forced-addition obstructions build their crossing child at the parent's own
history horizon, so the parent clock transfers verbatim. -/
theorem ReadyDebtInvariant.obstruction_readyRefinedStep
    {target horizon anchor value firstTime : Nat}
    (htarget : 0 < target)
    (h : ReadyDebtInvariant target
      ⟨horizon, anchor, .debt, firstTime⟩ value firstTime)
    (hobstruction : DebtStepObstruction target horizon anchor value
      firstTime) :
    (∃ witness, a witness = target) ∨
      ∃ child, ReadyRefinedInvariant target child ∧
        PhaseSearchProgress target child
          ⟨horizon, anchor, .debt, firstTime⟩ := by
  cases hobstruction with
  | legal_reaches_anchor n htime hcan hvalue htargetValue hanchor =>
      rcases h.readyExtendedHistoryExit htarget with
        ⟨child, hchild, hprogress⟩
      exact Or.inr ⟨child,
        RefinedNonCrossingInvariant.toReadyRefinedInvariant
          (Or.inr hchild), hprogress⟩
  | addition_nonpositive n htime hforced hvalue htargetValue hbelow
      hnonpositive =>
      subst firstTime
      rcases debtCrossing_enters_recovery h.debt hforced hbelow with
        hoccurs | ⟨quotient, remainder, hrecovery, hprogress⟩
      · exact Or.inl hoccurs
      · let child : PhaseSearchNode :=
          ⟨horizon, a n, .normal, a n⟩
        have hcrossing : ReadyCrossingSearchInvariant target child := {
          crossing := ⟨anchor, n, quotient, remainder, {
            target_positive := htarget
            node_eq := rfl
            recovery := hrecovery
          }⟩
          horizon_ready := by
            simpa [child] using h.horizon_ready
        }
        exact Or.inr ⟨child, hcrossing.toReadyRefinedInvariant, hprogress⟩
  | addition_seen_below_target n candidate candidateTime htime hforced
      hvalue htargetValue hbelow hcandidate hpositive hfirst htimeDrop
      hcandidateBelow halready =>
      subst firstTime
      rcases debtCrossing_enters_recovery h.debt hforced hbelow with
        hoccurs | ⟨quotient, remainder, hrecovery, hprogress⟩
      · exact Or.inl hoccurs
      · let child : PhaseSearchNode :=
          ⟨horizon, a n, .normal, a n⟩
        have hcrossing : ReadyCrossingSearchInvariant target child := {
          crossing := ⟨anchor, n, quotient, remainder, {
            target_positive := htarget
            node_eq := rfl
            recovery := hrecovery
          }⟩
          horizon_ready := by
            simpa [child] using h.horizon_ready
        }
        exact Or.inr ⟨child, hcrossing.toReadyRefinedInvariant, hprogress⟩

/-- Ready debt has a residual-free step *inside the horizon-ready refined
domain*.  No child of a ready debt node can leak. -/
theorem ReadyDebtInvariant.readyRefinedStep
    {target horizon anchor value firstTime : Nat}
    (htarget : 0 < target)
    (h : ReadyDebtInvariant target
      ⟨horizon, anchor, .debt, firstTime⟩ value firstTime) :
    (∃ witness, a witness = target) ∨
      ∃ child, ReadyRefinedInvariant target child ∧
        PhaseSearchProgress target child
          ⟨horizon, anchor, .debt, firstTime⟩ := by
  rcases h.readyCurrentOrDebtStep_or_obstruction htarget with
    hoccurs | ⟨child, hchild, hprogress⟩ | hobstruction
  · exact Or.inl hoccurs
  · exact Or.inr ⟨child,
      RefinedNonCrossingInvariant.toReadyRefinedInvariant
        (Or.inl hchild), hprogress⟩
  · exact h.obstruction_readyRefinedStep htarget hobstruction

/-! ## Extended-history producers of crossing children -/

/-- Ready form of `extendedNormal_crossingRecovery_refinedStep_from_below`.
The constructed crossing child stores `max node.horizon (crossingTime + 2)`,
which never falls below the parent horizon, so the parent's clock is
inherited. -/
theorem extendedNormal_readyCrossingRecovery_refinedStep_from_below
    {target : Nat} {node : PhaseSearchNode}
    {representativeTime startTime : Nat}
    (htarget : 0 < target)
    (hnode : node =
      ⟨node.horizon, a representativeTime, .normal,
        a representativeTime⟩)
    (hhorizonReady : target ≤ node.horizon + 1)
    (htargetValue : target ≤ a representativeTime)
    (hbelow : a startTime < target) :
    (∃ witness, a witness = target) ∨
      ∃ child, ReadyRefinedInvariant target child ∧
        PhaseSearchProgress target child node := by
  rcases exists_weakUpcrossingStep_from_below htarget hbelow with
    ⟨crossingTime, hcrossing⟩
  by_cases hseen : target ∈ valuesThrough crossingTime
  · rcases mem_valuesThrough_iff.mp hseen with ⟨witness, _, hvalue⟩
    exact Or.inl ⟨witness, hvalue⟩
  by_cases hequal : a (crossingTime + 1) = target
  · exact Or.inl ⟨crossingTime + 1, hequal⟩
  have hstrict : target < a (crossingTime + 1) :=
    Nat.lt_of_le_of_ne hcrossing.endpoint_ge (Ne.symm hequal)
  have hforcedValue :=
    a_succ_of_not_canSubtract hcrossing.forced_addition
  have hdebtCrossing : DebtCrossing target
      (a (crossingTime + 1)) crossingTime :=
    ⟨hcrossing.below, hstrict, hforcedValue⟩
  rcases exists_coordinatesAt (n := crossingTime + 1) (by omega) with
    ⟨crossingQuotient, crossingRemainder, hcoordinates⟩
  let historyHorizon := max node.horizon (crossingTime + 2)
  let child : PhaseSearchNode :=
    ⟨historyHorizon, a crossingTime, .normal, a crossingTime⟩
  have hanchorDrop : a crossingTime < a representativeTime :=
    Nat.lt_of_lt_of_le hcrossing.below htargetValue
  have hrecovery : CrossingRecoveryInvariant target historyHorizon
      (a representativeTime) crossingTime crossingQuotient
      crossingRemainder := {
    target_missing := hseen
    forced_addition := hcrossing.forced_addition
    crossing := hdebtCrossing
    coordinates := hcoordinates
    crossing_before_horizon := by
      simp only [historyHorizon]
      exact Nat.lt_of_lt_of_le (by omega)
        (Nat.le_max_right node.horizon (crossingTime + 2))
    predecessor_lt_anchor := hanchorDrop
  }
  have hreadyCrossing : ReadyCrossingSearchInvariant target child := {
    crossing :=
      ⟨a representativeTime, crossingTime, crossingQuotient,
        crossingRemainder, {
          target_positive := htarget
          node_eq := rfl
          recovery := hrecovery
        }⟩
    horizon_ready := by
      have hmono : node.horizon ≤ historyHorizon :=
        Nat.le_max_left node.horizon (crossingTime + 2)
      simpa [child] using Nat.le_trans hhorizonReady (by omega)
  }
  have hprogress : PhaseSearchProgress target child node := by
    rw [hnode]
    exact phaseSearchProgress_of_horizonAndAnchor
      (Nat.le_max_left _ _) hanchorDrop
  exact Or.inr ⟨child, hreadyCrossing.toReadyRefinedInvariant, hprogress⟩

/-- Ready form of the strict history-budget gap exit. -/
theorem ExtendedHistoryNormalCertificate.readyRefinedStep_of_budgetGap
    {target : Nat} {node : PhaseSearchNode}
    {representativeTime quotient remainder : Nat}
    (h : ExtendedHistoryNormalCertificate target node representativeTime
      quotient remainder)
    (hgap : missingBelowCount target node.horizon <
      missingBelowCount target representativeTime) :
    (∃ witness, a witness = target) ∨
      ∃ child, ReadyRefinedInvariant target child ∧
        PhaseSearchProgress target child node := by
  rcases exists_newBelow_occurrence_of_missingBelowCount_strict
      h.representative_le_horizon hgap with
    ⟨value, occurrenceTime, hvalueTarget, _, _, hvalue, _, _⟩
  have hbelow : a occurrenceTime < target := by
    rw [hvalue]
    exact hvalueTarget
  exact extendedNormal_readyCrossingRecovery_refinedStep_from_below
    h.target_positive h.node_eq h.horizon_time_ready h.target_le_value
    hbelow

/-- Early representatives never leak: forward children stay extended
history, blocked candidates enter ready debt, and both residual mechanisms
route through the ready future-upcrossing exit above. -/
theorem EarlyRepresentativeCertificate.readyRefinedStep
    {target : Nat} {node : PhaseSearchNode}
    {representativeTime quotient remainder : Nat}
    (h : EarlyRepresentativeCertificate target node representativeTime
      quotient remainder) :
    (∃ witness, a witness = target) ∨
      ∃ child, ReadyRefinedInvariant target child ∧
        PhaseSearchProgress target child node := by
  cases h.classify with
  | target_occurs witness hvalue =>
      exact Or.inl ⟨witness, hvalue⟩
  | forward_child child hforward =>
      have hextended : ExtendedHistoryNormalInvariant target child :=
        ⟨hforward.representativeTime, hforward.quotient,
          hforward.remainder, hforward.certificate⟩
      exact Or.inr ⟨child,
        RefinedNonCrossingInvariant.toReadyRefinedInvariant
          (Or.inr hextended), hforward.progress⟩
  | debt_child value firstTime child hchild hdebt _ hprogress =>
      have hready : ReadyDebtInvariant target child value firstTime := {
        debt := hdebt
        horizon_ready := by
          rw [hchild]
          exact h.extended.horizon_time_ready
      }
      exact Or.inr ⟨child,
        RefinedNonCrossingInvariant.toReadyRefinedInvariant
          (Or.inl (Or.inr ⟨value, firstTime, hready⟩)), hprogress⟩
  | residual hresidual =>
      cases hresidual with
      | legal_downcross representativeTime quotient remainder certificate
          _legal hbelow _nextDrop _historyGap =>
          exact extendedNormal_readyCrossingRecovery_refinedStep_from_below
            certificate.extended.target_positive
            certificate.extended.node_eq
            certificate.extended.horizon_time_ready
            certificate.extended.target_le_value hbelow
      | forced_below_candidate representativeTime quotient remainder
          candidate certificate _candidateEq _positive hbelow hseen
          _forced _next =>
          rcases mem_valuesThrough_iff.mp hseen with
            ⟨startTime, _, hstartValue⟩
          have hbelowStart : a startTime < target := by
            rw [hstartValue]
            exact hbelow
          exact extendedNormal_readyCrossingRecovery_refinedStep_from_below
            certificate.extended.target_positive
            certificate.extended.node_eq
            certificate.extended.horizon_time_ready
            certificate.extended.target_le_value hbelowStart

/-! ## The one producer whose crossing-freeness is not re-proved here

`OrbitReadyNormalInvariant.refinedStep` of `OrbitReadyDirectRefined` returns
its children through the refined union.  Inspection of that file shows every
branch lands in the current/debt or extended-history constructor, never in
crossing recovery, but the statement does not record it.  The predicate
below names exactly that missing statement, and nothing more. -/
def OrbitReadyNormalNonCrossingStep (target : Nat) : Prop :=
  ∀ parent, OrbitReadyNormalInvariant target parent →
    (∃ witness, a witness = target) ∨
      ∃ child, RefinedNonCrossingInvariant target child ∧
        PhaseSearchProgress target child parent

/-- Extended-history normal nodes are locally total in the horizon-ready
refined domain.  The representative-stable branch is the only one which
consults the orbit-ready producer. -/
theorem ExtendedHistoryNormalCertificate.readyRefinedStep
    {target : Nat} {node : PhaseSearchNode}
    {representativeTime quotient remainder : Nat}
    (hnormal : OrbitReadyNormalNonCrossingStep target)
    (h : ExtendedHistoryNormalCertificate target node representativeTime
      quotient remainder) :
    (∃ witness, a witness = target) ∨
      ∃ child, ReadyRefinedInvariant target child ∧
        PhaseSearchProgress target child node := by
  by_cases hready : target ≤ representativeTime + 1
  · by_cases hstable : missingBelowCount target node.horizon =
        missingBelowCount target representativeTime
    · rcases hnormal _
        ⟨representativeTime, quotient, remainder,
          h.toOrbitReadyAtRepresentative hready⟩ with
        hoccurs | ⟨child, hchild, hprogress⟩
      · exact Or.inl hoccurs
      · exact Or.inr ⟨child, hchild.toReadyRefinedInvariant,
          h.transportProgress_of_budgetStable hstable hprogress⟩
    · have hbudgetLe := missingBelowCount_antitone (m := target)
          h.representative_le_horizon
      have hgap : missingBelowCount target node.horizon <
          missingBelowCount target representativeTime := by omega
      exact h.readyRefinedStep_of_budgetGap hgap
  · have hearly : EarlyRepresentativeCertificate target node
        representativeTime quotient remainder := {
      extended := h
      not_ready := by omega
    }
    exact hearly.readyRefinedStep

/-- Existential packaging. -/
theorem ExtendedHistoryNormalInvariant.readyRefinedStep
    {target : Nat} {node : PhaseSearchNode}
    (hnormal : OrbitReadyNormalNonCrossingStep target)
    (h : ExtendedHistoryNormalInvariant target node) :
    (∃ witness, a witness = target) ∨
      ∃ child, ReadyRefinedInvariant target child ∧
        PhaseSearchProgress target child node := by
  rcases h with ⟨representativeTime, quotient, remainder, hcertificate⟩
  exact hcertificate.readyRefinedStep hnormal

/-- Ready current and ready debt nodes are locally total in the
horizon-ready refined domain. -/
theorem ReadyCurrentOrDebtInvariant.readyRefinedStep
    {target : Nat} (htarget : 0 < target) {node : PhaseSearchNode}
    (hnormal : OrbitReadyNormalNonCrossingStep target)
    (h : ReadyCurrentOrDebtInvariant target node) :
    (∃ witness, a witness = target) ∨
      ∃ child, ReadyRefinedInvariant target child ∧
        PhaseSearchProgress target child node := by
  rcases h with hcurrent | ⟨value, firstTime, hdebt⟩
  · rcases hnormal node hcurrent with hoccurs | ⟨child, hchild, hprogress⟩
    · exact Or.inl hoccurs
    · exact Or.inr ⟨child, hchild.toReadyRefinedInvariant, hprogress⟩
  · rcases node with ⟨horizon, anchor, phase, loc⟩
    have hphase : phase = .debt := hdebt.debt.phase_eq
    have hlocal : loc = firstTime := hdebt.debt.local_eq
    subst phase
    subst loc
    exact hdebt.readyRefinedStep htarget

/-! ## The bridged local step and the closed descent -/

/-- Ready-crossing local step which keeps the clock on its child.  This is
`ReadyCrossingRefinedStepHypothesis` with the readiness field retained; the
audited crossing producers all satisfy the stronger form. -/
def ReadyCrossingReadyStepHypothesis (target : Nat) : Prop :=
  ∀ node, ReadyCrossingSearchInvariant target node →
    (∃ witness, a witness = target) ∨
      ∃ child, ReadyRefinedInvariant target child ∧
        PhaseSearchProgress target child node

/-- Forgetting the child clock recovers the earlier hypothesis. -/
theorem ReadyCrossingReadyStepHypothesis.toReadyCrossingRefinedStep
    {target : Nat} (h : ReadyCrossingReadyStepHypothesis target) :
    ReadyCrossingRefinedStepHypothesis target := by
  intro node hnode
  rcases h node hnode with hoccurs | ⟨child, hchild, hprogress⟩
  · exact Or.inl hoccurs
  · exact Or.inr ⟨child, hchild.1, hprogress⟩

/-- Constructor-complete step *inside* the horizon-ready refined domain.
Compared with `ReadyRefinedInvariant.step_or_readyCrossing`, the child is
returned with its clock, so the descent below has no unready residual. -/
theorem ReadyRefinedInvariant.readyStep
    {target : Nat} (htarget : 0 < target) {node : PhaseSearchNode}
    (hnormal : OrbitReadyNormalNonCrossingStep target)
    (hcrossing : ReadyCrossingReadyStepHypothesis target)
    (h : ReadyRefinedInvariant target node) :
    (∃ witness, a witness = target) ∨
      ∃ child, ReadyRefinedInvariant target child ∧
        PhaseSearchProgress target child node := by
  rcases readyRefinedInvariant_iff.mp h with hnon | hready
  · rcases hnon with hcurrent | hextended
    · exact hcurrent.readyRefinedStep htarget hnormal
    · exact hextended.readyRefinedStep hnormal
  · exact hcrossing node hready

/-- The horizon-ready refined domain is a restricted phase-search oracle. -/
theorem readyRefinedPhaseSearchOracle
    {target : Nat} (htarget : 0 < target)
    (hnormal : OrbitReadyNormalNonCrossingStep target)
    (hcrossing : ReadyCrossingReadyStepHypothesis target) :
    RestrictedPhaseSearchOracle target (ReadyRefinedInvariant target) :=
  fun _ hnode =>
    ReadyRefinedInvariant.readyStep htarget hnormal hcrossing hnode

/-- The bridge.  With the crossing-local step upgraded to a clock-preserving
form, the descent from the canonical start closes outright: the unready
crossing residual of `occurs_or_unreadyCrossing_of_readyCrossingStep` is
gone. -/
theorem occurs_of_readyCrossingReadyStep
    {target : Nat} (htarget : 0 < target)
    (hnormal : OrbitReadyNormalNonCrossingStep target)
    (hcrossing : ReadyCrossingReadyStepHypothesis target) :
    ∃ witness, a witness = target :=
  targetStart_reaches_of_restrictedOracle htarget
    (ReadyRefinedInvariant target)
    (fun _ hstart => targetStartInvariant_readyRefined htarget hstart)
    (readyRefinedPhaseSearchOracle htarget hnormal hcrossing)

/-- Same descent started at a horizon-ready semantic child. -/
theorem phaseSemanticChild_occurs_of_readyCrossingReadyStep
    {target : Nat} (htarget : 0 < target)
    (hnormal : OrbitReadyNormalNonCrossingStep target)
    (hcrossing : ReadyCrossingReadyStepHypothesis target)
    {stepParent child : PhaseSearchNode}
    (hsemantic : PhaseSemanticInvariant target child)
    (_hprogress : PhaseSearchProgress target child stepParent)
    (hready : target ≤ child.horizon + 1) :
    ∃ witness, a witness = target :=
  restrictedPhaseSearchOracle_reaches_from
    (readyRefinedPhaseSearchOracle htarget hnormal hcrossing)
    (hsemantic.toReadyRefinedInvariant htarget hready)


/-! ## Crossing producers keep the clock on their children -/

/-- A future downcross exit raises the history horizon, because it strictly
lowers the history budget.  Its extended-history child is therefore ready
without any extra argument. -/
theorem ReadyCrossingSearchInvariant.readyRefinedStep_of_futureDowncross
    {target : Nat} {node : PhaseSearchNode} {time : Nat}
    (h : ReadyCrossingSearchInvariant target node)
    (hdown : FutureDowncrossStep target node.horizon time) :
    (∃ witness, a witness = target) ∨
      ∃ child, ReadyRefinedInvariant target child ∧
        PhaseSearchProgress target child node := by
  rcases h.refinedStep_of_futureDowncross_withBudgetDrop hdown with
    hoccurs | ⟨child, hchild, hprogress, hdrop⟩
  · exact Or.inl hoccurs
  · exact Or.inr ⟨child,
      readyRefined_of_budgetDrop h.horizon_ready hchild hdrop, hprogress⟩

/-- Ready form of the below-horizon continuation.  The crossing child built
there is already known to be a `ReadyCrossingSearchInvariant`; only the
statement forgot it. -/
theorem ReadyCrossingSearchInvariant.readyRefinedStep_or_continuationGrowth_of_horizonBelow
    {target : Nat} {node : PhaseSearchNode}
    (h : ReadyCrossingSearchInvariant target node)
    (hbelow : a node.horizon < target) :
    (∃ witness, a witness = target) ∨
      (∃ child, ReadyRefinedInvariant target child ∧
        PhaseSearchProgress target child node) ∨
      CrossingContinuationGrowthResidual target node := by
  rcases h.crossing with
    ⟨oldAnchor, oldTime, oldQuotient, oldRemainder, oldCertificate⟩
  rcases exists_weakUpcrossingStep_from_below
      oldCertificate.target_positive hbelow with ⟨time, hcross⟩
  by_cases hseen : target ∈ valuesThrough time
  · rcases mem_valuesThrough_iff.mp hseen with ⟨witness, _, hvalue⟩
    exact Or.inl ⟨witness, hvalue⟩
  by_cases hequal : a (time + 1) = target
  · exact Or.inl ⟨time + 1, hequal⟩
  have hstrict : target < a (time + 1) :=
    Nat.lt_of_le_of_ne hcross.endpoint_ge (Ne.symm hequal)
  have hstep := a_succ_of_not_canSubtract hcross.forced_addition
  have hdebtCrossing : DebtCrossing target (a (time + 1)) time :=
    ⟨hcross.below, hstrict, hstep⟩
  rcases exists_coordinatesAt (n := time + 1) (by omega) with
    ⟨quotient, remainder, hcoordinates⟩
  let child : PhaseSearchNode :=
    ⟨time + 2, a time, .normal, a time⟩
  have hrecovery : CrossingRecoveryInvariant target (time + 2)
      (a (time + 1)) time quotient remainder := {
    target_missing := hseen
    forced_addition := hcross.forced_addition
    crossing := hdebtCrossing
    coordinates := hcoordinates
    crossing_before_horizon := by omega
    predecessor_lt_anchor := Nat.lt_trans hcross.below hstrict
  }
  have hready : ReadyCrossingSearchInvariant target child := {
    crossing := ⟨a (time + 1), time, quotient, remainder, {
      target_positive := oldCertificate.target_positive
      node_eq := rfl
      recovery := hrecovery
    }⟩
    horizon_ready := by
      have hclock : target ≤ time + 1 :=
        Nat.le_trans h.horizon_ready
          (Nat.add_le_add_right hcross.start_le 1)
      simpa [child] using Nat.le_trans hclock (by omega)
  }
  have hhorizon : node.horizon ≤ child.horizon := by
    simpa [child] using Nat.le_trans hcross.start_le (by omega)
  have hbudgetLe := missingBelowCount_antitone (m := target) hhorizon
  rcases Nat.eq_or_lt_of_le hbudgetLe with hbudgetEq | hbudgetDrop
  · by_cases hanchorDrop : child.anchorParent < node.anchorParent
    · right
      left
      refine ⟨child, hready.toReadyRefinedInvariant, ?_⟩
      have hparentAnchor : node.anchorParent = a oldTime := by
        simpa using congrArg PhaseSearchNode.anchorParent
          oldCertificate.node_eq
      have hanchorDrop' : a time < a oldTime := by
        simpa [child, hparentAnchor] using hanchorDrop
      rw [oldCertificate.node_eq]
      simpa [child] using
        (phaseSearchProgress_of_horizonAndAnchor
          (target := target)
          (show node.horizon ≤ time + 2 by
            exact Nat.le_trans hcross.start_le (by omega))
          hanchorDrop')
    · right
      right
      have hanchorNondecreasing :
          node.anchorParent ≤ child.anchorParent :=
        Nat.le_of_not_gt hanchorDrop
      have hnoProgress : ¬ PhaseSearchProgress target child node := by
        intro hprogress
        have hparentAnchor : node.anchorParent = a oldTime := by
          simpa using congrArg PhaseSearchNode.anchorParent
            oldCertificate.node_eq
        have hshape :
            missingBelowCount target child.horizon <
                missingBelowCount target node.horizon ∨
              (missingBelowCount target child.horizon =
                  missingBelowCount target node.horizon ∧
                a time < a oldTime) := by
          rw [oldCertificate.node_eq] at hprogress
          simpa [child] using
            (crossingNumeric_progress_iff_budgetDrop_or_anchorDrop.mp
              hprogress)
        rcases hshape with hdrop | ⟨_, hdrop⟩
        · rw [hbudgetEq] at hdrop
          omega
        · apply hanchorDrop
          simpa [child, hparentAnchor] using hdrop
      exact .intro time quotient remainder child rfl hcross hready
        hbudgetEq hanchorNondecreasing hnoProgress
  · right
    left
    refine ⟨child, hready.toReadyRefinedInvariant, ?_⟩
    exact Prod.Lex.left _ _ hbudgetDrop

/-- Ready form of the tail-downcross closure.  Every branch either drops the
history budget, in which case readiness is inherited, or reuses the ready
continuation child above. -/
theorem ReadyCrossingSearchInvariant.readyRefinedStep_of_tailDowncross
    {target : Nat} {node : PhaseSearchNode}
    (h : ReadyCrossingSearchInvariant target node)
    (htail : ReadyCrossingTailDowncrossHypothesis target) :
    (∃ witness, a witness = target) ∨
      ∃ child, ReadyRefinedInvariant target child ∧
        PhaseSearchProgress target child node := by
  by_cases habove : target ≤ a node.horizon
  · rcases htail node h habove with hoccurs | ⟨time, hdown⟩
    · exact Or.inl hoccurs
    · exact h.readyRefinedStep_of_futureDowncross hdown
  · have hbelow : a node.horizon < target := Nat.lt_of_not_ge habove
    rcases h.readyRefinedStep_or_continuationGrowth_of_horizonBelow hbelow
      with hoccurs | hstep | hresidual
    · exact Or.inl hoccurs
    · exact Or.inr hstep
    · rcases hresidual with
        ⟨time, quotient, remainder, child, rfl, hcontinuation,
          hchild, hbudgetStable, hanchorNondecreasing, hnoProgress⟩
      have hchildAbove : target ≤ a (time + 2) := by
        by_cases haboveChild : target ≤ a (time + 2)
        · exact haboveChild
        · have hchildBelow : a (time + 2) < target :=
            Nat.lt_of_not_ge haboveChild
          have hdown : FutureDowncrossStep target node.horizon (time + 1) := {
            horizon_le_time := Nat.le_trans hcontinuation.start_le (by omega)
            start_at_or_above := hcontinuation.endpoint_ge
            endpoint_below := by simpa [Nat.add_assoc] using hchildBelow
          }
          have hdrop := hdown.strict_budget_drop
          have hstable :
              missingBelowCount target (time + 2) =
                missingBelowCount target node.horizon := by
            simpa using hbudgetStable
          change missingBelowCount target (time + 2) <
            missingBelowCount target node.horizon at hdrop
          rw [hstable] at hdrop
          exact False.elim (Nat.lt_irrefl _ hdrop)
      rcases htail ⟨time + 2, a time, .normal, a time⟩ hchild
          hchildAbove with hoccurs | ⟨downTime, hdown⟩
      · exact Or.inl hoccurs
      · rcases hchild.refinedStep_of_futureDowncross_withBudgetDrop hdown
          with hoccurs | ⟨next, hnext, hnextProgress, hbudgetDrop⟩
        · exact Or.inl hoccurs
        · have hbudgetDropParent :
              missingBelowCount target next.horizon <
                missingBelowCount target node.horizon := by
            rw [← hbudgetStable]
            exact hbudgetDrop
          have hchildReady : target ≤ time + 2 + 1 := by
            simpa using hchild.horizon_ready
          have hhorizonGrew : time + 2 < next.horizon := by
            simpa using horizon_lt_of_budgetDrop hbudgetDrop
          exact Or.inr ⟨next, ⟨hnext, by omega⟩,
            Prod.Lex.left _ _ hbudgetDropParent⟩

/-- Ready form of the target-tail closure of the crossing-local step. -/
theorem ReadyCrossingSearchInvariant.readyRefinedStep_of_targetTailReturn
    {target : Nat} {node : PhaseSearchNode}
    (h : ReadyCrossingSearchInvariant target node)
    (hreturn : TargetTailReturnHypothesis target) :
    (∃ witness, a witness = target) ∨
      ∃ child, ReadyRefinedInvariant target child ∧
        PhaseSearchProgress target child node :=
  h.readyRefinedStep_of_tailDowncross
    (readyCrossingTailDowncross_of_targetTailReturn hreturn)

/-- A target-tail return discharges the clock-preserving crossing step. -/
theorem readyCrossingReadyStepHypothesis_of_targetTailReturn
    {target : Nat} (hreturn : TargetTailReturnHypothesis target) :
    ReadyCrossingReadyStepHypothesis target :=
  fun _ hnode => hnode.readyRefinedStep_of_targetTailReturn hreturn

/-- Consequence of the whole bridge: for a positive target, the orbit tail
statement now really produces an occurrence, with the crossing-readiness
leak closed.  The only remaining input is the audit fact about the
orbit-ready producer. -/
theorem occurs_of_targetTailReturn
    {target : Nat} (htarget : 0 < target)
    (hnormal : OrbitReadyNormalNonCrossingStep target)
    (hreturn : TargetTailReturnHypothesis target) :
    ∃ witness, a witness = target :=
  occurs_of_readyCrossingReadyStep htarget hnormal
    (readyCrossingReadyStepHypothesis_of_targetTailReturn hreturn)

/-! ## Position of the two remaining inputs -/

/-- The audit predicate is a strengthening of the existing orbit-ready
refined step, not an independent assumption: forgetting that the child is
non-crossing recovers `OrbitReadyNormalInvariant.refinedStep` verbatim. -/
theorem OrbitReadyNormalNonCrossingStep.toRefinedStep
    {target : Nat} (h : OrbitReadyNormalNonCrossingStep target) :
    ∀ parent, OrbitReadyNormalInvariant target parent →
      (∃ witness, a witness = target) ∨
        ∃ child, OrbitReadyRefinedInvariant target child ∧
          PhaseSearchProgress target child parent := by
  intro parent hparent
  rcases h parent hparent with hoccurs | ⟨child, hchild, hprogress⟩
  · exact Or.inl hoccurs
  · refine Or.inr ⟨child, ?_, hprogress⟩
    rcases hchild with hready | hextended
    · exact Or.inl hready
    · exact Or.inr (Or.inl hextended)

/-- Price of the bridged pair.  A least missing target refutes the two
inputs jointly, exactly as it refutes the older crossing-local hypothesis.
The bridge therefore relocates the difficulty without hiding it. -/
theorem LeastMissingTarget.not_readyStep_pair
    {target : Nat} (h : LeastMissingTarget target) :
    ¬ (OrbitReadyNormalNonCrossingStep target ∧
      ReadyCrossingReadyStepHypothesis target) := by
  intro hpair
  exact h.target_missing
    (occurs_of_readyCrossingReadyStep h.target_pos hpair.1 hpair.2)

/-- Under the audit predicate alone, the clock-preserving crossing step is
already equivalent to the target occurring.  This is the precise amount by
which the crossing residual has shrunk: from the bare
`CrossingRefinedStepHypothesis` over all crossing nodes down to a step over
*ready* crossing nodes returning *ready* children. -/
theorem readyCrossingReadyStep_iff_occurs
    {target : Nat} (htarget : 0 < target)
    (hnormal : OrbitReadyNormalNonCrossingStep target) :
    ReadyCrossingReadyStepHypothesis target ↔
      ∃ witness, a witness = target := by
  constructor
  · intro hcrossing
    exact occurs_of_readyCrossingReadyStep htarget hnormal hcrossing
  · intro hoccurs _ _
    exact Or.inl hoccurs

end

end Recaman
