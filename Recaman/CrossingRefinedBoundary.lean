import Recaman.RefinedOracleBoundary

namespace Recaman

/-! # Rank boundary at a crossing-recovery node

A crossing-recovery node deliberately uses the below-target predecessor as
its numeric normal anchor.  Every ordinary current, ready-debt, or
extended-history node has an anchor at least the target.  Consequently such
a non-crossing child cannot decrease the crossing node through the anchor
component: any valid phase-search edge must strictly decrease the outer
history-budget component.  This is a rank obstruction, not merely missing
source provenance.
-/

/-- The non-crossing part of the current refined domain. -/
def RefinedNonCrossingInvariant
    (target : Nat) (node : PhaseSearchNode) : Prop :=
  ReadyCurrentOrDebtInvariant target node ∨
    ExtendedHistoryNormalInvariant target node

/-- Every non-crossing refined node has an anchor at least the target. -/
theorem RefinedNonCrossingInvariant.target_le_anchor
    {target : Nat} {node : PhaseSearchNode}
    (h : RefinedNonCrossingInvariant target node) :
    target ≤ node.anchorParent := by
  rcases h with hready | hextended
  · rcases hready with hcurrent | ⟨value, firstTime, hdebt⟩
    · rcases hcurrent with ⟨time, quotient, remainder, hcertificate⟩
      have hanchor : node.anchorParent = a time := by
        simpa using congrArg PhaseSearchNode.anchorParent
          hcertificate.node_eq
      rw [hanchor]
      exact hcertificate.target_le_value
    · exact Nat.le_trans hdebt.debt.target_le
        (Nat.le_of_lt hdebt.debt.value_lt_anchor)
  · rcases hextended with
      ⟨representativeTime, quotient, remainder, hcertificate⟩
    have hanchor : node.anchorParent = a representativeTime := by
      simpa using congrArg PhaseSearchNode.anchorParent
        hcertificate.node_eq
    rw [hanchor]
    exact hcertificate.target_le_value

/-- A crossing-recovery node's numeric anchor is strictly below the target. -/
theorem CrossingSearchInvariant.anchor_lt_target
    {target : Nat} {node : PhaseSearchNode}
    (h : CrossingSearchInvariant target node) :
    node.anchorParent < target := by
  rcases h with
    ⟨oldAnchor, crossingTime, quotient, remainder, hcertificate⟩
  have hanchor : node.anchorParent = a crossingTime := by
    simpa using congrArg PhaseSearchNode.anchorParent hcertificate.node_eq
  rw [hanchor]
  exact hcertificate.recovery.crossing.1

/-- Any rank edge from a crossing-recovery node to a non-crossing refined
child must strictly lower `missingBelowCount`.  Equal-budget anchor, phase,
or local descent is arithmetically impossible because the parent anchor is
below the target and the child anchor is at least the target. -/
theorem crossing_to_nonCrossing_progress_forces_budgetDrop
    {target : Nat} {parent child : PhaseSearchNode}
    (hparent : CrossingSearchInvariant target parent)
    (hchild : RefinedNonCrossingInvariant target child)
    (hprogress : PhaseSearchProgress target child parent) :
    missingBelowCount target child.horizon <
      missingBelowCount target parent.horizon := by
  have hparentAnchor := hparent.anchor_lt_target
  have hchildAnchor := hchild.target_le_anchor
  unfold PhaseSearchProgress phaseSearchRank at hprogress
  rcases Prod.lex_def.mp hprogress with hbudget | ⟨_, hrest⟩
  · exact hbudget
  · rcases Prod.lex_def.mp hrest with hanchor | ⟨hanchorEq, _⟩
    · have hanchor' : child.anchorParent < parent.anchorParent := by
        simpa using hanchor
      omega
    · have : child.anchorParent = parent.anchorParent := by
        simpa using hanchorEq
      omega

/-- In particular, a crossing node has no same-horizon non-crossing refined
successor.  A future proof must expose a strict history-budget event or stay
inside a more precise crossing descent. -/
theorem crossing_no_sameHorizon_nonCrossing_progress
    {target : Nat} {parent child : PhaseSearchNode}
    (hparent : CrossingSearchInvariant target parent)
    (hchild : RefinedNonCrossingInvariant target child)
    (hhorizon : child.horizon = parent.horizon) :
    ¬ PhaseSearchProgress target child parent := by
  intro hprogress
  have hdrop := crossing_to_nonCrossing_progress_forces_budgetDrop
    hparent hchild hprogress
  rw [hhorizon] at hdrop
  omega

/-- Exhaustive rank shape of any refined child of a crossing node: either it
remains a crossing-recovery state, or the outer history budget strictly
decreases. -/
theorem crossing_refinedChild_budgetDrop_or_crossing
    {target : Nat} {parent child : PhaseSearchNode}
    (hparent : CrossingSearchInvariant target parent)
    (hchild : OrbitReadyRefinedInvariant target child)
    (hprogress : PhaseSearchProgress target child parent) :
    (missingBelowCount target child.horizon <
      missingBelowCount target parent.horizon) ∨
      CrossingSearchInvariant target child := by
  rcases hchild with hready | hextended | hcrossing
  · exact Or.inl (crossing_to_nonCrossing_progress_forces_budgetDrop
      hparent (Or.inl hready) hprogress)
  · exact Or.inl (crossing_to_nonCrossing_progress_forces_budgetDrop
      hparent (Or.inr hextended) hprogress)
  · exact Or.inr hcrossing

/-- At an unchanged history horizon, every refined successor of a crossing
node must itself be crossing. -/
theorem crossing_sameHorizon_refinedChild_is_crossing
    {target : Nat} {parent child : PhaseSearchNode}
    (hparent : CrossingSearchInvariant target parent)
    (hchild : OrbitReadyRefinedInvariant target child)
    (hhorizon : child.horizon = parent.horizon)
    (hprogress : PhaseSearchProgress target child parent) :
    CrossingSearchInvariant target child := by
  rcases crossing_refinedChild_budgetDrop_or_crossing hparent hchild
      hprogress with hdrop | hcrossing
  · rw [hhorizon] at hdrop
    exact False.elim (Nat.lt_irrefl _ hdrop)
  · exact hcrossing

end Recaman
