import Recaman.CrossingDowncrossRefined

namespace Recaman

/-! # A crossing whose stored horizon is already below the target

Starting below the target always supplies a later weak upcrossing.  If that
upcrossing is strict, it gives another ready crossing-recovery node.  The
existing rank accepts it exactly when a new below-target value has consumed
history budget or its predecessor is smaller than the old crossing anchor.
The remaining joint-growth case is recorded without weakening either fact.
-/

/-- Exact obstruction after continuing a ready crossing from a below-target
stored horizon.  The next strict upcrossing exists, but neither component
available to a crossing-to-crossing edge has decreased. -/
inductive CrossingContinuationGrowthResidual
    (target : Nat) (parent : PhaseSearchNode) : Prop where
  | intro (time quotient remainder : Nat) (child : PhaseSearchNode)
      (child_eq : child = ⟨time + 2, a time, .normal, a time⟩)
      (continuation : WeakUpcrossingStep target parent.horizon time)
      (ready_crossing : ReadyCrossingSearchInvariant target child)
      (budget_stable :
        missingBelowCount target child.horizon =
          missingBelowCount target parent.horizon)
      (anchor_nondecreasing : parent.anchorParent ≤ child.anchorParent)
      (no_progress : ¬ PhaseSearchProgress target child parent) :
      CrossingContinuationGrowthResidual target parent

/-- A ready crossing whose stored endpoint is below the target either already
contains the target, advances to a refined crossing child, or exposes the
literal joint-growth obstruction: stable history budget and a nondecreasing
pre-crossing anchor.

This closes the existence part of the below-horizon branch.  No recurrence
or unbounded search assumption is used: the next weak upcrossing comes from
`exists_weakUpcrossingStep_from_below`. -/
theorem ReadyCrossingSearchInvariant.refinedStep_or_continuationGrowth_of_horizonBelow
    {target : Nat} {node : PhaseSearchNode}
    (h : ReadyCrossingSearchInvariant target node)
    (hbelow : a node.horizon < target) :
    (∃ witness, a witness = target) ∨
      (∃ child, OrbitReadyRefinedInvariant target child ∧
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
      refine ⟨child, Or.inr (Or.inr hready.crossing), ?_⟩
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
    refine ⟨child, Or.inr (Or.inr hready.crossing), ?_⟩
    exact Prod.Lex.left _ _ hbudgetDrop

set_option maxRecDepth 10000 in
/-- The growth residual is realized by the actual Recamán orbit.  Target 19
is strictly crossed at time six; at the later ready horizon 31 the orbit is
again below 19, but the immediate continuation raises the crossing anchor
from 13 to 14 without discovering a new value below 19. -/
theorem crossingContinuationGrowth_actual_example :
    let parent : PhaseSearchNode := ⟨31, 13, .normal, 13⟩
    ReadyCrossingSearchInvariant 19 parent ∧
      a parent.horizon < 19 ∧
      CrossingContinuationGrowthResidual 19 parent := by
  let parent : PhaseSearchNode := ⟨31, 13, .normal, 13⟩
  let child : PhaseSearchNode := ⟨33, 14, .normal, 14⟩
  have hparent : ReadyCrossingSearchInvariant 19 parent := {
    crossing := ⟨20, 6, 2, 6, {
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
    }⟩
    horizon_ready := by decide
  }
  have hchild : ReadyCrossingSearchInvariant 19 child := {
    crossing := ⟨46, 31, 1, 14, {
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
    }⟩
    horizon_ready := by decide
  }
  refine ⟨hparent, by decide, ?_⟩
  exact .intro 31 1 14 child rfl
    ⟨by decide, by decide, by decide, by decide⟩
    hchild (by decide) (by decide) (by
      change ¬ PhaseSearchProgress 19
        ⟨33, 14, .normal, 14⟩ ⟨31, 13, .normal, 13⟩
      rw [crossingNumeric_progress_iff_budgetDrop_or_anchorDrop]
      decide)

end Recaman
