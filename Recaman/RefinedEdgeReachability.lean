import Recaman.RefinedFixedPointCore

namespace Recaman

noncomputable section

/-! # Is the refined semantic edge free for a least missing target?

`RefinedSemanticEdge.target_missing` rules out the cheap attack that broke
the two earlier payloads: the edge already entails that the target never
occurs, so it cannot follow from `0 < target`.  The remaining question is
sharper.  A least missing target unconditionally supplies a permanent-above
tail and a combined certificate, and those are exactly the objects the edge
stores.  Does the edge then come for free?

This module answers that by isolating the single arithmetic fact the edge
still needs, and by showing that the canonical candidate supplied by the
certificate itself misses it by exactly zero.
-/

/-! ## What the edge yields -/

/-- A refined semantic edge knows its target is positive. -/
theorem RefinedSemanticEdge.target_positive
    {target start : Nat} (h : RefinedSemanticEdge target start) :
    0 < target := by
  cases h with
  | discharge_step _dischargeParent discharge _step =>
      exact discharge.combined.tail.target_positive
  | mounted_crossing _mountedParent _minimumTime _predecessorFirstTime
      _crossingTime combined _ready _progress =>
      exact combined.tail.target_positive

/-- Descending from a refined semantic edge inside the restricted oracle
recursion always terminates at a crossing node: the occurrence branch is
excluded by the edge's own missing-target field. -/
theorem RefinedSemanticEdge.exists_stuckCrossing
    {target start : Nat} (h : RefinedSemanticEdge target start) :
    ∃ stuck, CrossingSearchInvariant target stuck := by
  rcases h.toRefinedDomainEdge.occurs_or_crossing h.target_positive with
    hoccurs | hstuck
  · exact False.elim (h.target_missing hoccurs)
  · exact hstuck

/-- The edge also refutes the crossing-local step at its own target, so it
cannot be consumed by assuming that hypothesis. -/
theorem RefinedSemanticEdge.not_crossingRefinedStepHypothesis
    {target start : Nat} (h : RefinedSemanticEdge target start) :
    ¬ CrossingRefinedStepHypothesis target := by
  intro hcrossing
  exact h.target_missing
    (crossingRefinedStepHypothesis_implies_occurs h.target_positive hcrossing)

/-! ## The single missing input -/

/-- The exact extra input a permanent-tail certificate needs in order to hand
over a refined semantic edge through its mounted-crossing constructor: one
first weak upcrossing, finishing strictly inside the parent horizon, whose
predecessor value is strictly below the parent anchor. -/
def HorizonInternalAnchorDrop (target start : Nat) : Prop :=
  ∃ (parent : PhaseSearchNode) (minimumTime predecessorFirstTime : Nat),
    PermanentTailCombinedCertificate target start parent minimumTime
        predecessorFirstTime ∧
      ∃ landingTime crossingTime : Nat,
        FirstWeakUpcrossingStep target landingTime crossingTime ∧
          crossingTime + 1 < parent.horizon ∧
          a crossingTime < parent.anchorParent

/-- That single inequality is sufficient: everything else in the
mounted-crossing constructor is supplied by the certificate. -/
theorem RefinedSemanticEdge.of_horizonInternalAnchorDrop
    {target start : Nat} (h : HorizonInternalAnchorDrop target start) :
    RefinedSemanticEdge target start := by
  rcases h with ⟨parent, minimumTime, predecessorFirstTime, combined,
    landingTime, crossingTime, hnext, hhorizon, hdrop⟩
  have hready := combined.landingReadyCrossing hnext hhorizon
  cases combined.mountedLandingRankOutcome crossingTime with
  | phase_exit hprogress =>
      exact .mounted_crossing parent minimumTime predecessorFirstTime
        crossingTime combined hready hprogress
  | anchor_nondecreasing hanchor =>
      exact False.elim (by omega)

/-- The certificate's own two-way boundary, restated at edge level: a mounted
ready crossing either yields the refined semantic edge outright, or its
predecessor value fails to drop below the parent anchor.  Nothing else can
happen, so the strict inequality is not merely sufficient but is the whole
of what a mounted crossing still has to decide. -/
theorem PermanentTailCombinedCertificate.mountedEdge_or_anchorNondecreasing
    {target start : Nat} {parent : PhaseSearchNode}
    {minimumTime predecessorFirstTime : Nat}
    (combined : PermanentTailCombinedCertificate target start parent
      minimumTime predecessorFirstTime)
    {crossingTime : Nat}
    (ready : ReadyCrossingSearchInvariant target
      (terminalPredecessorCrossingNode parent crossingTime)) :
    RefinedSemanticEdge target start ∨
      parent.anchorParent ≤ a crossingTime := by
  cases combined.mountedLandingRankOutcome crossingTime with
  | phase_exit progress =>
      exact Or.inl (.mounted_crossing parent minimumTime predecessorFirstTime
        crossingTime combined ready progress)
  | anchor_nondecreasing hanchor =>
      exact Or.inr hanchor

/-! ## The canonical candidate misses by exactly zero -/

/-- Every combined certificate owns a first weak upcrossing which finishes
strictly inside its parent horizon: the crossing recorded by the parent node
itself.  Its predecessor value is the parent anchor exactly, so the free
candidate lands on the boundary of `HorizonInternalAnchorDrop` without
crossing it. -/
theorem PermanentTailCombinedCertificate.ownFirstUpcrossing
    {target start : Nat} {parent : PhaseSearchNode}
    {minimumTime predecessorFirstTime : Nat}
    (h : PermanentTailCombinedCertificate target start parent minimumTime
      predecessorFirstTime) :
    ∃ crossingTime : Nat,
      FirstWeakUpcrossingStep target crossingTime crossingTime ∧
        crossingTime + 1 < parent.horizon ∧
        a crossingTime = parent.anchorParent := by
  rcases h.crossing.ready_crossing.crossing with
    ⟨oldAnchor, oldTime, quotient, remainder, hcertificate⟩
  have hanchor : parent.anchorParent = a oldTime := by
    rw [hcertificate.node_eq]
  have hbelow : a oldTime < target := hcertificate.recovery.crossing.1
  have hself : WeakUpcrossingStep target oldTime oldTime := {
    start_le := Nat.le_refl _
    below := hbelow
    endpoint_ge := Nat.le_of_lt hcertificate.recovery.crossing.2.1
    forced_addition := hcertificate.recovery.forced_addition
  }
  rcases exists_firstWeakUpcrossingStep_from_below h.tail.target_positive
      hbelow with ⟨candidate, hfirst⟩
  have hle : candidate ≤ oldTime := hfirst.time_le hself
  have hge : oldTime ≤ candidate := hfirst.crossing.start_le
  have heq : candidate = oldTime := by omega
  subst heq
  exact ⟨candidate, hfirst, hcertificate.recovery.crossing_before_horizon,
    hanchor.symm⟩

/-- Consequently a least missing target owns the whole mounted-crossing
package except the strict inequality, and its canonical instance yields
equality.  This is the precise shape of the remaining gap. -/
theorem LeastMissingTarget.ownFirstUpcrossing_anchor_eq
    {target : Nat} (h : LeastMissingTarget target) :
    ∃ (start : Nat) (parent : PhaseSearchNode)
      (minimumTime predecessorFirstTime : Nat),
      PermanentTailCombinedCertificate target start parent minimumTime
          predecessorFirstTime ∧
        ∃ crossingTime : Nat,
          FirstWeakUpcrossingStep target crossingTime crossingTime ∧
            crossingTime + 1 < parent.horizon ∧
            a crossingTime = parent.anchorParent := by
  rcases h.exists_missingPermanentAboveTail with ⟨start, htail⟩
  rcases htail.exists_combinedCertificate with
    ⟨crossingNode, minimumTime, predecessorFirstTime, hcombined⟩
  rcases hcombined.ownFirstUpcrossing with
    ⟨crossingTime, hfirst, hhorizon, hanchor⟩
  exact ⟨start, crossingNode, minimumTime, predecessorFirstTime, hcombined,
    crossingTime, hfirst, hhorizon, hanchor⟩

/-- The refined summit stays a genuine two-way branch unless the drop is
supplied: assuming the drop for every least missing target makes the floored
fixed-point disjunct unreachable. -/
theorem refinedSummit_left_of_horizonInternalAnchorDrop
    {target : Nat} (h : LeastMissingTarget target)
    (hdrop : ∀ start : Nat, MissingPermanentAboveTail target start →
      HorizonInternalAnchorDrop target start) :
    ∃ start : Nat, MissingPermanentAboveTail target start ∧
      RefinedSemanticEdge target start := by
  rcases h.exists_missingPermanentAboveTail with ⟨start, htail⟩
  exact ⟨start, htail,
    RefinedSemanticEdge.of_horizonInternalAnchorDrop (hdrop start htail)⟩

/-! ## The mounted route cannot be free

An anchor drop is not merely unproved: it cannot be available at every
permanent-tail parent.  Installing a dropped crossing produces a combined
certificate of the same tail whose anchor is the dropped value, so an
always-available drop would give an infinite strictly decreasing sequence of
naturals.
-/

/-- The strongest form of the missing input: a horizon-internal anchor drop
at every permanent-tail parent of the given target. -/
def AlwaysHorizonInternalAnchorDrop (target : Nat) : Prop :=
  ∀ (start : Nat) (parent : PhaseSearchNode)
    (minimumTime predecessorFirstTime : Nat),
    PermanentTailCombinedCertificate target start parent minimumTime
        predecessorFirstTime →
      ∃ landingTime crossingTime : Nat,
        FirstWeakUpcrossingStep target landingTime crossingTime ∧
          crossingTime + 1 < parent.horizon ∧
          a crossingTime < parent.anchorParent

/-- No least missing target can have a drop at every parent: the installed
successor reproduces the whole certificate at the strictly smaller anchor, so
the assumption descends the anchor forever. -/
theorem not_alwaysHorizonInternalAnchorDrop
    {target : Nat} (h : LeastMissingTarget target) :
    ¬ AlwaysHorizonInternalAnchorDrop target := by
  intro hdrop
  rcases h.exists_missingPermanentAboveTail with ⟨start, htail⟩
  rcases htail.exists_combinedCertificate with
    ⟨firstParent, minimumTime, predecessorFirstTime, hfirst⟩
  have main : ∀ anchor : Nat, ∀ parent : PhaseSearchNode,
      PermanentTailCombinedCertificate target start parent minimumTime
          predecessorFirstTime →
        parent.anchorParent = anchor → False := by
    intro anchor
    induction Nat.lt_wfRel.wf.apply anchor with
    | intro anchor _ ih =>
        intro parent hcombined hanchor
        rcases hdrop start parent minimumTime predecessorFirstTime hcombined
          with ⟨landingTime, crossingTime, hnext, hhorizon, hlt⟩
        have hready := hcombined.landingReadyCrossing hnext hhorizon
        exact ih (a crossingTime) (show a crossingTime < anchor by omega)
          (terminalPredecessorCrossingNode parent crossingTime)
          (hcombined.installReadyCrossing hready) rfl
  exact main firstParent.anchorParent firstParent hfirst rfl

/-- Therefore the mounted-crossing route to the refined semantic edge is not
free.  Any proof that a least missing target always owns the edge has to use
the discharge-step constructors, whose certificates are branch outputs of the
terminal analysis rather than data the tail supplies by itself. -/
theorem leastMissingTarget_mountedRoute_not_free
    {target : Nat} (h : LeastMissingTarget target) :
    ¬ ∀ (start : Nat) (parent : PhaseSearchNode)
        (minimumTime predecessorFirstTime : Nat),
        PermanentTailCombinedCertificate target start parent minimumTime
            predecessorFirstTime →
          ∃ landingTime crossingTime : Nat,
            FirstWeakUpcrossingStep target landingTime crossingTime ∧
              crossingTime + 1 < parent.horizon ∧
              a crossingTime < parent.anchorParent :=
  not_alwaysHorizonInternalAnchorDrop h

/-! ## What the left branch of the refined summit is worth

The edge is not a cheap escape hatch.  Both of its constructors store a
permanent-above tail, so anything the right branch has to fight is already
present on the left.
-/

/-- A refined semantic edge carries the whole permanent-above tail which
produced it. -/
theorem RefinedSemanticEdge.missingPermanentAboveTail
    {target start : Nat} (h : RefinedSemanticEdge target start) :
    MissingPermanentAboveTail target start := by
  cases h with
  | discharge_step _dischargeParent discharge _step =>
      exact discharge.combined.tail
  | mounted_crossing _mountedParent _minimumTime _predecessorFirstTime
      _crossingTime combined _ready _progress =>
      exact combined.tail

/-- Consequently the edge refutes the long-term tail-return hypothesis, just
as a least missing target does.  Reaching the left branch therefore does not
avoid the global obstruction; it carries it. -/
theorem RefinedSemanticEdge.not_targetTailReturn
    {target start : Nat} (h : RefinedSemanticEdge target start) :
    ¬ TargetTailReturnHypothesis target := by
  intro hreturn
  have htail := h.missingPermanentAboveTail
  have habove : target ≤ a start :=
    Nat.le_of_lt (htail.strictly_above start (Nat.le_refl _))
  rcases hreturn start habove with hoccurs | ⟨finish, htime, hbelow⟩
  · exact h.target_missing hoccurs
  · have := htail.strictly_above finish htime
    omega

/-- Summit-level reading: on either branch the analysis still owes the same
global content.  The left branch yields a stuck crossing node and refutes
both the crossing-local step and the tail-return hypothesis. -/
theorem RefinedSemanticEdge.stuckCrossing_and_obstructions
    {target start : Nat} (h : RefinedSemanticEdge target start) :
    (∃ stuck, CrossingSearchInvariant target stuck) ∧
      ¬ CrossingRefinedStepHypothesis target ∧
      ¬ TargetTailReturnHypothesis target :=
  ⟨h.exists_stuckCrossing, h.not_crossingRefinedStepHypothesis,
    h.not_targetTailReturn⟩

end

end Recaman
