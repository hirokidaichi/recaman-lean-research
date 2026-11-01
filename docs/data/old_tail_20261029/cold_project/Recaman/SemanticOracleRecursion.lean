import Recaman.RefinedOracleBoundary
import Recaman.PermanentAboveCorridorLeastMissingSummit

namespace Recaman

noncomputable section

/-! # Consuming the semantic branch of the summit theorem

`LeastMissingTarget.semantic_or_flooredCore` offers the outer recursion a
semantic phase child or a floored fixed-point core.  Only the fixed-point
side has ever been attacked.  This module audits the other side and connects
it to the well-founded restricted oracle of `PhaseSearchStart`.

Three separate facts come out of that audit.

* As literally stated, the semantic branch is *informationless*: an
  existentially quantified `stepParent` can always be manufactured above any
  node, and a positive target always owns a canonical semantic node.  So the
  whole left disjunct follows from `0 < target` alone.
* The informative content a semantic child would have to carry is membership
  in the refined domain `OrbitReadyRefinedInvariant`.  That promotion is
  available for every semantic constructor as soon as the child's history
  horizon is target-ready, and horizon readiness cannot be dropped.
* Once promoted, the child is a legal *start* of the existing well-founded
  recursion.  Descent from it terminates unconditionally at a crossing node,
  and terminates at the target itself under the already-isolated
  `CrossingRefinedStepHypothesis`.

The last section records the exact price of any consumer: closing the
semantic branch at a target is logically equivalent to that target occurring.
-/

/-! ## The semantic branch as stated carries no information -/

/-- Every phase-search node has a strictly larger parent: raising the anchor
component by one keeps the history budget and lowers nothing else.  Hence an
existentially quantified `stepParent` constrains a child in no way. -/
theorem exists_phaseSearchProgress_parent
    {target : Nat} (child : PhaseSearchNode) :
    ∃ parent : PhaseSearchNode, PhaseSearchProgress target child parent := by
  refine ⟨⟨child.horizon, child.anchorParent + 1, child.phase,
    child.localMeasure⟩, ?_⟩
  exact Prod.Lex.right _ (Prod.Lex.left _ _ (Nat.lt_succ_self _))

/-- A positive target already satisfies the summit's semantic branch: its
canonical start is a semantic node and a step parent exists above it. -/
theorem exists_semanticPhaseProgress
    {target : Nat} (htarget : 0 < target) :
    ∃ stepParent child : PhaseSearchNode,
      PhaseSemanticInvariant target child ∧
        PhaseSearchProgress target child stepParent := by
  rcases exists_phaseSemantic_start htarget with ⟨child, hchild⟩
  rcases exists_phaseSearchProgress_parent (target := target) child with
    ⟨stepParent, hprogress⟩
  exact ⟨stepParent, child, hchild, hprogress⟩

/-- Consequently the summit disjunction is derivable from positivity alone.
This is not a defect of the fixed-point analysis, whose right disjunct is
genuinely informative; it means the left disjunct must be strengthened before
any consumer can exist. -/
theorem semantic_or_flooredCore_of_pos
    {target : Nat} (htarget : 0 < target) :
    (∃ stepParent child : PhaseSearchNode,
      PhaseSemanticInvariant target child ∧
        PhaseSearchProgress target child stepParent) ∨
    (∃ (parent : PhaseSearchNode) (crossingTime : Nat),
      ∃ _core : TailFixedPointCore target parent crossingTime,
        (18 ≤ crossingTime ∨ target = 19) ∧ 19 ≤ target) :=
  Or.inl (exists_semanticPhaseProgress htarget)

/-- A least missing target is positive. -/
theorem LeastMissingTarget.target_pos
    {target : Nat} (h : LeastMissingTarget target) : 0 < target := by
  by_cases hzero : target = 0
  · subst target
    exact False.elim (h.target_missing ⟨0, rfl⟩)
  · omega

/-! ## Promoting a semantic child into the refined recursion domain -/

/-- Refined current and ready-debt nodes always know that their history
horizon has reached the target clock. -/
theorem ReadyCurrentOrDebtInvariant.horizon_ready
    {target : Nat} {node : PhaseSearchNode}
    (h : ReadyCurrentOrDebtInvariant target node) :
    target ≤ node.horizon + 1 := by
  rcases h with ⟨time, quotient, remainder, hcertificate⟩ |
    ⟨value, firstTime, hready⟩
  · have htime := hcertificate.time_ready
    simpa [hcertificate.node_eq] using htime
  · exact hready.horizon_ready

/-- Extended-history normal nodes carry the same clock field by definition. -/
theorem ExtendedHistoryNormalInvariant.horizon_ready
    {target : Nat} {node : PhaseSearchNode}
    (h : ExtendedHistoryNormalInvariant target node) :
    target ≤ node.horizon + 1 := by
  rcases h with ⟨representativeTime, quotient, remainder, hcertificate⟩
  exact hcertificate.horizon_time_ready

/-- Inside the refined domain the crossing constructor is the only one which
may fail target readiness at its own horizon. -/
theorem OrbitReadyRefinedInvariant.horizonReady_or_crossing
    {target : Nat} {node : PhaseSearchNode}
    (h : OrbitReadyRefinedInvariant target node) :
    target ≤ node.horizon + 1 ∨ CrossingSearchInvariant target node := by
  rcases h with hready | hextended | hcrossing
  · exact Or.inl hready.horizon_ready
  · exact Or.inl hextended.horizon_ready
  · exact Or.inr hcrossing

/-- Constructor-complete promotion of a semantic node into the refined
recursion domain.  Canonical starts and crossing recoveries need nothing;
ordinary normal and debt nodes need exactly the horizon clock. -/
theorem PhaseSemanticInvariant.toOrbitReadyRefinedInvariant
    {target : Nat} (htarget : 0 < target) {node : PhaseSearchNode}
    (h : PhaseSemanticInvariant target node)
    (hready : target ≤ node.horizon + 1) :
    OrbitReadyRefinedInvariant target node := by
  cases h with
  | canonical_start hstart =>
      exact Or.inl (Or.inl (hstart.toOrbitReadyNormalInvariant htarget))
  | normal hnormal =>
      rcases hnormal with ⟨value, firstTime, quotient, remainder, hcert⟩
      refine Or.inr (Or.inl ⟨firstTime, quotient, remainder, ?_⟩)
      exact {
        target_positive := hcert.target_positive
        node_eq := by
          rw [hcert.first.1]
          exact hcert.node_eq
        representative_le_horizon := hcert.firstTime_le_horizon
        horizon_time_ready := hready
        target_le_value := by
          rw [hcert.first.1]
          exact hcert.target_le
        coordinates := hcert.coordinates
      }
  | debt value firstTime hdebt =>
      exact Or.inl (Or.inr ⟨value, firstTime, {
        debt := hdebt
        horizon_ready := hready
      }⟩)
  | crossing_recovery hcrossing =>
      exact Or.inr (Or.inr hcrossing)

/-- Horizon readiness genuinely has to be supplied: the broad semantic domain
does not imply it.  The witness is the actual state `a 3 = 6` viewed as an
ordinary normal node for target six. -/
theorem not_forall_phaseSemantic_horizonReady :
    ¬ ∀ node : PhaseSearchNode, PhaseSemanticInvariant 6 node →
      6 ≤ node.horizon + 1 := by
  intro hall
  have hcounter := broadNormalChild_can_lack_horizonReadiness
  exact hcounter.2 (hall _ (.normal hcounter.1))

/-! ## Starting the well-founded recursion at a semantic child -/

/-- Unconditional descent.  From any refined node the well-founded phase
search either reaches the target or terminates at a crossing node.  No
oracle, clock, or tail hypothesis is used. -/
theorem orbitReadyRefined_occurs_or_crossing
    {target : Nat} (htarget : 0 < target) {node : PhaseSearchNode}
    (h : OrbitReadyRefinedInvariant target node) :
    (∃ witness, a witness = target) ∨
      ∃ stuck, CrossingSearchInvariant target stuck := by
  induction node using (phaseSearchProgress_wellFounded target).induction with
  | h parent ih =>
      rcases h.refinedStep_or_crossing htarget with hstep | hcrossing
      · rcases hstep with hoccurs | ⟨child, hchild, hprogress⟩
        · exact Or.inl hoccurs
        · exact ih child hprogress hchild
      · exact Or.inr ⟨parent, hcrossing⟩

/-- The semantic branch, once its child is horizon-ready, is a legal start of
that descent.  This is the missing consumer in its unconditional form. -/
theorem phaseSemanticChild_occurs_or_crossing
    {target : Nat} (htarget : 0 < target)
    {stepParent child : PhaseSearchNode}
    (hsemantic : PhaseSemanticInvariant target child)
    (_hprogress : PhaseSearchProgress target child stepParent)
    (hready : target ≤ child.horizon + 1) :
    (∃ witness, a witness = target) ∨
      ∃ stuck, CrossingSearchInvariant target stuck :=
  orbitReadyRefined_occurs_or_crossing htarget
    (hsemantic.toOrbitReadyRefinedInvariant htarget hready)

/-- Full consumer: with the already-isolated crossing-local step, the
restricted oracle recursion started *at the semantic child itself* produces
the target.  This is the connection the summit's semantic branch was missing.
-/
theorem phaseSemanticChild_reaches_of_crossingRefinedStep
    {target : Nat} (htarget : 0 < target)
    (hcrossing : CrossingRefinedStepHypothesis target)
    {stepParent child : PhaseSearchNode}
    (hsemantic : PhaseSemanticInvariant target child)
    (_hprogress : PhaseSearchProgress target child stepParent)
    (hready : target ≤ child.horizon + 1) :
    ∃ witness, a witness = target :=
  restrictedPhaseSearchOracle_reaches_from
    (refinedPhaseSearchOracle_of_crossing htarget hcrossing)
    (hsemantic.toOrbitReadyRefinedInvariant htarget hready)

/-- The shape the summit's semantic branch has to reach in order to feed the
outer recursion: a refined child strictly below a *given* parent, not below
an existentially quantified one. -/
def RefinedSemanticProgress
    (target : Nat) (parent : PhaseSearchNode) : Prop :=
  ∃ child : PhaseSearchNode,
    OrbitReadyRefinedInvariant target child ∧
      PhaseSearchProgress target child parent

/-- With that shape available at every domain parent, the outer recursion
closes with no further hypothesis. -/
theorem occurs_of_refinedSemanticProgress
    {target : Nat} (htarget : 0 < target)
    (hstep : ∀ parent : PhaseSearchNode,
      OrbitReadyRefinedInvariant target parent →
        (∃ witness, a witness = target) ∨
          RefinedSemanticProgress target parent) :
    ∃ witness, a witness = target :=
  targetStart_reaches_of_restrictedOracle htarget
    (OrbitReadyRefinedInvariant target)
    (fun _ hstart => targetStartInvariant_orbitReadyRefined htarget hstart)
    (fun parent hparent => hstep parent hparent)

/-! ## The horizon-ready refined domain -/

/-- Refined domain membership together with the target clock at the node's
own history horizon. -/
def ReadyRefinedInvariant (target : Nat) (node : PhaseSearchNode) : Prop :=
  OrbitReadyRefinedInvariant target node ∧ target ≤ node.horizon + 1

/-- A horizon-ready semantic child lands in the ready refined domain. -/
theorem PhaseSemanticInvariant.toReadyRefinedInvariant
    {target : Nat} (htarget : 0 < target) {node : PhaseSearchNode}
    (h : PhaseSemanticInvariant target node)
    (hready : target ≤ node.horizon + 1) :
    ReadyRefinedInvariant target node :=
  ⟨h.toOrbitReadyRefinedInvariant htarget hready, hready⟩

/-- Canonical starts are horizon-ready refined nodes. -/
theorem targetStartInvariant_readyRefined
    {target : Nat} (htarget : 0 < target) {node : PhaseSearchNode}
    (h : TargetStartInvariant target node) :
    ReadyRefinedInvariant target node := by
  refine ⟨targetStartInvariant_orbitReadyRefined htarget h, ?_⟩
  exact ReadyCurrentOrDebtInvariant.horizon_ready
    (Or.inl (h.toOrbitReadyNormalInvariant htarget))

/-- Constructor-complete audit on the ready domain: every node either steps
inside the refined domain or is a *ready* crossing node.  Compared with
`OrbitReadyRefinedInvariant.refinedStep_or_crossing`, the residual now carries
the clock field that `ReadyCrossingSearchInvariant` demands. -/
theorem ReadyRefinedInvariant.step_or_readyCrossing
    {target : Nat} (htarget : 0 < target) {node : PhaseSearchNode}
    (h : ReadyRefinedInvariant target node) :
    ((∃ witness, a witness = target) ∨
      ∃ child, OrbitReadyRefinedInvariant target child ∧
        PhaseSearchProgress target child node) ∨
      ReadyCrossingSearchInvariant target node := by
  rcases h.1.refinedStep_or_crossing htarget with hstep | hcrossing
  · exact Or.inl hstep
  · exact Or.inr { crossing := hcrossing, horizon_ready := h.2 }

/-- On the ready domain the crossing-local step is therefore only needed for
ready crossings, which is exactly the hypothesis discharged by
`ReadyCrossingSearchInvariant.refinedStep_of_targetTailReturn`. -/
def ReadyCrossingRefinedStepHypothesis (target : Nat) : Prop :=
  ∀ node, ReadyCrossingSearchInvariant target node →
    (∃ witness, a witness = target) ∨
      ∃ child, OrbitReadyRefinedInvariant target child ∧
        PhaseSearchProgress target child node

/-- A target-tail return discharges the ready-crossing step. -/
theorem readyCrossingRefinedStepHypothesis_of_targetTailReturn
    {target : Nat} (hreturn : TargetTailReturnHypothesis target) :
    ReadyCrossingRefinedStepHypothesis target :=
  fun _ hnode => hnode.refinedStep_of_targetTailReturn hreturn

/-- Descent from a horizon-ready refined node, using only the ready form of
the crossing step.  Children which lose horizon readiness are handed back
verbatim as the single explicit residual. -/
theorem readyRefined_occurs_or_unreadyChild
    {target : Nat} (htarget : 0 < target)
    (hcrossing : ReadyCrossingRefinedStepHypothesis target)
    {node : PhaseSearchNode} (h : ReadyRefinedInvariant target node) :
    (∃ witness, a witness = target) ∨
      ∃ unready, CrossingSearchInvariant target unready ∧
        unready.horizon + 1 < target := by
  induction node using (phaseSearchProgress_wellFounded target).induction with
  | h parent ih =>
      have hstep :
          (∃ witness, a witness = target) ∨
            ∃ child, OrbitReadyRefinedInvariant target child ∧
              PhaseSearchProgress target child parent := by
        rcases h.step_or_readyCrossing htarget with hstep | hready
        · exact hstep
        · exact hcrossing parent hready
      rcases hstep with hoccurs | ⟨child, hchild, hprogress⟩
      · exact Or.inl hoccurs
      · by_cases hchildReady : target ≤ child.horizon + 1
        · exact ih child hprogress ⟨hchild, hchildReady⟩
        · rcases hchild.horizonReady_or_crossing with hready | hcross
          · exact False.elim (hchildReady hready)
          · exact Or.inr ⟨child, hcross, by omega⟩

/-- Global assembly on the ready domain, stated with the two residuals kept
apart.  The canonical start supplies the recursion start, the ready-crossing
hypothesis supplies the only missing local step, and the second disjunct is
the exact unready-crossing leak. -/
theorem occurs_or_unreadyCrossing_of_readyCrossingStep
    {target : Nat} (htarget : 0 < target)
    (hcrossing : ReadyCrossingRefinedStepHypothesis target) :
    (∃ witness, a witness = target) ∨
      ∃ unready, CrossingSearchInvariant target unready ∧
        unready.horizon + 1 < target := by
  rcases exists_targetStartNode htarget with ⟨start, hstart⟩
  exact readyRefined_occurs_or_unreadyChild htarget hcrossing
    (targetStartInvariant_readyRefined htarget hstart)

/-- Same statement started at a horizon-ready semantic child instead of at
the canonical start.  This is the summit-facing form of the consumer. -/
theorem phaseSemanticChild_occurs_or_unreadyCrossing
    {target : Nat} (htarget : 0 < target)
    (hcrossing : ReadyCrossingRefinedStepHypothesis target)
    {stepParent child : PhaseSearchNode}
    (hsemantic : PhaseSemanticInvariant target child)
    (_hprogress : PhaseSearchProgress target child stepParent)
    (hready : target ≤ child.horizon + 1) :
    (∃ witness, a witness = target) ∨
      ∃ unready, CrossingSearchInvariant target unready ∧
        unready.horizon + 1 < target :=
  readyRefined_occurs_or_unreadyChild htarget hcrossing
    (hsemantic.toReadyRefinedInvariant htarget hready)

/-! ## Exact price of any semantic-branch consumer -/

/-- Closing the semantic branch at a target means turning every semantic node
into an occurrence witness. -/
def SemanticBranchClosure (target : Nat) : Prop :=
  ∀ node : PhaseSearchNode, PhaseSemanticInvariant target node →
    ∃ witness, a witness = target

/-- The closure is not a local lemma: at a positive target it is *equivalent*
to the target occurring.  Any consumer of the semantic branch therefore has
to be part of the global contradiction, never a constructor-local step. -/
theorem semanticBranchClosure_iff_occurs
    {target : Nat} (htarget : 0 < target) :
    SemanticBranchClosure target ↔ ∃ witness, a witness = target := by
  constructor
  · intro hclosure
    rcases exists_phaseSemantic_start htarget with ⟨node, hnode⟩
    exact hclosure node hnode
  · intro hoccurs _ _
    exact hoccurs

/-- In particular a least missing target refutes its own semantic closure. -/
theorem LeastMissingTarget.not_semanticBranchClosure
    {target : Nat} (h : LeastMissingTarget target) :
    ¬ SemanticBranchClosure target := by
  intro hclosure
  exact h.target_missing
    ((semanticBranchClosure_iff_occurs h.target_pos).mp hclosure)

/-- The same holds for the crossing-local hypothesis, which is why the
fixed-point analysis cannot be replaced by assuming it. -/
theorem LeastMissingTarget.not_crossingRefinedStepHypothesis
    {target : Nat} (h : LeastMissingTarget target) :
    ¬ CrossingRefinedStepHypothesis target := by
  intro hcrossing
  exact h.target_missing
    (crossingRefinedStepHypothesis_implies_occurs h.target_pos hcrossing)

/-- Under a least missing target the ready-crossing step is likewise
unavailable unless an unready crossing node exists.  This is the precise
statement of what is still open on the semantic side. -/
theorem LeastMissingTarget.unreadyCrossing_of_readyCrossingStep
    {target : Nat} (h : LeastMissingTarget target)
    (hcrossing : ReadyCrossingRefinedStepHypothesis target) :
    ∃ unready, CrossingSearchInvariant target unready ∧
      unready.horizon + 1 < target := by
  rcases occurs_or_unreadyCrossing_of_readyCrossingStep h.target_pos
      hcrossing with hoccurs | hunready
  · exact False.elim (h.target_missing hoccurs)
  · exact hunready

end

end Recaman
