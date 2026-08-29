import Recaman.RefinedSemanticOutcome
import Recaman.LandingRevisitTransport
import Recaman.ReplayDoubleSubtractDescent

namespace Recaman

noncomputable section

/-! # Adversarial probes against the refined semantic outcome

Every statement below is a *positive* construction: each one exhibits an
inhabitant of something the surrounding development treats as informative,
built from data that is available without the surrounding analysis.  Nothing
here refutes a proved theorem; the point is to measure how much information
the newly refined statements actually carry.

Three independent results.

* `RefinedDomainEdge target` — the forgetful shape into which
  `PermanentTailRefinedSuccessorOutcome.toEdge` collapses all four refined
  semantic branches — follows from `0 < target` alone.  Two genuine orbit
  states with distinct values at or above the target, viewed at a common
  history horizon, are both extended-history refined nodes and the smaller
  one has strictly smaller phase-search rank.  Consequently the summit
  statement `LeastMissingTarget.historyEdge_or_refinedEdge_or_installedEdge`
  is derivable from positivity, exactly like the broad
  `semantic_or_flooredCore` it was built to repair.  Its first disjunct is
  free as well, for an unrelated and even cheaper reason.
* The anchor bump of `exists_phaseSearchProgress_parent` does *not* always
  leave the refined domain.  `anchorBump_not_orbitReadyRefined` needs
  `node.phase = .normal`, and the debt phase is a genuine escape: every
  refined debt node keeps its whole certificate when its anchor is raised.
  A concrete refined debt node is exhibited.
* The regeneration hypothesis of
  `blockedFirstOccurrence_impossible_of_regeneration` is refutable: the real
  orbit contains the blocked first occurrence `BlockedFirstOccurrence 13 6`,
  so that conditional theorem, and the two replay corollaries drawn from it,
  are vacuously true.
-/

/-! ## The forgetful refined edge is free -/

/-- Two extended-history normal nodes at one common horizon, carrying two
genuine orbit values at or above the target, already realise
`RefinedDomainEdge`.  The larger value is produced by asking the initial
region for a state ready for the larger target `a n + 1`. -/
theorem probe_refinedDomainEdge_of_pos
    {target : Nat} (htarget : 0 < target) :
    RefinedDomainEdge target := by
  rcases exists_targetReady_state_of_pos htarget with
    ⟨n, q, r, _f, _hnear, htime, hvalue, hcoord, _hf, _hfirst⟩
  rcases exists_targetReady_state_of_pos (m := a n + 1) (by omega) with
    ⟨n2, q2, r2, _f2, _hnear2, _htime2, hvalue2, hcoord2, _hf2, _hfirst2⟩
  refine ⟨⟨max n n2, a n2, .normal, a n2⟩,
          ⟨max n n2, a n, .normal, a n⟩, ?_, ?_, ?_⟩
  · exact Or.inr (Or.inl ⟨n2, q2, r2, {
      target_positive := htarget
      node_eq := rfl
      representative_le_horizon := Nat.le_max_right _ _
      horizon_time_ready := by
        show target ≤ max n n2 + 1
        have hmax : n ≤ max n n2 := Nat.le_max_left _ _
        omega
      target_le_value := by omega
      coordinates := hcoord2 }⟩)
  · exact Or.inr (Or.inl ⟨n, q, r, {
      target_positive := htarget
      node_eq := rfl
      representative_le_horizon := Nat.le_max_left _ _
      horizon_time_ready := by
        show target ≤ max n n2 + 1
        have hmax : n ≤ max n n2 := Nat.le_max_left _ _
        omega
      target_le_value := hvalue
      coordinates := hcoord }⟩)
  · have hlt : a n < a n2 := by omega
    exact Prod.Lex.right _ (Prod.Lex.left _ _ hlt)

/-! The history disjunct of the same summit statement was conjectured to be
free as well, with `(childTime, parentTime) = (1, 0)`.  That route does not
work.  `TerminalChronologyHistoryProgress` is a conjunction whose second
component `TerminalHistoryCursor target (parentTime + 1)` demands a time
strictly below `parentTime + 1` whose orbit value already exceeds the target,
together with a successor value and a strict-above tail.  At `parentTime = 0`
the only candidate time is zero and `a 0 = 0`, so the cursor is unsatisfiable.
The history disjunct therefore carries real content, unlike the refined edge
above. -/

/-- A least missing target is at least two, since zero and one both occur. -/
theorem probe_two_le_of_leastMissing
    {target : Nat} (h : LeastMissingTarget target) : 2 ≤ target := by
  by_cases hzero : target = 0
  · subst hzero
    exact absurd ⟨0, by decide⟩ h.target_missing
  · by_cases hone : target = 1
    · subst hone
      exact absurd ⟨1, by decide⟩ h.target_missing
    · omega

/-- The whole conclusion of
`LeastMissingTarget.historyEdge_or_refinedEdge_or_installedEdge` follows from
positivity of the target.  Nothing about a permanent tail, a discharge
certificate or a refined outcome is used. -/
theorem probe_summit_disjunction_of_pos
    {target : Nat} (htarget : 0 < target) :
    (∃ childTime parentTime,
      TerminalChronologyHistoryProgress target childTime parentTime) ∨
    RefinedDomainEdge target ∨
    (∃ installedChild installedParent : TailInstalledCycleSearchNode,
      TailInstalledCycleProgress target installedChild installedParent) :=
  Or.inr (Or.inl (probe_refinedDomainEdge_of_pos htarget))

/-- The refined-edge hypothesis of `stuckCrossing_of_refinedEdge` is inert:
the same conclusion comes from the canonical start of the target. -/
theorem probe_stuckCrossing_without_refinedEdge
    {target : Nat} (h : LeastMissingTarget target) :
    ∃ stuck, CrossingSearchInvariant target stuck := by
  rcases exists_targetStartNode h.target_pos with ⟨start, hstart⟩
  rcases orbitReadyRefined_occurs_or_crossing h.target_pos
      (targetStartInvariant_orbitReadyRefined h.target_pos hstart) with
    hoccurs | hstuck
  · exact False.elim (h.target_missing hoccurs)
  · exact hstuck

/-- The landing-transport summit statement is free for the older reason: its
first disjunct is the broad semantic branch already known to be empty. -/
theorem probe_unifiedOutcome_conclusion_of_pos
    {target : Nat} (htarget : 0 < target) :
    (∃ stepParent child : PhaseSearchNode,
      PhaseSemanticInvariant target child ∧
        PhaseSearchProgress target child stepParent) ∨
    (∃ (parent : PhaseSearchNode) (crossingTime : Nat),
      ∃ _core : TailFixedPointCore target parent crossingTime,
        32 ≤ crossingTime ∧ 19 ≤ target) ∨
    (∃ (parent : PhaseSearchNode) (crossingTime predecessorFirstTime : Nat),
      ∃ _core : TailFixedPointCore target parent crossingTime,
        crossingTime < predecessorFirstTime ∧
          target < a predecessorFirstTime ∧ 19 ≤ target) :=
  Or.inl (exists_semanticPhaseProgress htarget)

/-! ## The anchor bump survives in the debt phase -/

/-- Raising the anchor of a refined *debt* node keeps every field of its
certificate, so the node stays in the refined domain.  The obstruction
recorded by `anchorBump_not_orbitReadyRefined` is specific to the normal
phase. -/
theorem probe_debtAnchorBump_stays_orbitReadyRefined
    {target : Nat} {node : PhaseSearchNode} {value firstTime : Nat}
    (h : ReadyDebtInvariant target node value firstTime) :
    OrbitReadyRefinedInvariant target
      ⟨node.horizon, node.anchorParent + 1, node.phase, node.localMeasure⟩ :=
  Or.inl (Or.inr ⟨value, firstTime, {
    debt := {
      phase_eq := h.debt.phase_eq
      local_eq := h.debt.local_eq
      target_le := h.debt.target_le
      first := h.debt.first
      firstTime_lt_horizon := h.debt.firstTime_lt_horizon
      value_lt_anchor := by
        have hlt := h.debt.value_lt_anchor
        show value < node.anchorParent + 1
        omega }
    horizon_ready := h.horizon_ready }⟩)

/-- The bumped node is a genuine strict parent, so the fabrication of
`exists_phaseSearchProgress_parent` runs entirely inside the refined domain
whenever the child is in the debt phase. -/
theorem probe_debtAnchorBump_progress
    {target : Nat} (node : PhaseSearchNode) :
    PhaseSearchProgress target node
      ⟨node.horizon, node.anchorParent + 1, node.phase, node.localMeasure⟩ :=
  Prod.Lex.right _ (Prod.Lex.left _ _ (Nat.lt_succ_self _))

/-- A concrete refined debt node: value three first occurs at time two, the
horizon is three and the anchor is four, for target two. -/
theorem probe_concrete_readyDebt :
    ReadyDebtInvariant 2 ⟨3, 4, .debt, 2⟩ 3 2 := {
  debt := {
    phase_eq := rfl
    local_eq := rfl
    target_le := by decide
    first := by constructor <;> decide
    firstTime_lt_horizon := by decide
    value_lt_anchor := by decide }
  horizon_ready := by decide }

/-- Hence a concrete refined node whose anchor bump is refined as well: both
`⟨3, 4, .debt, 2⟩` and `⟨3, 5, .debt, 2⟩` lie in the refined domain for
target two, and the second is a strict phase-search parent of the first. -/
theorem probe_concrete_debtBump :
    OrbitReadyRefinedInvariant 2 ⟨3, 4, .debt, 2⟩ ∧
      OrbitReadyRefinedInvariant 2 ⟨3, 5, .debt, 2⟩ ∧
        PhaseSearchProgress 2 ⟨3, 4, .debt, 2⟩ ⟨3, 5, .debt, 2⟩ :=
  ⟨Or.inl (Or.inr ⟨3, 2, probe_concrete_readyDebt⟩),
    probe_debtAnchorBump_stays_orbitReadyRefined probe_concrete_readyDebt,
    probe_debtAnchorBump_progress (target := 2) ⟨3, 4, .debt, 2⟩⟩

/-! ## The regeneration hypothesis is refutable -/

/-- The real orbit contains a blocked first occurrence: thirteen first occurs
at time six, and its subtraction defect six is already stored. -/
theorem probe_blockedFirstOccurrence_thirteen :
    BlockedFirstOccurrence 13 6 := by
  refine ⟨?_, by decide, by decide⟩
  constructor
  · decide
  · decide

/-- Therefore the uniform regeneration hypothesis assumed by
`blockedFirstOccurrence_impossible_of_regeneration`,
`minimum_predecessor_canSubtract_of_regeneration` and
`minimum_predecessor_doubleSubtract_of_regeneration` is false, and those three
statements are vacuously true. -/
theorem probe_not_blockedFirstOccurrence_regeneration :
    ¬ (∀ value time earlier, BlockedFirstOccurrence value time →
        FirstAt a (value - (time + 1)) earlier →
        BlockedFirstOccurrence (value - (time + 1)) earlier) := by
  intro hregen
  exact blockedFirstOccurrence_impossible_of_regeneration hregen 13 6
    probe_blockedFirstOccurrence_thirteen

end

end Recaman
