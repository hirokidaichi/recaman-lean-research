import Recaman.NormalPhase
import Recaman.PhaseSemantic
import Recaman.PhaseProgress

namespace Recaman

private theorem natQuadLex_fst_le
    {x y : Nat × (Nat × (Nat × Nat))}
    (h : Prod.Lex Nat.lt (Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt)) x y) :
    x.1 ≤ y.1 := by
  rcases x with ⟨xa, xb⟩
  rcases y with ⟨ya, yb⟩
  cases h with
  | left _ _ hlt => exact Nat.le_of_lt hlt
  | right _ _ => exact Nat.le_refl _

private theorem natQuadLex_tail_of_fst_eq
    {x y : Nat × (Nat × (Nat × Nat))}
    (h : Prod.Lex Nat.lt (Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt)) x y)
    (heq : x.1 = y.1) :
    Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt) x.2 y.2 := by
  rcases x with ⟨xa, xb⟩
  rcases y with ⟨ya, yb⟩
  change xa = ya at heq
  subst ya
  cases h with
  | left _ _ hlt => exact False.elim (Nat.lt_irrefl _ hlt)
  | right _ htail => exact htail

private theorem natTripleLex_tail_of_fst_eq
    {x y : Nat × (Nat × Nat)}
    (h : Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt) x y)
    (heq : x.1 = y.1) : Prod.Lex Nat.lt Nat.lt x.2 y.2 := by
  rcases x with ⟨xa, xb⟩
  rcases y with ⟨ya, yb⟩
  change xa = ya at heq
  subst ya
  cases h with
  | left _ _ hlt => exact False.elim (Nat.lt_irrefl _ hlt)
  | right _ htail => exact htail

private theorem natPairLex_tail_of_fst_eq
    {x y : Nat × Nat}
    (h : Prod.Lex Nat.lt Nat.lt x y)
    (heq : x.1 = y.1) : x.2 < y.2 := by
  rcases x with ⟨xa, xb⟩
  rcases y with ⟨ya, yb⟩
  change xa = ya at heq
  subst ya
  cases h with
  | left _ _ hlt => exact False.elim (Nat.lt_irrefl _ hlt)
  | right _ htail => exact htail

/-- Raising the history horizon and strictly lowering the anchor gives phase
progress. -/
theorem phaseSearchProgress_of_horizonAndAnchor
    {target childHorizon childAnchor childLocal parentHorizon
      parentAnchor parentLocal : Nat}
    (htime : parentHorizon ≤ childHorizon)
    (hanchor : childAnchor < parentAnchor) :
    PhaseSearchProgress target
      ⟨childHorizon, childAnchor, .normal, childLocal⟩
      ⟨parentHorizon, parentAnchor, .normal, parentLocal⟩ := by
  have hbudget := missingBelowCount_antitone (m := target) htime
  rcases Nat.eq_or_lt_of_le hbudget with heq | hlt
  · change Prod.Lex Nat.lt (Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt))
      (missingBelowCount target childHorizon,
        (childAnchor, (SearchPhase.normal.rank, childLocal)))
      (missingBelowCount target parentHorizon,
        (parentAnchor, (SearchPhase.normal.rank, parentLocal)))
    rw [heq]
    exact Prod.Lex.right _ (Prod.Lex.left _ _ hanchor)
  · exact Prod.Lex.left _ _ hlt

/-- A positive first-occurring value above the target gives an ordinary
normal-search certificate at every horizon containing its first time. -/
theorem firstAt_normalSearchInvariant
    {target value firstTime horizon : Nat}
    (htarget : 0 < target)
    (htargetValue : target ≤ value)
    (hfirst : FirstAt a value firstTime)
    (htime : firstTime ≤ horizon) :
    NormalSearchInvariant target
      ⟨horizon, value, .normal, value⟩ := by
  have hfirstPositive : 0 < firstTime := by
    by_cases hzero : firstTime = 0
    · subst firstTime
      have hvalue := firstAt_time_zero_value hfirst
      omega
    · omega
  rcases exists_coordinatesAt hfirstPositive with ⟨q, r, hcoord⟩
  exact ⟨value, firstTime, q, r, {
    target_positive := htarget
    node_eq := rfl
    target_le := htargetValue
    first := hfirst
    firstTime_le_horizon := htime
    coordinates := hcoord
  }⟩

/-- The parent-drop obstruction is an artifact of requiring the stronger
negative-coordinate invariant.  Its first occurrence always gives an
ordinary semantic normal child. -/
theorem normalParentDrop_phaseSemantic
    {target n activeParent horizon value firstTime : Nat}
    (htarget : 0 < target)
    (hevidence : NormalParentDropEvidence target horizon value firstTime
      ⟨n, activeParent, .normal, a n⟩
      ⟨horizon, value, .normal, a horizon⟩) :
    let child : PhaseSearchNode :=
      ⟨max horizon firstTime, value, .normal, value⟩
    PhaseSemanticInvariant target child ∧
      PhaseSearchProgress target child
        ⟨n, activeParent, .normal, a n⟩ := by
  let child : PhaseSearchNode :=
    ⟨max horizon firstTime, value, .normal, value⟩
  have hsemantic : PhaseSemanticInvariant target child := .normal
    (firstAt_normalSearchInvariant htarget hevidence.target_le_anchor
      hevidence.anchor_first (Nat.le_max_right _ _))
  refine ⟨hsemantic, ?_⟩
  have hmono := missingBelowCount_antitone
    (m := target) (Nat.le_max_left horizon firstTime)
  have hp : Prod.Lex Nat.lt (Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt))
      (missingBelowCount target horizon,
        (value, (SearchPhase.normal.rank, a horizon)))
      (missingBelowCount target n,
        (activeParent, (SearchPhase.normal.rank, a n))) := by
    simpa [PhaseSearchProgress, phaseSearchRank] using hevidence.progress
  have hsourceBudget : missingBelowCount target horizon ≤
      missingBelowCount target n := natQuadLex_fst_le hp
  have hchildBudget : missingBelowCount target (max horizon firstTime) ≤
      missingBelowCount target n := Nat.le_trans hmono hsourceBudget
  rcases Nat.eq_or_lt_of_le hchildBudget with heq | hlt
  · change Prod.Lex Nat.lt (Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt))
      (missingBelowCount target (max horizon firstTime),
        (value, (SearchPhase.normal.rank, value)))
      (missingBelowCount target n,
        (activeParent, (SearchPhase.normal.rank, a n)))
    rw [heq]
    exact Prod.Lex.right _
      (Prod.Lex.left _ _ hevidence.anchor_drop)
  · exact Prod.Lex.left _ _ hlt

/-- The residual forward-epoch configuration.  The new value is below the
target, while restarting from the old value has exactly the parent's rank. -/
structure NormalEpochSharpObstruction
    (target n activeParent time : Nat) : Prop where
  new_value_below_target : a time < target
  old_value_above_target : target < a n
  anchor_tight : activeParent = a n
  budget_unchanged :
    missingBelowCount target time = missingBelowCount target n
  orbit_drop : a time < a n

theorem NormalEpochSharpObstruction.newValue_not_normal
    {target n activeParent time : Nat}
    (h : NormalEpochSharpObstruction target n activeParent time) :
    ¬ NormalSearchInvariant target
      ⟨time, a time, .normal, a time⟩ := by
  rintro ⟨value, firstTime, q, r, hcert⟩
  have hvalue : value = a time := by
    simpa using (congrArg PhaseSearchNode.anchorParent hcert.node_eq).symm
  exact (Nat.not_le_of_gt h.new_value_below_target) (hvalue ▸ hcert.target_le)

theorem NormalEpochSharpObstruction.oldValue_not_progress
    {target n activeParent time : Nat}
    (h : NormalEpochSharpObstruction target n activeParent time) :
    ¬ PhaseSearchProgress target
      ⟨time, a n, .normal, a n⟩
      ⟨n, activeParent, .normal, a n⟩ := by
  intro hp
  have hp' : Prod.Lex Nat.lt (Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt))
      (missingBelowCount target time,
        (a n, (SearchPhase.normal.rank, a n)))
      (missingBelowCount target n,
        (a n, (SearchPhase.normal.rank, a n))) := by
    simpa [PhaseSearchProgress, phaseSearchRank, h.anchor_tight] using hp
  have htail := natQuadLex_tail_of_fst_eq hp' h.budget_unchanged
  have hphaseLocal := natTripleLex_tail_of_fst_eq htail rfl
  have hlocal := natPairLex_tail_of_fst_eq hphaseLocal rfl
  exact Nat.lt_irrefl _ hlocal

/-- Exact closure theorem for a forward negative-epoch exit.  Above-target
new values close directly.  A below-target exit restarts from the old value
when either the history budget or active anchor decreased.  The final branch
is a literal rank equality, recorded by `NormalEpochSharpObstruction`. -/
theorem normalEpochExit_phaseSemantic_or_sharp
    {target n activeParent time quotient remainder q r : Nat}
    (htarget : 0 < target)
    (hinv : NormalPhaseInvariantAt target
      ⟨n, activeParent, .normal, a n⟩ n q r)
    (hevidence : NormalEpochExitEvidence target time quotient remainder
      ⟨n, activeParent, .normal, a n⟩
      ⟨time, activeParent, .normal, a time⟩) :
    (∃ witness, a witness = target) ∨
      (∃ child, PhaseSemanticInvariant target child ∧
        PhaseSearchProgress target child
          ⟨n, activeParent, .normal, a n⟩) ∨
      NormalEpochSharpObstruction target n activeParent time := by
  by_cases htargetOld : target = a n
  · exact Or.inl ⟨n, htargetOld.symm⟩
  · have htargetOldLt : target < a n :=
      Nat.lt_of_le_of_ne hinv.target_le_value htargetOld
    by_cases hnew : target ≤ a time
    · rcases history_member_has_firstAt (current_mem_valuesThrough time) with
        ⟨firstTime, hfirstTime, hfirst⟩
      let child : PhaseSearchNode :=
        ⟨time, a time, .normal, a time⟩
      have hsemantic : PhaseSemanticInvariant target child := .normal
        (firstAt_normalSearchInvariant htarget hnew hfirst hfirstTime)
      refine Or.inr (Or.inl ⟨child, hsemantic, ?_⟩)
      have hp : Prod.Lex Nat.lt (Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt))
          (missingBelowCount target time,
            (activeParent, (SearchPhase.normal.rank, a time)))
          (missingBelowCount target n,
            (activeParent, (SearchPhase.normal.rank, a n))) := by
        simpa [PhaseSearchProgress, phaseSearchRank] using hevidence.progress
      have hbudgetLe := natQuadLex_fst_le hp
      rcases Nat.eq_or_lt_of_le hbudgetLe with hbudgetEq | hbudgetDrop
      · change missingBelowCount target time =
          missingBelowCount target n at hbudgetEq
        have htail := natQuadLex_tail_of_fst_eq hp hbudgetEq
        have hphaseLocal := natTripleLex_tail_of_fst_eq htail rfl
        have hlocal := natPairLex_tail_of_fst_eq hphaseLocal rfl
        change a time < a n at hlocal
        change Prod.Lex Nat.lt (Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt))
          (missingBelowCount target time,
            (a time, (SearchPhase.normal.rank, a time)))
          (missingBelowCount target n,
            (activeParent, (SearchPhase.normal.rank, a n)))
        rw [hbudgetEq]
        exact Prod.Lex.right _ (Prod.Lex.left _ _
          (Nat.lt_of_lt_of_le hlocal hinv.value_le_anchor))
      · exact Prod.Lex.left _ _ hbudgetDrop
    · have hnewBelow : a time < target := Nat.lt_of_not_ge hnew
      have htime : n ≤ time := Nat.le_of_lt hevidence.time_advance
      have hbudgetLe := missingBelowCount_antitone
        (m := target) htime
      rcases Nat.eq_or_lt_of_le hbudgetLe with hbudgetEq | hbudgetDrop
      · by_cases hanchor : a n < activeParent
        · rcases history_member_has_firstAt (current_mem_valuesThrough n) with
            ⟨firstTime, hfirstTime, hfirst⟩
          let child : PhaseSearchNode := ⟨time, a n, .normal, a n⟩
          have hsemantic : PhaseSemanticInvariant target child := .normal
            (firstAt_normalSearchInvariant htarget hinv.target_le_value
              hfirst (Nat.le_trans hfirstTime htime))
          exact Or.inr (Or.inl ⟨child, hsemantic,
            phaseSearchProgress_of_horizonAndAnchor htime hanchor⟩)
        · have hanchorEq : activeParent = a n := by
            have : a n ≤ activeParent := by
              simpa using hinv.value_le_anchor
            omega
          have horbitDrop : a time < a n := by
            have hp : Prod.Lex Nat.lt
                (Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt))
                (missingBelowCount target time,
                  (activeParent, (SearchPhase.normal.rank, a time)))
                (missingBelowCount target n,
                  (activeParent, (SearchPhase.normal.rank, a n))) := by
              simpa [PhaseSearchProgress, phaseSearchRank] using
                hevidence.progress
            have htail := natQuadLex_tail_of_fst_eq hp hbudgetEq
            have hphaseLocal := natTripleLex_tail_of_fst_eq htail rfl
            exact natPairLex_tail_of_fst_eq hphaseLocal rfl
          exact Or.inr (Or.inr {
            new_value_below_target := hnewBelow
            old_value_above_target := htargetOldLt
            anchor_tight := hanchorEq
            budget_unchanged := hbudgetEq
            orbit_drop := horbitDrop
          })
      · rcases history_member_has_firstAt (current_mem_valuesThrough n) with
          ⟨firstTime, hfirstTime, hfirst⟩
        let child : PhaseSearchNode := ⟨time, a n, .normal, a n⟩
        have hsemantic : PhaseSemanticInvariant target child := .normal
          (firstAt_normalSearchInvariant htarget hinv.target_le_value
            hfirst (Nat.le_trans hfirstTime htime))
        exact Or.inr (Or.inl ⟨child, hsemantic,
          Prod.Lex.left _ _ hbudgetDrop⟩)

/-- A full negative-normal invariant can always be normalized to the weaker
ordinary semantic normal certificate.  If its anchor is already the current
value the numeric node is unchanged; otherwise normalization itself lowers
the anchor, and transitivity retains progress from the original node. -/
theorem normalPhaseInvariant_phaseSemantic_progress
    {target n activeParent q r : Nat}
    (htarget : 0 < target)
    (hinv : NormalPhaseInvariantAt target
      ⟨n, activeParent, .normal, a n⟩ n q r)
    {parent : PhaseSearchNode}
    (hprogress : PhaseSearchProgress target
      ⟨n, activeParent, .normal, a n⟩ parent) :
    ∃ child, PhaseSemanticInvariant target child ∧
      PhaseSearchProgress target child parent := by
  rcases history_member_has_firstAt (current_mem_valuesThrough n) with
    ⟨firstTime, hfirstTime, hfirst⟩
  let child : PhaseSearchNode := ⟨n, a n, .normal, a n⟩
  have hsemantic : PhaseSemanticInvariant target child := .normal
    (firstAt_normalSearchInvariant htarget hinv.target_le_value
      hfirst hfirstTime)
  rcases Nat.eq_or_lt_of_le hinv.value_le_anchor with hanchorEq | hanchorDrop
  · change a n = activeParent at hanchorEq
    subst activeParent
    exact ⟨child, hsemantic, hprogress⟩
  · exact ⟨child, hsemantic,
      (phaseSearchProgress_of_horizonAndAnchor (Nat.le_refl _)
        hanchorDrop).trans hprogress⟩

/-- Residual obligations after replacing the strong negative-normal domain by
the actual `PhaseSemanticInvariant` domain.  In particular, the old generic
`NormalPhaseObstruction` is absent. -/
inductive NegativeNormalSemanticResidual
    (target : Nat) (parent : PhaseSearchNode) : Prop
  | epoch_sharp (n activeParent time : Nat)
      (parent_eq : parent = ⟨n, activeParent, .normal, a n⟩)
      (obstruction : NormalEpochSharpObstruction
        target n activeParent time) :
      NegativeNormalSemanticResidual target parent
  | debt_anchor (time value firstTime : Nat)
      (target_le : target ≤ value)
      (first : FirstAt a value firstTime)
      (firstTime_lt : firstTime < time)
      (anchor_not_above : parent.anchorParent ≤ value)
      (progress : PhaseSearchProgress target
        ⟨time, parent.anchorParent, .debt, firstTime⟩ parent) :
      NegativeNormalSemanticResidual target parent

/-- Semantic refinement of the complete negative-normal classification.
Every former parent-drop obstruction closes, as do all forward exits except
the sharp rank-equality case.  The unrelated debt-anchor boundary is retained
verbatim. -/
theorem negativeNormal_phaseSemanticStep_or_residual
    {target activeParent n q r : Nat}
    (htargetPositive : 0 < target)
    (hinv : NormalPhaseInvariantAt target
      ⟨n, activeParent, .normal, a n⟩ n q r) :
    (∃ witness, a witness = target) ∨
      (∃ child, PhaseSemanticInvariant target child ∧
        PhaseSearchProgress target child
          ⟨n, activeParent, .normal, a n⟩) ∨
      NegativeNormalSemanticResidual target
        ⟨n, activeParent, .normal, a n⟩ := by
  cases negativeNormal_classify htargetPositive hinv with
  | target_occurs witness hvalue =>
      exact Or.inl ⟨witness, hvalue⟩
  | normal_child child hchild hprogress =>
      rcases hchild with ⟨cn, cq, cr, hchildInv⟩
      let childAnchor := child.anchorParent
      have hnode : child =
          ⟨cn, childAnchor, .normal, a cn⟩ := hchildInv.node_eq
      have hchildInv' : NormalPhaseInvariantAt target
          ⟨cn, childAnchor, .normal, a cn⟩ cn cq cr := by
        simpa [hnode] using hchildInv
      have hprogress' : PhaseSearchProgress target
          ⟨cn, childAnchor, .normal, a cn⟩
          ⟨n, activeParent, .normal, a n⟩ := by
        simpa [hnode] using hprogress
      exact Or.inr (Or.inl
        (normalPhaseInvariant_phaseSemantic_progress htargetPositive
          hchildInv' hprogress'))
  | debt_child child value firstTime hchild hprogress =>
      exact Or.inr (Or.inl
        ⟨child, .debt value firstTime hchild, hprogress⟩)
  | normal_obstruction child hobstruction =>
      cases hobstruction with
      | parent_drop horizon value firstTime hevidence _ =>
          have hchildEq := hevidence.child_eq
          subst child
          rcases normalParentDrop_phaseSemantic htargetPositive hevidence with
            ⟨hsemantic, hprogress⟩
          exact Or.inr (Or.inl ⟨_, hsemantic, hprogress⟩)
      | epoch_exit time quotient remainder hevidence _ =>
          have hchildEq := hevidence.child_eq
          subst child
          rcases normalEpochExit_phaseSemantic_or_sharp
              htargetPositive hinv hevidence with
            hoccurs | hsemantic | hsharp
          · exact Or.inl hoccurs
          · exact Or.inr (Or.inl hsemantic)
          · exact Or.inr (Or.inr (.epoch_sharp n activeParent time rfl hsharp))
  | debt_anchor_obstruction time value firstTime htarget hfirst htime
      hanchor hprogress =>
      exact Or.inr (Or.inr
        (.debt_anchor time value firstTime htarget hfirst htime
          hanchor hprogress))

end Recaman
