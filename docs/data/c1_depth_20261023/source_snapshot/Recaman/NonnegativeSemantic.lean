import Recaman.BoundaryAudit
import Recaman.PhaseProgress

namespace Recaman

private theorem nonnegativeSemantic_natQuadLex_fst_le
    {x y : Nat × (Nat × (Nat × Nat))}
    (h : Prod.Lex Nat.lt (Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt)) x y) :
    x.1 ≤ y.1 := by
  rcases x with ⟨xa, xb⟩
  rcases y with ⟨ya, yb⟩
  cases h with
  | left _ _ hlt => exact Nat.le_of_lt hlt
  | right _ _ => exact Nat.le_refl _

private theorem nonnegativeSemantic_natQuadLex_tail
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

private theorem nonnegativeSemantic_natTripleLex_tail
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

private theorem nonnegativeSemantic_natPairLex_tail
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

/-- If a normal rank step keeps the old anchor but its actual child value is
above the target, the child can be re-anchored at that value without losing
progress.  A too-large new anchor is possible only when the history-budget
component already decreased. -/
theorem normalProgress_reanchorAtValue
    {target parentTime parentAnchor parentValue childTime childValue : Nat}
    (hparentBound : parentValue ≤ parentAnchor)
    (hprogress : PhaseSearchProgress target
      ⟨childTime, parentAnchor, .normal, childValue⟩
      ⟨parentTime, parentAnchor, .normal, parentValue⟩) :
    PhaseSearchProgress target
      ⟨childTime, childValue, .normal, childValue⟩
      ⟨parentTime, parentAnchor, .normal, parentValue⟩ := by
  by_cases hanchorDrop : childValue < parentAnchor
  · have hstep : PhaseSearchProgress target
        ⟨childTime, childValue, .normal, childValue⟩
        ⟨childTime, parentAnchor, .normal, childValue⟩ :=
      phaseSearchProgress_of_horizonAndAnchor (Nat.le_refl _)
        hanchorDrop
    exact hstep.trans hprogress
  · have hparentLeChild : parentAnchor ≤ childValue :=
      Nat.le_of_not_gt hanchorDrop
    have hp : Prod.Lex Nat.lt (Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt))
        (missingBelowCount target childTime,
          (parentAnchor, (SearchPhase.normal.rank, childValue)))
        (missingBelowCount target parentTime,
          (parentAnchor, (SearchPhase.normal.rank, parentValue))) := by
      simpa [PhaseSearchProgress, phaseSearchRank] using hprogress
    have hbudgetLe := nonnegativeSemantic_natQuadLex_fst_le hp
    rcases Nat.eq_or_lt_of_le hbudgetLe with hbudgetEq | hbudgetDrop
    · have hlocalDrop : childValue < parentValue := by
        change missingBelowCount target childTime =
          missingBelowCount target parentTime at hbudgetEq
        have htail := nonnegativeSemantic_natQuadLex_tail hp hbudgetEq
        have hphaseLocal := nonnegativeSemantic_natTripleLex_tail htail rfl
        exact nonnegativeSemantic_natPairLex_tail hphaseLocal rfl
      have : parentValue ≤ childValue :=
        Nat.le_trans hparentBound hparentLeChild
      omega
    · exact Prod.Lex.left _ _ hbudgetDrop

/-- Semantic version of the nonnegative history frontier on a regular level.

Every raw parent descent is rebuilt as an ordinary semantic normal node.
Every forward orbit step either stays above the target and is re-anchored at
its new value, or crosses below the target; the latter necessarily witnesses
the target or lowers the missing-history budget.  The old quotient-zero
boundary is impossible because a semantic normal start has
`target ≤ a n`, whereas quotient zero on level `g<target` has `a n=g`.

Consequently no low-level or quotient-zero residual is needed under exactly
the hypotheses already carried by a target-valid normal node. -/
theorem nonnegative_epoch_phaseSemanticOutcome
    {target activeParent n q r g : Nat}
    (htargetPositive : 0 < target)
    (htimeReady : target ≤ n + 1)
    (htargetValue : target ≤ a n)
    (hvalueBound : a n ≤ activeParent)
    (hlevelLower : 3 ≤ g)
    (hlevelUpper : g < target)
    (hcoord : CoordinatesAt n q r)
    (hpotential : potential q r = Int.ofNat g) :
    (∃ witness, a witness = target) ∨
      ∃ child, PhaseSemanticInvariant target child ∧
        PhaseSearchProgress target child
          ⟨n, activeParent, .normal, a n⟩ := by
  rcases nonnegative_epoch_historySearchOutcome hvalueBound htimeReady
      hlevelLower hlevelUpper hcoord hpotential with
    hoccurs | hparent | hqzero | hforward
  · exact Or.inl hoccurs
  · rcases hparent with
      ⟨y, fy, htargetY, hfirstY, hyAnchor, _⟩
    let childHorizon := max n fy
    let child : PhaseSearchNode :=
      ⟨childHorizon, y, .normal, y⟩
    have hsemantic : PhaseSemanticInvariant target child := .normal
      (firstAt_normalSearchInvariant htargetPositive htargetY hfirstY
        (Nat.le_max_right _ _))
    have hprogress : PhaseSearchProgress target child
        ⟨n, activeParent, .normal, a n⟩ :=
      phaseSearchProgress_of_horizonAndAnchor
        (Nat.le_max_left _ _) hyAnchor
    exact Or.inr ⟨child, hsemantic, hprogress⟩
  · subst q
    have hvalue : a n = r := by
      simpa using hcoord.eqn
    have hlevel : r = g := by
      apply Int.ofNat_inj.mp
      simpa [potential, upperTri] using hpotential
    omega
  · rcases hforward with
      ⟨t, k, s, hnt, _, htcoord, _, hrawProgress⟩
    have hphaseProgress : PhaseSearchProgress target
        ⟨t, activeParent, .normal, a t⟩
        ⟨n, activeParent, .normal, a n⟩ :=
      hrawProgress.toNormalPhaseSearchProgress
    by_cases htargetAtT : target ≤ a t
    · rcases history_member_has_firstAt (current_mem_valuesThrough t) with
        ⟨ft, hft, hfirstT⟩
      let child : PhaseSearchNode := ⟨t, a t, .normal, a t⟩
      have hsemantic : PhaseSemanticInvariant target child := .normal
        (firstAt_normalSearchInvariant htargetPositive htargetAtT
          hfirstT hft)
      exact Or.inr ⟨child, hsemantic,
        normalProgress_reanchorAtValue hvalueBound hphaseProgress⟩
    · have hbelow : a t < target := Nat.lt_of_not_ge htargetAtT
      rcases orbit_downcrossing_occurs_or_budgetDrop
          (Nat.le_of_lt hnt) htargetValue hbelow with
        hoccurs | hbudgetDrop
      · rcases hoccurs with ⟨u, _, _, hu⟩
        exact Or.inl ⟨u, hu⟩
      · rcases history_member_has_firstAt (current_mem_valuesThrough n) with
          ⟨fn, hfn, hfirstN⟩
        let child : PhaseSearchNode := ⟨t, a n, .normal, a n⟩
        have hsemantic : PhaseSemanticInvariant target child := .normal
          (firstAt_normalSearchInvariant htargetPositive htargetValue
            hfirstN (Nat.le_trans hfn (Nat.le_of_lt hnt)))
        exact Or.inr ⟨child, hsemantic,
          Prod.Lex.left _ _ hbudgetDrop⟩

/-- Exact boundary left by the current nonnegative epoch API for a general
orbit-ready normal node.  Quotient zero is absent: together with
`target ≤ a n` it contradicts being strictly below the target level. -/
structure NonnegativeLowLevelResidualAt
    (target activeParent n q r level : Nat) : Prop where
  time_ready : target ≤ n + 1
  target_le_value : target ≤ a n
  value_le_anchor : a n ≤ activeParent
  coordinates : CoordinatesAt n q r
  quotient_positive : 0 < q
  potential_eq : potential q r = Int.ofNat level
  level_le_two : level ≤ 2
  level_lt_target : level < target

/-- Complete semantic classification of a nonnegative potential strictly
below the target.  Regular levels `g≥3` close by
`nonnegative_epoch_phaseSemanticOutcome`; the only residual is the literal
three-level band `g=0,1,2`. -/
theorem nonnegative_epoch_phaseSemanticStep_or_lowLevel
    {target activeParent n q r : Nat}
    (htargetPositive : 0 < target)
    (htimeReady : target ≤ n + 1)
    (htargetValue : target ≤ a n)
    (hvalueBound : a n ≤ activeParent)
    (hcoord : CoordinatesAt n q r)
    (hnonnegative : 0 ≤ potential q r)
    (hbelow : potential q r < Int.ofNat target) :
    (∃ witness, a witness = target) ∨
      (∃ child, PhaseSemanticInvariant target child ∧
        PhaseSearchProgress target child
          ⟨n, activeParent, .normal, a n⟩) ∨
      ∃ level, NonnegativeLowLevelResidualAt
        target activeParent n q r level := by
  have hqpos : 0 < q := by
    cases q with
    | zero =>
        have hvalue : a n = r := by simpa using hcoord.eqn
        have hcast : Int.ofNat target ≤ Int.ofNat r := by
          exact Int.ofNat_le.mpr (by simpa [hvalue] using htargetValue)
        simp [potential, upperTri] at hbelow
        omega
    | succ q => omega
  let level := r - upperTri q
  have htri : upperTri q ≤ r :=
    (potential_nonnegative_iff q r).mp hnonnegative
  have hpotential : potential q r = Int.ofNat level := by
    apply (potential_eq_ofNat_iff q r level).mpr
    simp only [level]
    omega
  have hlevelTarget : level < target := by
    rw [hpotential] at hbelow
    exact Int.ofNat_lt.mp hbelow
  by_cases hregular : 3 ≤ level
  · rcases nonnegative_epoch_phaseSemanticOutcome htargetPositive
        htimeReady htargetValue hvalueBound hregular hlevelTarget
        hcoord hpotential with hoccurs | hchild
    · exact Or.inl hoccurs
    · exact Or.inr (Or.inl hchild)
  · exact Or.inr (Or.inr ⟨level, {
      time_ready := htimeReady
      target_le_value := htargetValue
      value_le_anchor := hvalueBound
      coordinates := hcoord
      quotient_positive := hqpos
      potential_eq := hpotential
      level_le_two := by omega
      level_lt_target := hlevelTarget
    }⟩)

end Recaman
