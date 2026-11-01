import Recaman.Diagonal

namespace Recaman

/-- The normal search may enter a one-way diagonal-debt phase.  The numeric
order is chosen so that entering debt is a strict rank decrease. -/
inductive SearchPhase where
  | debt
  | normal
deriving Repr, DecidableEq

def SearchPhase.rank : SearchPhase → Nat
  | .debt => 0
  | .normal => 1

/-- A phase-aware node keeps the history horizon fixed while an earlier
first occurrence is inspected.  `localMeasure` is the orbit value in normal mode
and the decreasing first-occurrence time in debt mode. -/
structure PhaseSearchNode where
  horizon : Nat
  anchorParent : Nat
  phase : SearchPhase
  localMeasure : Nat
deriving Repr, DecidableEq

/-- Four-component rank: history budget, anchor parent, phase, local debt or
orbit coordinate. -/
def phaseSearchRank (m : Nat) (node : PhaseSearchNode) :
    Nat × (Nat × (Nat × Nat)) :=
  (missingBelowCount m node.horizon,
    (node.anchorParent, (node.phase.rank, node.localMeasure)))

def PhaseSearchProgress (m : Nat)
    (child parent : PhaseSearchNode) : Prop :=
  Prod.Lex Nat.lt (Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt))
    (phaseSearchRank m child) (phaseSearchRank m parent)

/-- The right-nested lexicographic order on four naturals is well founded. -/
theorem natQuadLex_wellFounded :
    WellFounded
      (Prod.Lex Nat.lt (Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt))) := by
  apply WellFounded.intro
  intro p
  exact Prod.lexAccessible
    (Nat.lt_wfRel.wf.apply p.1)
    (fun triple => natTripleLex_wellFounded.apply triple)
    p.2

/-- Pullback of the four-coordinate order along `phaseSearchRank`. -/
theorem phaseSearchProgress_wellFounded (m : Nat) :
    WellFounded (PhaseSearchProgress m) := by
  apply WellFounded.intro
  intro node
  generalize hx : phaseSearchRank m node = x
  have hacc := natQuadLex_wellFounded.apply x
  induction hacc generalizing node with
  | intro x _ ih =>
      apply Acc.intro node
      intro child hchild
      have hrank :
          Prod.Lex Nat.lt (Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt))
            (phaseSearchRank m child) x := by
        simpa [PhaseSearchProgress, hx] using hchild
      exact ih (phaseSearchRank m child) hrank child rfl

/-- Entering diagonal debt decreases the phase component, independently of
the newly exposed first-occurrence time. -/
theorem phaseSearch_enterDebt
    {m horizon anchor normalLocal debtTime : Nat} :
    PhaseSearchProgress m
      ⟨horizon, anchor, .debt, debtTime⟩
      ⟨horizon, anchor, .normal, normalLocal⟩ := by
  exact Prod.Lex.right _
    (Prod.Lex.right _ (Prod.Lex.left _ _ (by
      change 0 < 1
      omega)))

/-- While debt remains active, moving to an earlier first occurrence lowers
the local component without changing the known-history horizon. -/
theorem phaseSearch_debtTimeDrop
    {m horizon anchor childTime parentTime : Nat}
    (htime : childTime < parentTime) :
    PhaseSearchProgress m
      ⟨horizon, anchor, .debt, childTime⟩
      ⟨horizon, anchor, .debt, parentTime⟩ := by
  exact Prod.Lex.right _
    (Prod.Lex.right _ (Prod.Lex.right _ htime))

/-- Returning from debt to normal search is safe once the anchor parent has
strictly decreased; the phase increase is then hidden behind that decrease. -/
theorem phaseSearch_exitDebt_of_anchorDrop
    {m horizon childAnchor parentAnchor childLocal parentTime : Nat}
    (hanchor : childAnchor < parentAnchor) :
    PhaseSearchProgress m
      ⟨horizon, childAnchor, .normal, childLocal⟩
      ⟨horizon, parentAnchor, .debt, parentTime⟩ := by
  exact Prod.Lex.right _ (Prod.Lex.left _ _ hanchor)

/-- The maximal-tail theorem now enters the well-founded debt phase without
any bound on the blocker's value.  Its earlier first time is stored as the
debt-local coordinate while the history horizon remains at the diagonal. -/
theorem diagonal_successor_or_entersPhaseDebt
    {n anchor normalLocal : Nat}
    (hdiagonal : a (n + 2) = n + 2) :
    (∃ u, a u = n + 3) ∨
      ∃ y fy,
        n + 3 ≤ y ∧ FirstAt a y fy ∧ fy < n + 2 ∧
        PhaseSearchProgress (n + 3)
          ⟨n + 2, anchor, .debt, fy⟩
          ⟨n + 2, anchor, .normal, normalLocal⟩ := by
  rcases diagonal_successor_occurs_or_earlierBlocker hdiagonal with
    hoccurs | ⟨y, fy, hy, hfirst, htime⟩
  · exact Or.inl hoccurs
  · exact Or.inr ⟨y, fy, hy, hfirst, htime,
      phaseSearch_enterDebt⟩

/-- Abstract completion obligation for the phase-aware search. -/
def PhaseSearchOracle (m : Nat) : Prop :=
  ∀ parent : PhaseSearchNode,
    (∃ t, a t = m) ∨
      ∃ child : PhaseSearchNode,
        PhaseSearchProgress m child parent

/-- A total phase-aware oracle reaches the target by well-founded induction. -/
theorem phaseSearchOracle_reaches_from {m : Nat}
    (horacle : PhaseSearchOracle m)
    (start : PhaseSearchNode) :
    ∃ t, a t = m := by
  apply (phaseSearchProgress_wellFounded m).induction start
  intro parent ih
  rcases horacle parent with hoccurs | ⟨child, hprogress⟩
  · exact hoccurs
  · exact ih child hprogress

theorem phaseSearchOracle_implies_occurs {m : Nat}
    (horacle : PhaseSearchOracle m) :
    ∃ t, a t = m := by
  exact phaseSearchOracle_reaches_from horacle
    ⟨0, 0, .normal, 0⟩

end Recaman
