import Recaman.PhaseEpoch
import Recaman.PhaseSearchStart
import Recaman.DebtInvariant

namespace Recaman

/-- Semantic data for a normal node while the represented actual orbit state
is in a negative epoch.  `anchorParent` may be larger than the current orbit
value, but it must still bound it; this is the transport hypothesis used by
the history-frontier lemmas. -/
structure NormalPhaseInvariantAt
    (target : Nat) (node : PhaseSearchNode) (n q r : Nat) : Prop where
  node_eq : node = ⟨n, node.anchorParent, .normal, a n⟩
  time_ready : target ≤ n + 1
  target_le_value : target ≤ a n
  value_le_anchor : a n ≤ node.anchorParent
  coordinates : CoordinatesAt n q r
  negative : potential q r < 0

/-- Existential packaging of the orbit time and coordinates represented by a
semantically valid negative normal node. -/
def NormalPhaseInvariant (target : Nat) (node : PhaseSearchNode) : Prop :=
  ∃ n q r, NormalPhaseInvariantAt target node n q r

/-- Evidence retained by the parent-decrease branch of the negative-epoch
theorem.  The new anchor is a genuine first-occurring value above the target,
but the theorem's interface does not say that the orbit value at `horizon`
is above the target or has negative potential. -/
structure NormalParentDropEvidence
    (target horizon value firstTime : Nat)
    (parent child : PhaseSearchNode) : Prop where
  child_eq : child = ⟨horizon, value, .normal, a horizon⟩
  target_le_anchor : target ≤ value
  anchor_first : FirstAt a value firstTime
  anchor_drop : value < parent.anchorParent
  progress : PhaseSearchProgress target child parent

/-- Evidence retained by the forward orbit branch.  Coordinates and the
target/time bound survive, but negativity and the target/value/anchor bounds
are not exposed by the current epoch theorem's result type. -/
structure NormalEpochExitEvidence
    (target time quotient remainder : Nat)
    (parent child : PhaseSearchNode) : Prop where
  child_eq : child = ⟨time, parent.anchorParent, .normal, a time⟩
  time_ready : target ≤ time + 1
  coordinates : CoordinatesAt time quotient remainder
  progress : PhaseSearchProgress target child parent

/-- The two normal-child interfaces which may fail to re-establish the full
negative-normal invariant. -/
inductive NormalPhaseObstruction
    (target : Nat) (parent child : PhaseSearchNode) : Prop
  | parent_drop
      (horizon value firstTime : Nat)
      (evidence : NormalParentDropEvidence
        target horizon value firstTime parent child)
      (not_closed : ¬ NormalPhaseInvariant target child) :
      NormalPhaseObstruction target parent child
  | epoch_exit
      (time quotient remainder : Nat)
      (evidence : NormalEpochExitEvidence
        target time quotient remainder parent child)
      (not_closed : ¬ NormalPhaseInvariant target child) :
      NormalPhaseObstruction target parent child

/-- Exact semantic classification of a negative epoch from a valid normal
node.  A rank child is accepted only when its matching semantic invariant can
be rebuilt.  Otherwise the missing interface is returned explicitly.

The debt obstruction is especially sharp: all `DebtInvariant` fields except
`value < anchorParent` are available, and the obstruction records its literal
negation `anchorParent ≤ value`. -/
inductive NegativeNormalOutcome
    (target : Nat) (parent : PhaseSearchNode) : Prop
  | target_occurs (witness : Nat) (hvalue : a witness = target) :
      NegativeNormalOutcome target parent
  | normal_child (child : PhaseSearchNode)
      (invariant : NormalPhaseInvariant target child)
      (progress : PhaseSearchProgress target child parent) :
      NegativeNormalOutcome target parent
  | debt_child (child : PhaseSearchNode) (value firstTime : Nat)
      (invariant : DebtInvariant target child value firstTime)
      (progress : PhaseSearchProgress target child parent) :
      NegativeNormalOutcome target parent
  | normal_obstruction (child : PhaseSearchNode)
      (obstruction : NormalPhaseObstruction target parent child) :
      NegativeNormalOutcome target parent
  | debt_anchor_obstruction (time value firstTime : Nat)
      (target_le : target ≤ value)
      (first : FirstAt a value firstTime)
      (firstTime_lt : firstTime < time)
      (anchor_not_above : parent.anchorParent ≤ value)
      (progress : PhaseSearchProgress target
        ⟨time, parent.anchorParent, .debt, firstTime⟩ parent) :
      NegativeNormalOutcome target parent

/-- Semantic refinement of `negative_epoch_phaseSearchOutcome`.

This theorem uses the same negative-epoch analysis, but retains enough branch
data to test semantic closure.  It therefore describes precisely what a
future `RestrictedPhaseSearchOracle` may accept as a child and what still
needs an additional bridge lemma. -/
theorem negativeNormal_classify
    {target activeParent n q r : Nat}
    (htargetPositive : 0 < target)
    (hinv : NormalPhaseInvariantAt target
      ⟨n, activeParent, .normal, a n⟩ n q r) :
    NegativeNormalOutcome target
      ⟨n, activeParent, .normal, a n⟩ := by
  rcases negative_epoch_historySearchOutcome_or_qOneDebt
      htargetPositive hinv.time_ready hinv.value_le_anchor
      hinv.coordinates hinv.negative with
    hoccurs | hparent | horbit |
      ⟨t, r', s, hnt, _, htcoord, htborrow, _, _,
        hnonnegative, hbelow⟩
  · rcases hoccurs with ⟨u, hu⟩
    exact .target_occurs u hu
  · rcases hparent with
      ⟨horizon, y, fy, htargetY, hfirstY, hyAnchor, hprogress⟩
    let child : PhaseSearchNode :=
      ⟨horizon, y, .normal, a horizon⟩
    have hprogress' : PhaseSearchProgress target child
        ⟨n, activeParent, .normal, a n⟩ :=
      hprogress.toNormalPhaseSearchProgress
    classical
    by_cases hclosed : NormalPhaseInvariant target child
    · exact .normal_child child hclosed hprogress'
    · exact .normal_obstruction child (.parent_drop horizon y fy {
        child_eq := rfl
        target_le_anchor := htargetY
        anchor_first := hfirstY
        anchor_drop := hyAnchor
        progress := hprogress'
      } hclosed)
  · rcases horbit with ⟨u, p, v, hnu, hucoord, hprogress⟩
    let child : PhaseSearchNode := ⟨u, activeParent, .normal, a u⟩
    have hprogress' : PhaseSearchProgress target child
        ⟨n, activeParent, .normal, a n⟩ :=
      hprogress.toNormalPhaseSearchProgress
    classical
    by_cases hclosed : NormalPhaseInvariant target child
    · exact .normal_child child hclosed hprogress'
    · exact .normal_obstruction child (.epoch_exit u p v {
        child_eq := rfl
        time_ready := Nat.le_trans hinv.time_ready (by omega)
        coordinates := hucoord
        progress := hprogress'
      } hclosed)
  · rcases qOneDebt_target_or_phaseSearchProgress
        (activeParent := activeParent) (normalLocal := a n)
        hinv.time_ready hnt htcoord htborrow hnonnegative hbelow with
      hoccurs | ⟨y, fy, htargetY, hfirstY, hfy, hprogress⟩
    · rcases hoccurs with ⟨u, hu⟩
      exact .target_occurs u hu
    · let child : PhaseSearchNode := ⟨t, activeParent, .debt, fy⟩
      by_cases hyAnchor : y < activeParent
      · have hdebt : DebtInvariant target child y fy := {
          phase_eq := rfl
          local_eq := rfl
          target_le := htargetY
          first := hfirstY
          firstTime_lt_horizon := hfy
          value_lt_anchor := hyAnchor
        }
        exact .debt_child child y fy hdebt hprogress
      · exact .debt_anchor_obstruction t y fy htargetY hfirstY hfy
          (Nat.le_of_not_gt hyAnchor) hprogress

/-- The semantic domain naturally shared by the negative-normal and debt
parts of the phase search. -/
def NegativePhaseInvariant (target : Nat) (node : PhaseSearchNode) : Prop :=
  NormalPhaseInvariant target node ∨
    ∃ value firstTime, DebtInvariant target node value firstTime

/-- Residual obligations preventing the negative-epoch theorem from directly
supplying one clause of `RestrictedPhaseSearchOracle`. -/
inductive NegativeNormalRestrictedObstruction
    (target : Nat) (parent : PhaseSearchNode) : Prop
  | normal (child : PhaseSearchNode)
      (obstruction : NormalPhaseObstruction target parent child) :
      NegativeNormalRestrictedObstruction target parent
  | debt_anchor (time value firstTime : Nat)
      (target_le : target ≤ value)
      (first : FirstAt a value firstTime)
      (firstTime_lt : firstTime < time)
      (anchor_not_above : parent.anchorParent ≤ value)
      (progress : PhaseSearchProgress target
        ⟨time, parent.anchorParent, .debt, firstTime⟩ parent) :
      NegativeNormalRestrictedObstruction target parent

/-- Restricted-oracle form of `negativeNormal_classify`: from a negative
normal node, the epoch theorem either finds the target, produces a decreasing
child in the combined semantic domain, or returns the exact interface
obstruction which prevents semantic closure. -/
theorem negativeNormal_restrictedStep_or_obstruction
    {target activeParent n q r : Nat}
    (htargetPositive : 0 < target)
    (hinv : NormalPhaseInvariantAt target
      ⟨n, activeParent, .normal, a n⟩ n q r) :
    (∃ u, a u = target) ∨
      (∃ child,
        NegativePhaseInvariant target child ∧
        PhaseSearchProgress target child
          ⟨n, activeParent, .normal, a n⟩) ∨
      NegativeNormalRestrictedObstruction target
        ⟨n, activeParent, .normal, a n⟩ := by
  cases negativeNormal_classify htargetPositive hinv with
  | target_occurs witness hvalue =>
      exact Or.inl ⟨witness, hvalue⟩
  | normal_child child hchild hprogress =>
      exact Or.inr (Or.inl ⟨child, Or.inl hchild, hprogress⟩)
  | debt_child child value firstTime hchild hprogress =>
      exact Or.inr (Or.inl
        ⟨child, Or.inr ⟨value, firstTime, hchild⟩, hprogress⟩)
  | normal_obstruction child hobstruction =>
      exact Or.inr (Or.inr (.normal child hobstruction))
  | debt_anchor_obstruction time value firstTime htarget hfirst htime
      hanchor hprogress =>
      exact Or.inr (Or.inr
        (.debt_anchor time value firstTime htarget hfirst htime
          hanchor hprogress))

end Recaman
