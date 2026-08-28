import Recaman.BoundaryAudit

namespace Recaman

/-- Complete semantic closure of a valid negative-normal phase.

The parent-drop branch restarts from the certified first-occurring anchor.
The forward branch either supplies a semantic child or crosses the target;
its apparent rank-equality obstruction is impossible because a downward
target crossing must consume history budget.  Finally, the quotient-one
exception already contradicts the normal invariant unless the target occurs.
-/
theorem negativeNormal_phaseSemanticStep
    {target activeParent n q r : Nat}
    (htargetPositive : 0 < target)
    (hinv : NormalPhaseInvariantAt target
      ⟨n, activeParent, .normal, a n⟩ n q r) :
    (∃ witness, a witness = target) ∨
      ∃ child, PhaseSemanticInvariant target child ∧
        PhaseSearchProgress target child
          ⟨n, activeParent, .normal, a n⟩ := by
  rcases negative_epoch_historySearchOutcome_or_qOneDebt
      htargetPositive hinv.time_ready hinv.value_le_anchor
      hinv.coordinates hinv.negative with
    hoccurs | hparent | horbit |
      ⟨t, remainder, landing, hnt, htvalue, htcoord, htborrow, _, _,
        hnonnegative, hbelow⟩
  · rcases hoccurs with ⟨witness, hvalue⟩
    exact Or.inl ⟨witness, hvalue⟩
  · rcases hparent with
      ⟨horizon, value, firstTime, htargetValue, hfirst,
        hanchorDrop, hprogress⟩
    have hevidence : NormalParentDropEvidence target horizon value firstTime
        ⟨n, activeParent, .normal, a n⟩
        ⟨horizon, value, .normal, a horizon⟩ := {
      child_eq := rfl
      target_le_anchor := htargetValue
      anchor_first := hfirst
      anchor_drop := hanchorDrop
      progress := hprogress.toNormalPhaseSearchProgress
    }
    rcases normalParentDrop_phaseSemantic htargetPositive hevidence with
      ⟨hsemantic, hphaseProgress⟩
    exact Or.inr ⟨_, hsemantic, hphaseProgress⟩
  · rcases horbit with ⟨time, quotient, remainder, htime, hcoordinates,
      hprogress⟩
    have hevidence : NormalEpochExitEvidence target time quotient remainder
        ⟨n, activeParent, .normal, a n⟩
        ⟨time, activeParent, .normal, a time⟩ := {
      child_eq := rfl
      time_advance := htime
      time_ready := Nat.le_trans hinv.time_ready (by omega)
      coordinates := hcoordinates
      progress := hprogress.toNormalPhaseSearchProgress
    }
    rcases normalEpochExit_phaseSemantic_or_sharp
        htargetPositive hinv hevidence with
      hoccurs | hsemantic | hsharp
    · exact Or.inl hoccurs
    · exact Or.inr hsemantic
    · exact Or.inl (hsharp.target_occurs (Nat.le_of_lt htime))
  · exact Or.inl (normalPhase_qOneDebt_already_occurs hinv hnt htvalue
      htcoord htborrow hnonnegative hbelow)

end Recaman
