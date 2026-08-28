import Recaman.PhaseSearch

namespace Recaman

/-- Inserting the fixed normal-phase component embeds the three-coordinate
history rank into the four-coordinate phase rank. -/
theorem natTripleLex_embed_normalPhase
    {x y : Nat × (Nat × Nat)}
    (hxy : Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt) x y) :
    Prod.Lex Nat.lt (Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt))
      (x.1, (x.2.1, (SearchPhase.normal.rank, x.2.2)))
      (y.1, (y.2.1, (SearchPhase.normal.rank, y.2.2))) := by
  rcases x with ⟨xbudget, xparent, xorbit⟩
  rcases y with ⟨ybudget, yparent, yorbit⟩
  cases hxy with
  | left _ _ hbudget =>
      exact Prod.Lex.left _ _ hbudget
  | right _ hrest =>
      cases hrest with
      | left _ _ hparent =>
          exact Prod.Lex.right _
            (Prod.Lex.left _ _ hparent)
      | right _ horbit =>
          exact Prod.Lex.right _
            (Prod.Lex.right _
              (Prod.Lex.right _ horbit))

/-- Every three-component history-search step embeds into the normal phase
of the four-component search rank. -/
theorem HistorySearchProgress.toNormalPhaseSearchProgress
    {m : Nat} {child parent : HistorySearchNode}
    (hprogress : HistorySearchProgress m child parent) :
    PhaseSearchProgress m
      ⟨child.horizon, child.parentValue, .normal, child.orbitValue⟩
      ⟨parent.horizon, parent.parentValue, .normal, parent.orbitValue⟩ := by
  exact natTripleLex_embed_normalPhase hprogress

/-- The rigid quotient-one endpoint of a negative epoch either witnesses the
target or enters the debt phase by a strict four-component rank step.  This
is a rank-level integration theorem: the child carries the earlier blocker
data explicitly, but no additional semantic debt invariant is assumed. -/
theorem qOneDebt_target_or_phaseSearchProgress
    {m activeParent normalLocal n t r s : Nat}
    (hm : m ≤ n + 1)
    (hnt : n ≤ t)
    (hcoord : CoordinatesAt t 1 r)
    (hborrow : BorrowData t 1 r 1 s)
    (hnonnegative : 0 ≤ potential 1 s)
    (hbelow : potential 1 s < Int.ofNat m) :
    (∃ u, a u = m) ∨
      ∃ y fy,
        m ≤ y ∧ FirstAt a y fy ∧ fy < t ∧
        PhaseSearchProgress m
          ⟨t, activeParent, .debt, fy⟩
          ⟨n, activeParent, .normal, normalLocal⟩ := by
  rcases qOneDebt_target_or_diagonalSuccessor
      hm hnt hcoord hborrow hnonnegative hbelow with
    hoccurs | ⟨hntEq, hmnext, hdiagonal⟩
  · exact Or.inl hoccurs
  · subst n
    subst m
    have htpos : 0 < t := by
      have hrlt := hcoord.remainder_lt
      omega
    rcases Nat.eq_or_lt_of_le
        (Nat.one_le_iff_ne_zero.mpr (by omega : t ≠ 0)) with
      htone | httwo
    · have ht : t = 1 := by omega
      subst t
      exact Or.inl ⟨4, by decide⟩
    · obtain ⟨k, hk⟩ : ∃ k, t = k + 2 := by
        exact ⟨t - 2, by omega⟩
      subst t
      rcases diagonal_successor_or_entersPhaseDebt
          (anchor := activeParent) (normalLocal := normalLocal)
          hdiagonal with
        hoccurs | ⟨y, fy, hy, hfirst, htime, hprogress⟩
      · exact Or.inl hoccurs
      · exact Or.inr ⟨y, fy, hy, hfirst, htime, hprogress⟩

/-- A complete negative epoch no longer needs `DiagonalSuccessorProperty` at
the rank level.  Every branch either witnesses the target or strictly lowers
the phase-aware search rank from the corresponding normal node. -/
theorem negative_epoch_phaseSearchOutcome
    {m activeParent n q r : Nat}
    (hmpos : 0 < m)
    (hm : m ≤ n + 1)
    (hbound : a n ≤ activeParent)
    (hcoord : CoordinatesAt n q r)
    (hnegative : potential q r < 0) :
    (∃ u, a u = m) ∨
      ∃ child : PhaseSearchNode,
        PhaseSearchProgress m child
          ⟨n, activeParent, .normal, a n⟩ := by
  rcases negative_epoch_historySearchOutcome_or_qOneDebt
      hmpos hm hbound hcoord hnegative with
    hoccurs | hparent | horbit |
      ⟨t, r', s, hnt, _, htcoord, htborrow, _, _,
        hnonnegative, hbelow⟩
  · exact Or.inl hoccurs
  · rcases hparent with
      ⟨horizon, y, fy, _, _, _, hprogress⟩
    exact Or.inr
      ⟨⟨horizon, y, .normal, a horizon⟩,
        hprogress.toNormalPhaseSearchProgress⟩
  · rcases horbit with ⟨u, _, _, _, _, hprogress⟩
    exact Or.inr
      ⟨⟨u, activeParent, .normal, a u⟩,
        hprogress.toNormalPhaseSearchProgress⟩
  · rcases qOneDebt_target_or_phaseSearchProgress
        (activeParent := activeParent) (normalLocal := a n)
        hm hnt htcoord htborrow hnonnegative hbelow with
      hoccurs | ⟨y, fy, _, _, _, hprogress⟩
    · exact Or.inl hoccurs
    · exact Or.inr ⟨⟨t, activeParent, .debt, fy⟩, hprogress⟩

end Recaman
