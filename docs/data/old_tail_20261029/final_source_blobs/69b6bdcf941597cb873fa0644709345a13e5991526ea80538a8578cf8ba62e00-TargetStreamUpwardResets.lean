import Recaman.TargetTailResidualKernel
import Recaman.TargetCandidateTransitions

namespace Recaman

/-! # Upward blocker resets inside an unbounded right-terminal stream

An unbounded right-terminal stream extracts, after any completed target-low
comb in the strict tail, the next consecutive same-target macro episode.
Between two consecutive episodes the blocker either strictly increases, or
the second entry drops strictly below the first blocker; in the latter case
the second blocker itself is strictly smaller, because every comb entry
exceeds its own blocker.  Since blocker values cannot decrease forever, the
stream must perform an upward blocker reset, and it must do so after every
cutoff.

This module records that forcing and packages it with the global kernel
disjunction: a missing permanent tail either enters an eventual-high
candidate corridor, or supports infinitely many upward blocker resets along
consecutive same-target macro episodes.
-/

/-- Every unbounded right-terminal stream performs an upward blocker reset
between some pair of consecutive same-target macro episodes starting after
any prescribed cutoff.  The proof descends through consecutive episodes:
whenever the reset fails, the second entry lies strictly below the first
blocker, so the second blocker is strictly smaller, and strong induction on
the blocker value terminates the descent. -/
theorem UnboundedRightTerminalStream.exists_upwardReset_after
    {target tailStart root : Nat}
    (hstream : UnboundedRightTerminalStream target tailStart root)
    (htail : MissingPermanentAboveTail target tailStart)
    (cutoff : Nat) :
    ∃ s₁ k₁ blocker₁ s₂ k₂ blocker₂,
      cutoff < s₁ ∧
      TargetMacroSuccessor target tailStart
        s₁ k₁ blocker₁ s₂ k₂ blocker₂ ∧
      blocker₁ < blocker₂ := by
  classical
  have haux : ∀ blocker₁ s₁ k₁,
      cutoff < s₁ →
      tailStart < s₁ →
      nextSubtractionCandidate s₁ < target →
      HistoryTerminatedComb s₁ k₁ blocker₁ →
      ∃ t₁ l₁ b₁ t₂ l₂ b₂,
        cutoff < t₁ ∧
        TargetMacroSuccessor target tailStart t₁ l₁ b₁ t₂ l₂ b₂ ∧
        b₁ < b₂ := by
    intro blocker₁
    induction blocker₁ using Nat.strongRecOn with
    | ind blocker₁ ih =>
        intro s₁ k₁ hcutoff hinside hlow hcomb
        rcases hstream.exists_targetMacroSuccessor htail hinside hlow
            hcomb with ⟨s₂, k₂, blocker₂, hsucc⟩
        rcases hsucc.first.next_entry_below_or_blocker_lt hsucc.second
            hsucc.chronological with hentryBelow | hreset
        · have hentry₂ := hsucc.second.entry_eq_blocker_add_length
          have hdecrease : blocker₂ < blocker₁ := by omega
          have hchronological := hsucc.chronological
          have hcutoff₂ : cutoff < s₂ := by omega
          have hinside₂ : tailStart < s₂ := by omega
          exact ih blocker₂ hdecrease s₂ k₂ hcutoff₂ hinside₂
            hsucc.second_low hsucc.second
        · exact ⟨s₁, k₁, blocker₁, s₂, k₂, blocker₂,
            hcutoff, hsucc, hreset⟩
  rcases hstream.2 (max cutoff tailStart) with
    ⟨start, length, blocker, hstart, _htailStart, hlowStart, hcombStart⟩
  have hcutoffMax : cutoff ≤ max cutoff tailStart := Nat.le_max_left _ _
  have htailMax : tailStart ≤ max cutoff tailStart := Nat.le_max_right _ _
  have hcutoffStart : cutoff < start := by omega
  have hinsideStart : tailStart < start := by omega
  exact haux blocker start length hcutoffStart hinsideStart
    hlowStart hcombStart

/-- Variant with the entry interface of the reset recorded: at the produced
upward reset, the first entry additionally lies on or below the second
blocker, so the whole first fresh interval sits to the left of the new
blocker. -/
theorem UnboundedRightTerminalStream.exists_upwardReset_entry_le_after
    {target tailStart root : Nat}
    (hstream : UnboundedRightTerminalStream target tailStart root)
    (htail : MissingPermanentAboveTail target tailStart)
    (cutoff : Nat) :
    ∃ s₁ k₁ blocker₁ s₂ k₂ blocker₂,
      cutoff < s₁ ∧
      TargetMacroSuccessor target tailStart
        s₁ k₁ blocker₁ s₂ k₂ blocker₂ ∧
      blocker₁ < blocker₂ ∧
      a s₁ ≤ blocker₂ := by
  rcases hstream.exists_upwardReset_after htail cutoff with
    ⟨s₁, k₁, blocker₁, s₂, k₂, blocker₂, hcutoff, hsucc, hreset⟩
  exact ⟨s₁, k₁, blocker₁, s₂, k₂, blocker₂, hcutoff, hsucc, hreset,
    hsucc.first.upward_reset_previous_entry_le_blocker hsucc.second
      hsucc.chronological hreset⟩

/-- Sharpened global kernel of a missing permanent tail.  Either low
candidates eventually stop, leaving an eventual-high corridor, or the finite
separator root supports an unbounded right-terminal stream which performs
upward blocker resets between consecutive same-target macro episodes after
every cutoff. -/
theorem MissingPermanentAboveTail.eventualHigh_or_infinitelyManyUpwardResets
    {target tailStart : Nat}
    (htail : MissingPermanentAboveTail target tailStart) :
    EventualHighCandidateTail target tailStart ∨
      ∃ root rootFirstTime,
        target < root ∧
        FirstAt a root rootFirstTime ∧
        rootFirstTime ≤ tailStart ∧
        UnboundedRightTerminalStream target tailStart root ∧
        ∀ cutoff,
          ∃ s₁ k₁ blocker₁ s₂ k₂ blocker₂,
            cutoff < s₁ ∧
            TargetMacroSuccessor target tailStart
              s₁ k₁ blocker₁ s₂ k₂ blocker₂ ∧
            blocker₁ < blocker₂ := by
  rcases htail.eventualHigh_or_unboundedRightTerminal with
    heventual | hstream
  · exact Or.inl heventual
  · rcases hstream with
      ⟨root, rootFirstTime, htargetRoot, hrootFirst, hrootPreTail,
        hstream⟩
    exact Or.inr ⟨root, rootFirstTime, htargetRoot, hrootFirst,
      hrootPreTail, hstream,
      fun cutoff => hstream.exists_upwardReset_after htail cutoff⟩

end Recaman
