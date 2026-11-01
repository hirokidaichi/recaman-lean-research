import Recaman.TargetMacroSuccessor

namespace Recaman

/-! # The exact residual kernel of a missing permanent tail

All first occurrences after the permanent-tail boundary already have a
value-decreasing `CoverageStep`: apply the actual two-step tail dynamics at
their first-occurrence clock.  Consequently the only values which require
new global information are the finitely many first occurrences in the
pre-tail prefix.

This module connects terminal-comb escape to that finite interface.  It does
not assume semantic-branch closure or tail return, both of which are already
equivalent to target occurrence.
-/

/-- The restriction of `CoverageOracle` to first occurrences in one finite
pre-tail prefix. -/
def PreTailCoverageOracle (target tailStart : Nat) : Prop :=
  ∀ value firstTime,
    FirstAt a value firstTime →
    target ≤ value →
    firstTime ≤ tailStart →
    CoverageStep target value firstTime

/-- A missing permanent tail supplies every part of the global coverage
oracle except its finite pre-tail restriction. -/
theorem MissingPermanentAboveTail.coverageOracle_of_preTail
    {target tailStart : Nat}
    (htail : MissingPermanentAboveTail target tailStart)
    (hpre : PreTailCoverageOracle target tailStart) :
    CoverageOracle target := by
  intro value firstTime hfirst htargetValue
  by_cases hpreTime : firstTime ≤ tailStart
  · exact hpre value firstTime hfirst htargetValue hpreTime
  · have htailTime : tailStart ≤ firstTime := by omega
    have hstep := htail.coverageStep_at htailTime
    rw [hfirst.1] at hstep
    exact hstep

/-- The finite pre-tail oracle is inconsistent with the target-missing field
of the same permanent-tail certificate. -/
theorem MissingPermanentAboveTail.not_preTailCoverageOracle
    {target tailStart : Nat}
    (htail : MissingPermanentAboveTail target tailStart) :
    ¬ PreTailCoverageOracle target tailStart := by
  intro hpre
  have horacle := htail.coverageOracle_of_preTail hpre
  exact htail.target_missing (coverageOracle_implies_occurs horacle)

/-- Every above-target pre-tail root can escape through a later fresh
terminal-comb entry of smaller value.  No uniform waiting bound is required. -/
def FiniteRootTerminalEscape (target tailStart : Nat) : Prop :=
  ∀ root rootFirstTime,
    target < root →
    FirstAt a root rootFirstTime →
    rootFirstTime ≤ tailStart →
    ∃ start length blocker,
      tailStart ≤ start ∧
      HistoryTerminatedComb start length blocker ∧
      a start < root

/-- A terminal escape is exactly enough to build the finite pre-tail
coverage oracle: the comb entry is a certified first occurrence, lies above
the permanent missing target, and is strictly below the old root. -/
theorem FiniteRootTerminalEscape.toPreTailCoverageOracle
    {target tailStart : Nat}
    (htail : MissingPermanentAboveTail target tailStart)
    (hescape : FiniteRootTerminalEscape target tailStart) :
    PreTailCoverageOracle target tailStart := by
  intro value firstTime hfirst htargetValue hpreTime
  rcases Nat.eq_or_lt_of_le htargetValue with hequal | htargetValueStrict
  · subst value
    exact Or.inl ⟨firstTime, hfirst.1⟩
  · rcases hescape value firstTime htargetValueStrict hfirst hpreTime with
      ⟨start, length, blocker, htailStart, hcomb, hentryBelow⟩
    have htargetEntry : target ≤ a start :=
      Nat.le_of_lt (htail.strictly_above start htailStart)
    exact Or.inr ⟨a start, start, htargetEntry,
      hcomb.episode.entry_first, hentryBelow⟩

/-- Hence a missing permanent tail cannot have terminal escape for every
finite pre-tail root. -/
theorem MissingPermanentAboveTail.not_finiteRootTerminalEscape
    {target tailStart : Nat}
    (htail : MissingPermanentAboveTail target tailStart) :
    ¬ FiniteRootTerminalEscape target tailStart := by
  intro hescape
  exact htail.not_preTailCoverageOracle
    (hescape.toPreTailCoverageOracle htail)

/-- The exact fixed-root obstruction left by the preceding theorem.  The
root is an actual above-target first occurrence in the finite prefix, and
every terminal comb beginning in the permanent tail has entry on or to its
right. -/
def FiniteRootTerminalNoEscape (target tailStart : Nat) : Prop :=
  ∃ root rootFirstTime,
    target < root ∧
    FirstAt a root rootFirstTime ∧
    rootFirstTime ≤ tailStart ∧
    ∀ start length blocker,
      tailStart ≤ start →
      HistoryTerminatedComb start length blocker →
      root ≤ a start

/-- Every hypothetical missing permanent tail contains a fixed finite
pre-tail separator root which no later terminal-comb entry crosses. -/
theorem MissingPermanentAboveTail.exists_finiteRootTerminalNoEscape
    {target tailStart : Nat}
    (htail : MissingPermanentAboveTail target tailStart) :
    FiniteRootTerminalNoEscape target tailStart := by
  classical
  by_cases hresult : FiniteRootTerminalNoEscape target tailStart
  · exact hresult
  · have hescape : FiniteRootTerminalEscape target tailStart := by
      intro root rootFirstTime htargetRoot hfirst hpreTime
      by_cases hexists : ∃ start length blocker,
          tailStart ≤ start ∧
          HistoryTerminatedComb start length blocker ∧
          a start < root
      · exact hexists
      · have hnoEscape : ∀ start length blocker,
            tailStart ≤ start →
            HistoryTerminatedComb start length blocker →
            root ≤ a start := by
          intro start length blocker hstart hcomb
          by_cases hright : root ≤ a start
          · exact hright
          · have hentryBelow : a start < root := by omega
            exact False.elim
              (hexists ⟨start, length, blocker, hstart, hcomb,
                hentryBelow⟩)
        exact False.elim
          (hresult ⟨root, rootFirstTime, htargetRoot, hfirst,
            hpreTime, hnoEscape⟩)
    exact False.elim (htail.not_finiteRootTerminalEscape hescape)

/-- An eventual corridor in which every candidate is strictly above the
missing target.  Candidate clocks are written as `n+1` to align directly
with low-to-terminal extraction. -/
def EventualHighCandidateTail (target tailStart : Nat) : Prop :=
  ∃ cutoff,
    tailStart ≤ cutoff ∧
    ∀ n, cutoff ≤ n →
      target < nextSubtractionCandidate (n + 1)

/-- A fixed-root no-escape certificate together with an unbounded
chronological stream of completed terminal combs extracted from target-low
candidate clocks.  The universal first conjunct preserves the original
finite-root residual; the second supplies arbitrarily late same-target macro
witnesses. -/
def UnboundedRightTerminalStream (target tailStart root : Nat) : Prop :=
  (∀ start length blocker,
    tailStart ≤ start →
    HistoryTerminatedComb start length blocker →
    root ≤ a start) ∧
  ∀ cutoff,
    ∃ start length blocker,
      cutoff < start ∧
      tailStart ≤ start ∧
      nextSubtractionCandidate start < target ∧
      HistoryTerminatedComb start length blocker

/-- An unbounded target-low terminal stream supplies the next consecutive
same-target macro episode after any completed target-low comb in the strict
tail.  We choose the least later low start, then re-run maximal-comb
extraction there.  Leastness is exactly the high-between field of
`TargetMacroSuccessor`. -/
theorem UnboundedRightTerminalStream.exists_targetMacroSuccessor
    {target tailStart root s₁ k₁ blocker₁ : Nat}
    (hstream : UnboundedRightTerminalStream target tailStart root)
    (htail : MissingPermanentAboveTail target tailStart)
    (hinside : tailStart < s₁)
    (hlow₁ : nextSubtractionCandidate s₁ < target)
    (hcomb₁ : HistoryTerminatedComb s₁ k₁ blocker₁) :
    ∃ s₂ k₂ blocker₂,
      TargetMacroSuccessor target tailStart
        s₁ k₁ blocker₁ s₂ k₂ blocker₂ := by
  classical
  let finalTime := s₁ + 2 * k₁
  let IsLaterLow : Nat → Prop := fun start =>
    finalTime < start ∧ nextSubtractionCandidate start < target
  have hexists : ∃ start, IsLaterLow start := by
    rcases hstream.2 finalTime with
      ⟨start, length, blocker, hstart, _htailStart,
        hlow, _hcomb⟩
    exact ⟨start, hstart, hlow⟩
  have hleastExists : ∀ bound,
      IsLaterLow bound →
      ∃ least, IsLaterLow least ∧
        ∀ time, IsLaterLow time → least ≤ time := by
    intro bound
    induction bound using Nat.strongRecOn with
    | ind bound ih =>
        intro hbound
        by_cases hsmaller : ∃ time, time < bound ∧ IsLaterLow time
        · rcases hsmaller with ⟨time, htime, htimeLow⟩
          exact ih time htime htimeLow
        · refine ⟨bound, hbound, ?_⟩
          intro time htimeLow
          by_cases htime : time < bound
          · exact False.elim (hsmaller ⟨time, htime, htimeLow⟩)
          · omega
  rcases hexists with ⟨someStart, hsomeStart⟩
  rcases hleastExists someStart hsomeStart with
    ⟨s₂, hs₂Spec, hs₂Minimal⟩
  have hchronological : s₁ + 2 * k₁ < s₂ := by
    simpa only [IsLaterLow, finalTime] using hs₂Spec.1
  have hlow₂ : nextSubtractionCandidate s₂ < target := by
    simpa only [IsLaterLow] using hs₂Spec.2
  have hs₂Positive : 0 < s₂ := by omega
  have hclock : s₂ - 1 + 1 = s₂ := by omega
  have htailPrevious : tailStart ≤ s₂ - 1 := by omega
  have hlowPrevious :
      nextSubtractionCandidate (s₂ - 1 + 1) < target := by
    simpa only [hclock] using hlow₂
  rcases htail.candidateBelow_exists_historyTerminatedComb
      htailPrevious hlowPrevious with ⟨k₂, blocker₂, hcomb₂⟩
  have hcomb₂AtStart : HistoryTerminatedComb s₂ k₂ blocker₂ := by
    simpa only [hclock] using hcomb₂
  refine ⟨s₂, k₂, blocker₂, {
    tail := htail
    first := hcomb₁
    second := hcomb₂AtStart
    first_inside_tail := hinside
    chronological := hchronological
    first_low := hlow₁
    second_low := hlow₂
    candidate_high_between := ?_
  }⟩
  intro time hafter hbefore
  have hnotLow : ¬ nextSubtractionCandidate time < target := by
    intro hlow
    have hlater : IsLaterLow time := by
      refine ⟨?_, hlow⟩
      simpa only [finalTime] using hafter
    have hleast : s₂ ≤ time := hs₂Minimal time hlater
    omega
  exact htail.candidate_strictAbove_of_not_below hnotLow

/-- Exact global kernel of a missing permanent tail.  Either low candidates
eventually stop, leaving an eventual-high corridor, or the finite separator
root above supports arbitrarily late terminal combs entirely on its right.

This conclusion uses no semantic closure and no target-tail return
hypothesis. -/
theorem MissingPermanentAboveTail.eventualHigh_or_unboundedRightTerminal
    {target tailStart : Nat}
    (htail : MissingPermanentAboveTail target tailStart) :
    EventualHighCandidateTail target tailStart ∨
      ∃ root rootFirstTime,
        target < root ∧
        FirstAt a root rootFirstTime ∧
        rootFirstTime ≤ tailStart ∧
        UnboundedRightTerminalStream target tailStart root := by
  by_cases heventual : EventualHighCandidateTail target tailStart
  · exact Or.inl heventual
  · apply Or.inr
    rcases htail.exists_finiteRootTerminalNoEscape with
      ⟨root, rootFirstTime, htargetRoot, hrootFirst,
        hrootPreTail, hterminalRight⟩
    have hunboundedLow : ∀ cutoff, ∃ n,
        tailStart ≤ n ∧ cutoff ≤ n ∧
          nextSubtractionCandidate (n + 1) < target := by
      intro cutoff
      let bound := max tailStart cutoff
      by_cases hexists : ∃ n,
          tailStart ≤ n ∧ cutoff ≤ n ∧
            nextSubtractionCandidate (n + 1) < target
      · exact hexists
      · have hevent : EventualHighCandidateTail target tailStart := by
          refine ⟨bound, Nat.le_max_left _ _, ?_⟩
          intro n hbound
          have hnotLow :
              ¬ nextSubtractionCandidate (n + 1) < target := by
            intro hlow
            exact hexists
              ⟨n, Nat.le_trans (Nat.le_max_left _ _) hbound,
                Nat.le_trans (Nat.le_max_right _ _) hbound, hlow⟩
          exact htail.candidate_strictAbove_of_not_below hnotLow
        exact False.elim (heventual hevent)
    refine ⟨root, rootFirstTime, htargetRoot, hrootFirst,
      hrootPreTail, hterminalRight, ?_⟩
    intro cutoff
    rcases hunboundedLow cutoff with
      ⟨n, htailTime, hcutoff, hlow⟩
    rcases htail.candidateBelow_exists_historyTerminatedComb
        htailTime hlow with ⟨length, blocker, hcomb⟩
    exact ⟨n + 1, length, blocker, by omega, by omega,
      hlow, hcomb⟩

end Recaman
