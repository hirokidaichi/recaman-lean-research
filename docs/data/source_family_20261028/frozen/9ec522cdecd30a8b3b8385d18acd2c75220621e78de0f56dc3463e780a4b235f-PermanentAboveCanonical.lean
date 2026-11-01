import Recaman.PermanentAboveHistory

namespace Recaman

noncomputable section

/-! # Canonical upcrossings and a dual historical rank

Arbitrary crossing selection admits the stationary cycle from
`PermanentAboveHistory`.  This module removes that first ambiguity by taking
the least future weak upcrossing.  Independently, it reverses the completed
history budget into `seenBelowCount`, which strictly decreases when proof
search moves from a zero-budget tail horizon back to a historical point with
positive missing budget.
-/

/-- The first weak upcrossing at or after a chosen below-target start. -/
structure FirstWeakUpcrossingStep
    (target start time : Nat) : Prop where
  crossing : WeakUpcrossingStep target start time
  first : ∀ earlier, earlier < time →
    ¬ WeakUpcrossingStep target start earlier

/-- Every below-target point has a canonical first future upcrossing. -/
theorem exists_firstWeakUpcrossingStep_from_below
    {target start : Nat}
    (htarget : 0 < target)
    (hbelow : a start < target) :
    ∃ time, FirstWeakUpcrossingStep target start time := by
  have aux : ∀ bound,
      WeakUpcrossingStep target start bound →
      ∃ time, FirstWeakUpcrossingStep target start time := by
    intro bound
    induction bound using Nat.strongRecOn with
    | ind bound ih =>
        intro hbound
        by_cases hearlier : ∃ time, time < bound ∧
            WeakUpcrossingStep target start time
        · rcases hearlier with ⟨time, htime, hcrossing⟩
          exact ih time htime hcrossing
        · exact ⟨bound, {
            crossing := hbound
            first := by
              intro time htime hcrossing
              exact hearlier ⟨time, htime, hcrossing⟩
          }⟩
  rcases exists_weakUpcrossingStep_from_below htarget hbelow with
    ⟨bound, hbound⟩
  exact aux bound hbound

/-- The canonical first upcrossing is no later than any other certified
upcrossing from the same start. -/
theorem FirstWeakUpcrossingStep.time_le
    {target start firstTime otherTime : Nat}
    (hfirst : FirstWeakUpcrossingStep target start firstTime)
    (hother : WeakUpcrossingStep target start otherTime) :
    firstTime ≤ otherTime := by
  by_cases hle : firstTime ≤ otherTime
  · exact hle
  · exact False.elim (hfirst.first otherTime (by omega) hother)

/-- Hence the first upcrossing witness is unique. -/
theorem FirstWeakUpcrossingStep.unique
    {target start firstTime otherTime : Nat}
    (hfirst : FirstWeakUpcrossingStep target start firstTime)
    (hother : FirstWeakUpcrossingStep target start otherTime) :
    firstTime = otherTime := by
  have hle := hfirst.time_le hother.crossing
  have hge := hother.time_le hfirst.crossing
  omega

/-- If any upcrossing finishes by a finite horizon, the canonical first one
also finishes by that horizon. -/
theorem FirstWeakUpcrossingStep.endpoint_le_of_witness
    {target start firstTime witnessTime finish : Nat}
    (hfirst : FirstWeakUpcrossingStep target start firstTime)
    (hwitness : WeakUpcrossingStep target start witnessTime)
    (hfinish : witnessTime + 1 ≤ finish) :
    firstTime + 1 ≤ finish := by
  have hle := hfirst.time_le hwitness
  omega

/-- Number of target-smaller values already seen by a history horizon. -/
def seenBelowCount (target horizon : Nat) : Nat :=
  target - missingBelowCount target horizon

theorem seenBelowCount_le (target horizon : Nat) :
    seenBelowCount target horizon ≤ target := by
  unfold seenBelowCount
  omega

/-- Seen and missing budgets partition the finite interval below target. -/
theorem seenBelowCount_add_missingBelowCount (target horizon : Nat) :
    seenBelowCount target horizon + missingBelowCount target horizon =
      target := by
  have hbound := missingBelowCount_le target horizon
  unfold seenBelowCount
  omega

/-- The dual budget is saturated exactly when the original missing budget is
zero. -/
theorem seenBelowCount_eq_target_iff
    (target horizon : Nat) :
    seenBelowCount target horizon = target ↔
      missingBelowCount target horizon = 0 := by
  have hpartition := seenBelowCount_add_missingBelowCount target horizon
  omega

/-- Seen-below count is monotone as actual history grows. -/
theorem seenBelowCount_monotone
    {target earlier later : Nat}
    (htime : earlier ≤ later) :
    seenBelowCount target earlier ≤ seenBelowCount target later := by
  have hmissing := missingBelowCount_antitone (m := target) htime
  have hearlierBound := missingBelowCount_le target earlier
  have hlaterBound := missingBelowCount_le target later
  unfold seenBelowCount
  omega

/-- A strict missing-budget drop is exactly a strict gain in the dual seen
budget. -/
theorem seenBelowCount_strict_of_missingBelowCount_strict
    {target earlier later : Nat}
    (hstrict : missingBelowCount target later <
      missingBelowCount target earlier) :
    seenBelowCount target earlier < seenBelowCount target later := by
  have hearlierBound := missingBelowCount_le target earlier
  have hlaterBound := missingBelowCount_le target later
  unfold seenBelowCount
  omega

/-- Historical proof search first backtracks through earlier tail minima and
then enters a terminal downcross-discharge phase. -/
inductive TailHistoryPhase where
  | discharge
  | backtrack
deriving Repr, DecidableEq

def TailHistoryPhase.rank : TailHistoryPhase → Nat
  | .discharge => 0
  | .backtrack => 1

structure TailHistorySearchNode where
  historyTime : Nat
  minimumValue : Nat
  phase : TailHistoryPhase
deriving Repr, DecidableEq

def tailHistoryRank (target : Nat) (node : TailHistorySearchNode) :
    Nat × (Nat × Nat) :=
  (node.phase.rank,
    (seenBelowCount target node.historyTime, node.minimumValue))

def TailHistoryProgress (target : Nat)
    (child parent : TailHistorySearchNode) : Prop :=
  Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt)
    (tailHistoryRank target child) (tailHistoryRank target parent)

/-- The phase/seen/minimum lexicographic order is well founded. -/
theorem tailHistoryProgress_wellFounded (target : Nat) :
    WellFounded (TailHistoryProgress target) := by
  apply WellFounded.intro
  intro node
  generalize hrank : tailHistoryRank target node = rank
  have hacc := natTripleLex_wellFounded.apply rank
  induction hacc generalizing node with
  | intro rank _ ih =>
      apply Acc.intro node
      intro child hchild
      have hrelation :
          Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt)
            (tailHistoryRank target child) rank := by
        simpa [TailHistoryProgress, hrank] using hchild
      exact ih (tailHistoryRank target child) hrelation child rfl

theorem tailHistoryProgress_of_seenDrop
    {target childTime parentTime childMinimum parentMinimum : Nat}
    (hseen : seenBelowCount target childTime <
      seenBelowCount target parentTime) :
    TailHistoryProgress target
      ⟨childTime, childMinimum, .backtrack⟩
      ⟨parentTime, parentMinimum, .backtrack⟩ := by
  exact Prod.Lex.right _ (Prod.Lex.left _ _ hseen)

theorem tailHistoryProgress_of_seenLe_minimumDrop
    {target childTime parentTime childMinimum parentMinimum : Nat}
    (hseen : seenBelowCount target childTime ≤
      seenBelowCount target parentTime)
    (hminimum : childMinimum < parentMinimum) :
    TailHistoryProgress target
      ⟨childTime, childMinimum, .backtrack⟩
      ⟨parentTime, parentMinimum, .backtrack⟩ := by
  rcases Nat.eq_or_lt_of_le hseen with hequal | hstrict
  · change Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt)
      (1, (seenBelowCount target childTime, childMinimum))
      (1, (seenBelowCount target parentTime, parentMinimum))
    rw [hequal]
    exact Prod.Lex.right _ (Prod.Lex.right _ hminimum)
  · exact tailHistoryProgress_of_seenDrop hstrict

theorem tailHistoryProgress_enterDischarge
    {target childTime parentTime childMinimum parentMinimum : Nat} :
    TailHistoryProgress target
      ⟨childTime, childMinimum, .discharge⟩
      ⟨parentTime, parentMinimum, .backtrack⟩ := by
  change Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt)
    (0, (seenBelowCount target childTime, childMinimum))
    (1, (seenBelowCount target parentTime, parentMinimum))
  exact Prod.Lex.left _ _ (Nat.zero_lt_succ 0)

/-- Both constructors of the historical predecessor dichotomy are strict in
the new rank: renewed tails decrease seen/minimum lexicographically, while a
real downcross enters the lower discharge phase. -/
theorem HistoricalPredecessorOutcome.tailHistoryProgress
    {target start minimumTime predecessorFirstTime : Nat}
    (h : HistoricalPredecessorOutcome target start minimumTime
      predecessorFirstTime) :
    ∃ child,
      TailHistoryProgress target child
        ⟨predecessorFirstTime, a minimumTime, .backtrack⟩ := by
  cases h with
  | downcross downTime hstep hfirst hbefore hbudget =>
      exact ⟨⟨downTime + 1, a minimumTime, .discharge⟩,
        tailHistoryProgress_enterDischarge⟩
  | renewed_tail newMinimumTime newFirstTime htail hminimum hvalueDrop =>
      have htime : newFirstTime ≤ predecessorFirstTime :=
        Nat.le_of_lt hminimum.firstTime_before_tail
      have hseen := seenBelowCount_monotone (target := target) htime
      exact ⟨⟨newFirstTime, a newMinimumTime, .backtrack⟩,
        tailHistoryProgress_of_seenLe_minimumDrop hseen hvalueDrop⟩

/-- A combined permanent-tail obstruction strictly enters the dual-history
domain.  The selected historical predecessor has positive missing budget,
whereas the crossing horizon has budget zero, so its `seenBelowCount` is
strictly smaller. -/
theorem PermanentTailCombinedCertificate.entersTailHistory
    {target start : Nat} {parent : PhaseSearchNode}
    {minimumTime predecessorFirstTime : Nat}
    (h : PermanentTailCombinedCertificate target start parent minimumTime
      predecessorFirstTime) :
    ∃ tailStart historicalMinimumTime historicalFirstTime downTime,
      MissingStrictAboveTail target tailStart ∧
      PermanentTailMinimumCertificate target tailStart
        historicalMinimumTime historicalFirstTime ∧
      FutureDowncrossStep target historicalFirstTime downTime ∧
      TailHistoryProgress target
        ⟨historicalFirstTime, a historicalMinimumTime, .backtrack⟩
        ⟨parent.horizon, a historicalMinimumTime, .backtrack⟩ := by
  rcases h.tail.exists_historicalDowncrossCertificate with
    ⟨tailStart, historicalMinimumTime, historicalFirstTime, downTime,
      htailStart, htail, hminimum, hdown, hfirst, hbefore, hbudget⟩
  have hhistoricalPositive :
      0 < missingBelowCount target historicalFirstTime := by
    omega
  have hmissingDrop :
      missingBelowCount target parent.horizon <
        missingBelowCount target historicalFirstTime := by
    rw [h.crossing.budget_zero]
    exact hhistoricalPositive
  have hseenDrop := seenBelowCount_strict_of_missingBelowCount_strict
    hmissingDrop
  exact ⟨tailStart, historicalMinimumTime, historicalFirstTime, downTime,
    htail, hminimum, hdown,
    tailHistoryProgress_of_seenDrop hseenDrop⟩

/-- The earliest-upcrossing rule is constructible on the historical cycle
and finishes before the renewed strict tail starts. -/
theorem MissingPermanentAboveTail.exists_firstHistoricalUpcrossing
    {target start : Nat}
    (h : MissingPermanentAboveTail target start) :
    ∃ tailStart historicalFirstTime downTime crossingTime,
      MissingStrictAboveTail target tailStart ∧
      FutureDowncrossStep target historicalFirstTime downTime ∧
      FirstWeakUpcrossingStep target (downTime + 1) crossingTime ∧
      crossingTime + 1 ≤ tailStart := by
  rcases h.exists_historicalDowncrossCertificate with
    ⟨tailStart, minimumTime, historicalFirstTime, downTime,
      htailStart, htail, hminimum, hdown, hdownFirst, hdownBefore,
      hbudget⟩
  rcases exists_firstWeakUpcrossingStep_from_below h.target_positive
      hdown.endpoint_below with ⟨crossingTime, hfirst⟩
  have htailAbove := htail.strictly_above tailStart (Nat.le_refl _)
  rcases exists_weakUpcrossingStep_between
      (Nat.le_of_lt hdownBefore) hdown.endpoint_below
      (Nat.le_of_lt htailAbove) with
    ⟨witnessTime, hwitness, hwitnessBound⟩
  have hfirstBound := hfirst.endpoint_le_of_witness hwitness hwitnessBound
  exact ⟨tailStart, historicalFirstTime, downTime, crossingTime,
    htail, hdown, hfirst, hfirstBound⟩

/-- Earliest selection removes witness ambiguity but not stationarity: a
second earliest selection from the same historical downcross endpoint must
return the identical crossing time. -/
theorem firstHistoricalUpcrossing_reselection_stationary
    {target start firstTime secondTime : Nat}
    (hfirst : FirstWeakUpcrossingStep target start firstTime)
    (hsecond : FirstWeakUpcrossingStep target start secondTime) :
    secondTime = firstTime :=
  (hsecond.unique hfirst)

end

end Recaman
