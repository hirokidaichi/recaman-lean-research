import Recaman.LeastTailLedgerMinimum
import Recaman.PermanentAboveCycleRank

namespace Recaman

/-! # Provenance of the low-quotient tail blocker

For a general strict tail, the unbounded `q = 1` branch at a tail minimum
remembers an earlier occurrence of `r - 1`.  This file records two
consequences of that provenance.  First, the two ledger identities give an
exact interval payment equation and rule out a blocker in the last two
steps.  Second, the earlier occurrence enters the existing historical-tail
dichotomy, and hence the well-founded tail-cycle rank.

These general provenance theorems are intended for noncanonical renewed
tails, where the completed below-target coverage need not be available at
the new start.  The canonical witness extracted directly from a
`LeastMissingTarget` satisfies a stronger height bound; the final theorem
shows that its high-blocker branch is empty.
-/

/-- Exact ledger balance on any time interval.  This is the additive form
which avoids truncated subtraction of orbit values. -/
theorem ledger_interval_balance {earlier later : Nat}
    (htime : earlier ≤ later) :
    a later + 2 * (subSum later - subSum earlier) + upperTri earlier =
      a earlier + upperTri later := by
  have hearlier := ledger_identity earlier
  have hlater := ledger_identity later
  have hmono := subSum_mono htime
  omega

/-- Sharp `C = 3` payment for one positive earlier occurrence.  If a later
value exceeds a positive earlier value by exactly the later clock plus one,
then at least three clocks separate the occurrences, the intervening
subtraction ledger has an exact payment equation, and that single job is
paid with additive slack three.

This is deliberately a one-job statement.  It does not control overlap
between the ledger intervals of several blockers, and therefore does not
prove the aggregate Hall inequality. -/
theorem positiveEarlierOccurrence_sharpC3
    {earlier time : Nat}
    (hpositive : 0 < a earlier)
    (hbefore : earlier < time)
    (hincrease : a time = a earlier + (time + 1)) :
    earlier + 3 ≤ time ∧
      2 * (subSum time - subSum earlier) + (time + 1) +
          upperTri earlier = upperTri time ∧
      time + 1 ≤ (subSum time - subSum earlier) + 3 := by
  have hledgerEarlier := ledger_identity earlier
  have hledgerTime := ledger_identity time
  have hsubMono := subSum_mono (Nat.le_of_lt hbefore)
  have hpayment :
      2 * (subSum time - subSum earlier) + (time + 1) +
          upperTri earlier = upperTri time := by
    omega
  have hearlierPositive : 0 < earlier := by
    by_cases hearlier : 0 < earlier
    · exact hearlier
    · have hearlierZero : earlier = 0 := by omega
      rw [hearlierZero] at hpositive
      have hbase : a 0 = 0 := rfl
      omega
  have hgapOne : earlier + 1 < time := by
    by_cases hstrict : earlier + 1 < time
    · exact hstrict
    · have htimeEq : time = earlier + 1 := by omega
      have htri := upperTri_succ earlier
      rw [htimeEq] at hpayment
      omega
  have hgapThree : earlier + 3 ≤ time := by
    by_cases hthree : earlier + 3 ≤ time
    · exact hthree
    · have htimeEq : time = earlier + 2 := by omega
      rw [htimeEq] at hincrease
      have hincreaseTwo :
          a ((earlier + 1) + 1) = a earlier + (earlier + 3) := by
        simpa [Nat.add_assoc] using hincrease
      by_cases hfirstCan : CanSubtract (earlier + 1) (stateAt earlier)
      · have hfirstStep := a_succ_of_canSubtract hfirstCan
        have hfirstPositive : earlier + 1 < a earlier := by
          simpa [a] using hfirstCan.1
        by_cases hsecondCan :
            CanSubtract ((earlier + 1) + 1) (stateAt (earlier + 1))
        · have hsecondStep := a_succ_of_canSubtract hsecondCan
          have hsecondPositive :
              (earlier + 1) + 1 < a (earlier + 1) := by
            simpa [a] using hsecondCan.1
          omega
        · have hsecondStep := a_succ_of_not_canSubtract hsecondCan
          omega
      · have hfirstStep := a_succ_of_not_canSubtract hfirstCan
        by_cases hsecondCan :
            CanSubtract ((earlier + 1) + 1) (stateAt (earlier + 1))
        · have hsecondStep := a_succ_of_canSubtract hsecondCan
          have hsecondPositive :
              (earlier + 1) + 1 < a (earlier + 1) := by
            simpa [a] using hsecondCan.1
          omega
        · have hsecondStep := a_succ_of_not_canSubtract hsecondCan
          omega
  let base := time - 3
  have hbaseTime : base + 3 = time := by
    simp only [base]
    omega
  have hearlierBase : earlier ≤ base := by
    simp only [base]
    omega
  have htriMono := upperTri_mono hearlierBase
  have htriOne :
      upperTri (base + 1) = upperTri base + (base + 1) := by
    have h := upperTri_succ base
    omega
  have htriTwo :
      upperTri (base + 2) = upperTri (base + 1) + (base + 2) := by
    have h := upperTri_succ (base + 1)
    simpa [Nat.add_assoc] using h
  have htriThree :
      upperTri (base + 3) = upperTri (base + 2) + (base + 3) := by
    have h := upperTri_succ (base + 2)
    simpa [Nat.add_assoc] using h
  have htriLastThree :
      upperTri time = upperTri base + (3 * time - 3) := by
    rw [← hbaseTime]
    omega
  have htriGap :
      upperTri earlier + (3 * time - 3) ≤ upperTri time := by
    omega
  have hsharp :
      time + 1 ≤ (subSum time - subSum earlier) + 3 := by
    omega
  exact ⟨hgapThree, hpayment, hsharp⟩

/-- If `a time = time + r` while the earlier blocker has value `r - 1`, the
value increase is exactly `time + 1`.  The subtraction ledger therefore pays
the remaining triangular growth exactly.  The last one or two Recamán steps
cannot realize that increase, so the blocker occurs at least three clocks
earlier. -/
theorem CoordinatesAt.qOne_earlierBlocker_ledgerPayment
    {time r blockerTime : Nat}
    (hcoordinates : CoordinatesAt time 1 r)
    (hblockerPositive : 0 < r - 1)
    (hblocker : FirstAt a (r - 1) blockerTime)
    (hbefore : blockerTime < time) :
    blockerTime + 3 ≤ time ∧
      subSum blockerTime ≤ subSum time ∧
      2 * (subSum time - subSum blockerTime) + (time + 1) +
          upperTri blockerTime = upperTri time := by
  have htimeValue := hcoordinates.eqn
  have hblockerValue := hblocker.1
  have hvalueIncrease :
      a time = a blockerTime + (time + 1) := by
    omega
  have hblockerValuePositive : 0 < a blockerTime := by
    rw [hblockerValue]
    exact hblockerPositive
  have hsubMono := subSum_mono (Nat.le_of_lt hbefore)
  rcases positiveEarlierOccurrence_sharpC3 hblockerValuePositive hbefore
      hvalueIncrease with ⟨hgapThree, hpayment, hsharp⟩
  exact ⟨hgapThree, hsubMono, hpayment⟩

/-- Any earlier first occurrence at or above the missing target and below a
reference minimum has the same reusable provenance as the predecessor stored
in a permanent-tail minimum certificate.  A future downcross gives a strict
history-budget drop; if no downcross exists, the first occurrence starts a
new strict tail whose certified minimum is strictly smaller. -/
theorem historicalAboveBlockerOutcome
    {target start referenceTime value blockerTime : Nat}
    (htail : MissingStrictAboveTail target start)
    (hblocker : FirstAt a value blockerTime)
    (htargetValue : target ≤ value)
    (hvalueDrop : value < a referenceTime) :
    HistoricalPredecessorOutcome target start referenceTime blockerTime := by
  have htargetAtBlocker : target < a blockerTime := by
    have hvalueAtBlocker := hblocker.1
    have hne : value ≠ target := by
      intro hequal
      exact htail.target_missing ⟨blockerTime,
        hvalueAtBlocker.trans hequal⟩
    omega
  by_cases hdown : ∃ downTime,
      FutureDowncrossStep target blockerTime downTime
  · rcases hdown with ⟨downTime, hstep⟩
    have hcan : CanSubtract (downTime + 1) (stateAt downTime) := by
      by_cases hcan : CanSubtract (downTime + 1) (stateAt downTime)
      · exact hcan
      · have hadd := a_succ_of_not_canSubtract hcan
        have hsource := hstep.start_at_or_above
        have hendpoint := hstep.endpoint_below
        omega
    have hfirst := firstAt_succ_of_canSubtract hcan
    have hbeforeTail : downTime + 1 < start := by
      by_cases hbefore : downTime + 1 < start
      · exact hbefore
      · have habove := htail.strictly_above (downTime + 1)
          (Nat.le_of_not_gt hbefore)
        exact False.elim (by
          have hbelow := hstep.endpoint_below
          omega)
    exact .downcross downTime hstep hfirst hbeforeTail
      hstep.strict_budget_drop
  · have hatOrAbove : ∀ later, blockerTime ≤ later → target ≤ a later :=
      (no_futureDowncross_iff_tail_atOrAbove
        (Nat.le_of_lt htargetAtBlocker)).mp hdown
    have hrenewed : MissingStrictAboveTail target blockerTime := {
      target_positive := htail.target_positive
      target_missing := htail.target_missing
      strictly_above := by
        intro later hlater
        have hle := hatOrAbove later hlater
        have hne : target ≠ a later := by
          intro hequal
          exact htail.target_missing ⟨later, hequal.symm⟩
        exact Nat.lt_of_le_of_ne hle hne
    }
    rcases hrenewed.exists_minimumCertificate with
      ⟨newMinimumTime, newFirstTime, hminimum⟩
    have hnewLe := hminimum.minimum.minimal blockerTime (Nat.le_refl _)
    have hvalueAtBlocker := hblocker.1
    have hminimumDrop : a newMinimumTime < a referenceTime := by
      omega
    exact .renewed_tail newMinimumTime newFirstTime hrenewed hminimum
      hminimumDrop

/-- Strengthening of the low-quotient blocker alternative for a general,
possibly renewed noncanonical tail: its earlier provenance carries both the
exact ledger payment and a reusable historical outcome. -/
theorem PermanentTailMinimumCertificate.lowQuotient_bounded_or_provenance
    {target start time firstTime q r : Nat}
    (htail : MissingStrictAboveTail target start)
    (hminimum : PermanentTailMinimumCertificate
      target start time firstTime)
    (hcoordinates : CoordinatesAt time q r)
    (hquotient : q ≤ 1) :
    a time ≤ time + target ∨
      ∃ blockerTime,
        q = 1 ∧
        FirstAt a (r - 1) blockerTime ∧
        blockerTime < start ∧
        blockerTime + 3 ≤ time ∧
        target ≤ r - 1 ∧
        r - 1 < a time ∧
        subSum blockerTime ≤ subSum time ∧
        2 * (subSum time - subSum blockerTime) + (time + 1) +
            upperTri blockerTime = upperTri time ∧
        HistoricalPredecessorOutcome target start time blockerTime := by
  rcases hminimum.lowQuotient_bounded_or_earlierBlocker
      htail.target_positive hcoordinates hquotient with
    hbounded | ⟨blockerTime, hq, hblocker, hbefore,
      htargetBlocker, hvalueDrop⟩
  · exact Or.inl hbounded
  · have hblockerPositive : 0 < r - 1 := by
      have htargetPos := htail.target_positive
      omega
    have hcoordinatesOne : CoordinatesAt time 1 r := by
      simpa [hq] using hcoordinates
    rcases hcoordinatesOne.qOne_earlierBlocker_ledgerPayment
        hblockerPositive hblocker
        hbefore with ⟨hgap, hsubMono, hpayment⟩
    have hbeforeStart : blockerTime < start := by
      by_cases hbeforeStart : blockerTime < start
      · exact hbeforeStart
      · have hminimumLe := hminimum.minimum.minimal blockerTime
          (Nat.le_of_not_gt hbeforeStart)
        have hblockerValue := hblocker.1
        omega
    have houtcome := historicalAboveBlockerOutcome htail hblocker
      htargetBlocker hvalueDrop
    exact Or.inr ⟨blockerTime, hq, hblocker, hbeforeStart, hgap,
      htargetBlocker,
      hvalueDrop, hsubMono, hpayment, houtcome⟩

/-- The provenance alternative is immediately a strict step in the existing
well-founded tail-cycle rank, at any fixed outer anchor. -/
theorem PermanentTailMinimumCertificate.lowQuotient_bounded_or_cycleProgress
    {target start time firstTime q r anchor : Nat}
    (htail : MissingStrictAboveTail target start)
    (hminimum : PermanentTailMinimumCertificate
      target start time firstTime)
    (hcoordinates : CoordinatesAt time q r)
    (hquotient : q ≤ 1) :
    a time ≤ time + target ∨
      ∃ blockerTime child,
        q = 1 ∧
        FirstAt a (r - 1) blockerTime ∧
        blockerTime < start ∧
        blockerTime + 3 ≤ time ∧
        2 * (subSum time - subSum blockerTime) + (time + 1) +
            upperTri blockerTime = upperTri time ∧
        TailCycleProgress target child
          ⟨anchor, .backtrack, blockerTime, a time⟩ := by
  rcases hminimum.lowQuotient_bounded_or_provenance htail hcoordinates
      hquotient with
    hbounded | ⟨blockerTime, hq, hblocker, hbeforeStart, hgap,
      htargetBlocker, hvalueDrop, hsubMono, hpayment, houtcome⟩
  · exact Or.inl hbounded
  · rcases houtcome.tailCycleProgress (anchor := anchor) with
      ⟨child, hprogress⟩
    exact Or.inr ⟨blockerTime, child, hq, hblocker, hbeforeStart, hgap,
      hpayment, hprogress⟩

/-- At the least valid tail start, the renewed-tail constructor of the
provenance outcome is impossible: it would start a valid strict tail at the
strictly earlier blocker time.  Hence the unbounded low-quotient branch
actually produces a finite downcross and a strict history-budget drop, while
retaining the exact ledger payment. -/
theorem PermanentTailMinimumCertificate.lowQuotient_bounded_or_leastTailDowncross
    {target start time firstTime q r : Nat}
    (htail : MissingStrictAboveTail target start)
    (hleast : ∀ other, MissingStrictAboveTail target other → start ≤ other)
    (hminimum : PermanentTailMinimumCertificate
      target start time firstTime)
    (hcoordinates : CoordinatesAt time q r)
    (hquotient : q ≤ 1) :
    a time ≤ time + target ∨
      ∃ blockerTime downTime,
        q = 1 ∧
        FirstAt a (r - 1) blockerTime ∧
        blockerTime < start ∧
        blockerTime + 3 ≤ time ∧
        target < r - 1 ∧
        r - 1 < a time ∧
        2 * (subSum time - subSum blockerTime) + (time + 1) +
            upperTri blockerTime = upperTri time ∧
        blockerTime < start - 1 ∧
        a (start - 1) < target ∧
        a (start - 1) +
            2 * (subSum (start - 1) - subSum blockerTime) +
            upperTri blockerTime =
          (r - 1) + upperTri (start - 1) ∧
        FutureDowncrossStep target blockerTime downTime ∧
        FirstAt a (a (downTime + 1)) (downTime + 1) ∧
        downTime + 1 < start ∧
        missingBelowCount target (downTime + 1) <
          missingBelowCount target blockerTime := by
  rcases hminimum.lowQuotient_bounded_or_provenance htail hcoordinates
      hquotient with
    hbounded | ⟨blockerTime, hq, hblocker, hbeforeStart, hgap,
      htargetBlocker, hvalueDrop, hsubMono, hpayment, houtcome⟩
  · exact Or.inl hbounded
  · cases houtcome with
    | downcross downTime hstep hfirst hbeforeTail hbudget =>
        have htargetStrict : target < r - 1 := by
          by_cases hequal : target = r - 1
          · have hblockerValue := hblocker.1
            exact False.elim
              (htail.target_missing ⟨blockerTime,
                hblockerValue.trans hequal.symm⟩)
          · omega
        have hcanonicalBelow :=
          least_predecessor_below_target htail hleast
        have hbeforePredecessor : blockerTime < start - 1 := by
          by_cases hstrict : blockerTime < start - 1
          · exact hstrict
          · have hequal : blockerTime = start - 1 := by omega
            have hblockerValue := hblocker.1
            rw [hequal] at hblockerValue
            omega
        have hprefixLedger := ledger_interval_balance
          (Nat.le_of_lt hbeforePredecessor)
        have hblockerValue := hblocker.1
        exact Or.inr ⟨blockerTime, downTime, hq, hblocker,
          hbeforeStart, hgap, htargetStrict, hvalueDrop, hpayment,
          hbeforePredecessor, hcanonicalBelow, by omega,
          hstep, hfirst, hbeforeTail, hbudget⟩
    | renewed_tail newMinimumTime newFirstTime hrenewed hnewMinimum
        hminimumDrop =>
        have hleastLe := hleast blockerTime hrenewed
        exact False.elim (by omega)

/-- The canonical least-missing witness never enters the high-blocker branch.
Its start-to-minimum height bound and `start ≤ time` give
`a time < time + target`; hence the only possible coordinates are `q = 0`,
or `q = 1` with remainder strictly below the target. -/
theorem LeastMissingTarget.exists_leastTailLedgerMinimum_lowCoordinates
    {target : Nat} (h : LeastMissingTarget target) :
    ∃ start time firstTime q r,
      MissingStrictAboveTail target start ∧
      (∀ other, MissingStrictAboveTail target other → start ≤ other) ∧
      PermanentTailMinimumCertificate target start time firstTime ∧
      CoordinatesAt time q r ∧
      a time + 1 ≤ target + start ∧
      a time < time + target ∧
      (q = 0 ∨ (q = 1 ∧ r < target)) := by
  rcases h.exists_leastTailLedgerMinimum with
    ⟨start, time, firstTime, q, r, htail, hleast, hminimum,
      hcoordinates, htargetMinimum, hminimumUpper, hminimumTwice,
      hquotient, hpotential, hledgerLower, hledgerUpper⟩
  have hstartTime := hminimum.minimum.start_le_time
  have hstrictHeight : a time < time + target := by
    omega
  have hcases : q = 0 ∨ q = 1 := by omega
  have hlowCoordinates : q = 0 ∨ (q = 1 ∧ r < target) := by
    rcases hcases with hzero | hone
    · exact Or.inl hzero
    · subst q
      refine Or.inr ⟨rfl, ?_⟩
      have hequation := hcoordinates.eqn
      simp at hequation
      omega
  exact ⟨start, time, firstTime, q, r, htail, hleast, hminimum,
    hcoordinates, hminimumUpper, hstrictHeight, hlowCoordinates⟩

end Recaman
