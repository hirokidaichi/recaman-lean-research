import Recaman.TargetCandidateTransitions
import Recaman.DebtInvariant

namespace Recaman

/-! # Macro provenance of completed comb blockers

The interval-order dichotomy leaves an exceptional upward-reset branch.  To
make that branch explicit, classify the transition which first created the
new terminal blocker.  A subtraction origin is not free: its predecessor is
an older value strictly above the entire fresh comb interval.  The remaining
branch is a forced-addition origin.
-/

/-- Any positive first-occurrence clock used by a blocker provenance lies
either in the finite pre-tail prefix, or has a predecessor already strictly
above the missing target.  In the forced-addition branch of
`PositiveTerminalBlockerOrigin`, the second case is the target-bounded
`EarlierSmaller` child needed by the existing debt recursion. -/
theorem MissingPermanentAboveTail.birthTime_le_start_or_predecessor_above
    {target start birthTime : Nat}
    (h : MissingPermanentAboveTail target start)
    (hpositive : 0 < birthTime) :
    birthTime ≤ start ∨ target < a (birthTime - 1) := by
  by_cases hpreTail : birthTime ≤ start
  · exact Or.inl hpreTail
  · exact Or.inr (h.strictly_above (birthTime - 1) (by omega))

/-- Exact provenance split for a positive terminal blocker. -/
inductive PositiveTerminalBlockerOrigin
    {s k blocker : Nat} (h : HistoryTerminatedComb s k blocker) : Prop
  | legal_subtraction
      (firstTime : Nat)
      (firstTime_lt_entry : firstTime < s)
      (first : FirstAt a blocker firstTime)
      (legal : CanSubtract firstTime (stateAt (firstTime - 1)))
      (blocker_eq_subtraction :
        blocker = a (firstTime - 1) - firstTime)
      (predecessorFirstTime : Nat)
      (predecessor_first :
        FirstAt a (a (firstTime - 1)) predecessorFirstTime)
      (predecessorFirstTime_lt : predecessorFirstTime < firstTime)
      (predecessor_above_entry : a s < a (firstTime - 1)) :
      PositiveTerminalBlockerOrigin h
  | forced_addition
      (firstTime : Nat)
      (firstTime_lt_entry : firstTime < s)
      (first : FirstAt a blocker firstTime)
      (forced : ¬ CanSubtract firstTime (stateAt (firstTime - 1)))
      (blocker_eq_addition :
        blocker = a (firstTime - 1) + firstTime)
      (predecessorFirstTime : Nat)
      (predecessor_first :
        FirstAt a (a (firstTime - 1)) predecessorFirstTime)
      (predecessorFirstTime_lt : predecessorFirstTime < firstTime)
      (predecessor_lt_blocker : a (firstTime - 1) < blocker) :
      PositiveTerminalBlockerOrigin h

/-- Every positive terminal blocker has the provenance split above.  In the
subtraction branch freshness of the comb supplies the strict lift beyond its
entry value. -/
theorem HistoryTerminatedComb.positive_blocker_origin
    {s k blocker : Nat}
    (h : HistoryTerminatedComb s k blocker)
    (hpositive : 0 < blocker) :
    PositiveTerminalBlockerOrigin h := by
  rcases h.blocker_has_firstAt_before_entry with
    ⟨firstTime, hfirstTime, hfirst⟩
  have hfirstPositive : 0 < firstTime := by
    by_cases hzero : firstTime = 0
    · subst firstTime
      have hzeroValue := firstAt_time_zero_value hfirst
      omega
    · omega
  have hclock : firstTime - 1 + 1 = firstTime := by omega
  have hfirst' : FirstAt a blocker (firstTime - 1 + 1) := by
    simpa only [hclock] using hfirst
  rcases firstAt_succ_transition hfirst' with hlegal | hforced
  · rcases hlegal with ⟨hcan, hvalue⟩
    have hcan' : CanSubtract firstTime
        (stateAt (firstTime - 1)) := by
      simpa only [hclock] using hcan
    have hvalue' : blocker = a (firstTime - 1) - firstTime := by
      simpa only [hclock] using hvalue
    rcases history_member_has_firstAt
        (current_mem_valuesThrough (firstTime - 1)) with
      ⟨predecessorFirstTime, hpredecessorTimeLe, hpredecessorFirst⟩
    have hpredecessorTime : predecessorFirstTime < firstTime := by omega
    exact .legal_subtraction firstTime hfirstTime hfirst hcan' hvalue'
      predecessorFirstTime hpredecessorFirst hpredecessorTime
      (h.subtraction_origin_predecessor_above_entry
        hfirst hfirstTime hfirstPositive hcan')
  · rcases hforced with ⟨hnot, hvalue⟩
    have hnot' : ¬ CanSubtract firstTime
        (stateAt (firstTime - 1)) := by
      simpa only [hclock] using hnot
    have hvalue' : blocker = a (firstTime - 1) + firstTime := by
      simpa only [hclock] using hvalue
    rcases history_member_has_firstAt
        (current_mem_valuesThrough (firstTime - 1)) with
      ⟨predecessorFirstTime, hpredecessorTimeLe, hpredecessorFirst⟩
    have hpredecessorTime : predecessorFirstTime < firstTime := by omega
    have hpredecessorLt : a (firstTime - 1) < blocker := by omega
    exact .forced_addition firstTime hfirstTime hfirst hnot' hvalue'
      predecessorFirstTime hpredecessorFirst hpredecessorTime hpredecessorLt

/-- Rank-facing form of the origin split.  A forced-addition origin is an
actual edge of the existing `EarlierSmaller` order.  The only residual is a
legal-subtraction origin: its first time decreases, but its value lifts above
the comb entry. -/
theorem PositiveTerminalBlockerOrigin.earlierSmaller_or_lift
    {s k blocker : Nat} {h : HistoryTerminatedComb s k blocker}
    (horigin : PositiveTerminalBlockerOrigin h) :
    (∃ firstTime predecessorFirstTime,
      FirstAt a blocker firstTime ∧
      FirstAt a (a (firstTime - 1)) predecessorFirstTime ∧
      EarlierSmaller
        ⟨a (firstTime - 1), predecessorFirstTime⟩
        ⟨blocker, firstTime⟩) ∨
    (∃ firstTime predecessorFirstTime,
      firstTime < s ∧
      FirstAt a blocker firstTime ∧
      CanSubtract firstTime (stateAt (firstTime - 1)) ∧
      FirstAt a (a (firstTime - 1)) predecessorFirstTime ∧
      predecessorFirstTime < firstTime ∧
      a s < a (firstTime - 1)) := by
  cases horigin with
  | legal_subtraction firstTime htime hfirst hlegal _
      predecessorFirstTime hpredecessorFirst hpredecessorTime habove =>
      exact Or.inr ⟨firstTime, predecessorFirstTime, htime, hfirst,
        hlegal, hpredecessorFirst, hpredecessorTime, habove⟩
  | forced_addition firstTime _ hfirst _ _ predecessorFirstTime
      hpredecessorFirst hpredecessorTime hpredecessorLt =>
      exact Or.inl ⟨firstTime, predecessorFirstTime, hfirst,
        hpredecessorFirst, ⟨hpredecessorLt, hpredecessorTime⟩⟩

/-- Tail-aware routing of blocker provenance.  A forced-addition birth is
either confined to the finite pre-tail prefix or yields an `EarlierSmaller`
child whose value is still strictly above the missing target.  The sole
remaining branch is the existing subtraction-origin lift above the fresh
comb entry. -/
theorem PositiveTerminalBlockerOrigin.preTail_or_targetEarlierSmaller_or_lift
    {target tailStart s k blocker : Nat}
    {hcomb : HistoryTerminatedComb s k blocker}
    (htail : MissingPermanentAboveTail target tailStart)
    (horigin : PositiveTerminalBlockerOrigin hcomb) :
    (exists firstTime predecessorFirstTime,
      firstTime ≤ tailStart ∧
      FirstAt a blocker firstTime ∧
      FirstAt a (a (firstTime - 1)) predecessorFirstTime) ∨
    (exists firstTime predecessorFirstTime,
      target < a (firstTime - 1) ∧
      FirstAt a blocker firstTime ∧
      FirstAt a (a (firstTime - 1)) predecessorFirstTime ∧
      EarlierSmaller
        ⟨a (firstTime - 1), predecessorFirstTime⟩
        ⟨blocker, firstTime⟩) ∨
    (exists firstTime predecessorFirstTime,
      firstTime < s ∧
      FirstAt a blocker firstTime ∧
      CanSubtract firstTime (stateAt (firstTime - 1)) ∧
      FirstAt a (a (firstTime - 1)) predecessorFirstTime ∧
      predecessorFirstTime < firstTime ∧
      a s < a (firstTime - 1)) := by
  cases horigin with
  | legal_subtraction firstTime htime hfirst hlegal _
      predecessorFirstTime hpredecessorFirst hpredecessorTime habove =>
      exact Or.inr (Or.inr ⟨firstTime, predecessorFirstTime, htime,
        hfirst, hlegal, hpredecessorFirst, hpredecessorTime, habove⟩)
  | forced_addition firstTime _ hfirst _ _ predecessorFirstTime
      hpredecessorFirst hpredecessorTime hpredecessorLt =>
      have hpositive : 0 < firstTime := by omega
      rcases htail.birthTime_le_start_or_predecessor_above hpositive with
        hpreTail | haboveTarget
      · exact Or.inl ⟨firstTime, predecessorFirstTime, hpreTail,
          hfirst, hpredecessorFirst⟩
      · exact Or.inr (Or.inl ⟨firstTime, predecessorFirstTime,
          haboveTarget, hfirst, hpredecessorFirst,
          ⟨hpredecessorLt, hpredecessorTime⟩⟩)

/-- A strict upward reset therefore has only two explanations: an older
predecessor above the new entry, or a forced-addition origin. -/
theorem HistoryTerminatedComb.upward_reset_origin
    {s₁ k₁ blocker₁ s₂ k₂ blocker₂ : Nat}
    (_h₁ : HistoryTerminatedComb s₁ k₁ blocker₁)
    (h₂ : HistoryTerminatedComb s₂ k₂ blocker₂)
    (hreset : blocker₁ < blocker₂) :
    PositiveTerminalBlockerOrigin h₂ :=
  h₂.positive_blocker_origin (Nat.lt_of_le_of_lt (Nat.zero_le _) hreset)

end Recaman
