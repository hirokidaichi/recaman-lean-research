import Recaman.TargetCombSemanticMount
import Recaman.SubtractionLedger

namespace Recaman

/-! # Clock constraints on the abstract right-moving comb ladder

The Round 10 interval countermodel forgets the actual transitions between
terminal fresh intervals.  A real history-terminated comb launches two
forced additions after its final low landing.  Moreover a target-low entry
inside a permanent tail was created by legal subtraction.  These facts give
an exact clock gap for the smallest, singleton version of the right ladder.
-/

/-- A target-low entry inside the permanent tail is not merely fresh: its
incoming transition is the legal subtraction which creates it. -/
theorem MissingPermanentAboveTail.candidateBelow_entry_legal
    {target tailStart n : Nat}
    (htail : MissingPermanentAboveTail target tailStart)
    (htime : tailStart ≤ n)
    (hlow : nextSubtractionCandidate (n + 1) < target) :
    CanSubtract (n + 1) (stateAt n) := by
  by_cases hcan : CanSubtract (n + 1) (stateAt n)
  · exact hcan
  · have hhigh := htail.forcedAddition_candidate_strictAbove htime hcan
    exact False.elim ((Nat.not_lt_of_ge (Nat.le_of_lt hhigh)) hlow)

/-- Exact two-addition launch after the final low landing of a completed
comb.  The second addition is forced by the historical terminal blocker. -/
theorem HistoryTerminatedComb.two_forced_launch
    {s k blocker : Nat}
    (hcomb : HistoryTerminatedComb s k blocker) :
    let finalTime := s + 2 * k
    ¬ CanSubtract (finalTime + 1) (stateAt finalTime) ∧
      ¬ CanSubtract (finalTime + 2) (stateAt (finalTime + 1)) ∧
      a (finalTime + 1) = blocker + finalTime + 2 ∧
      a (finalTime + 2) = blocker + 2 * finalTime + 4 := by
  dsimp only
  have hforced₁ := hcomb.final_forced
  have hforced₂ := hcomb.repayment_forced
  have hvalue₁ := a_succ_of_not_canSubtract hforced₁
  have hvalue₂ := a_succ_of_not_canSubtract hforced₂
  have hfinal := hcomb.blocker_eq
  have hvalue₁' : a (s + 2 * k + 1) =
      a (s + 2 * k) + (s + 2 * k + 1) := by
    simpa [Nat.add_assoc] using hvalue₁
  have hvalue₂' : a (s + 2 * k + 2) =
      a (s + 2 * k + 1) + (s + 2 * k + 2) := by
    simpa [Nat.add_assoc] using hvalue₂
  exact ⟨hforced₁, hforced₂, by omega, by omega⟩

/-- The singleton right-ladder edge cannot be packed immediately after the
two forced terminal additions.  If a later legal subtraction creates the
fresh successor `blocker+2`, its clock is at least four after the singleton
entry (assuming the noninitial range). -/
theorem HistoryTerminatedComb.singleton_unitLadder_gap_four
    {s blocker nextTime : Nat}
    (hcomb : HistoryTerminatedComb s 0 blocker)
    (hnoninitial : 1 < s)
    (hlater : s < nextTime)
    (hlegal : CanSubtract nextTime (stateAt (nextTime - 1)))
    (hnextEntry : a nextTime = blocker + 2) :
    s + 4 ≤ nextTime := by
  rcases hcomb.two_forced_launch with
    ⟨hforced₁, hforced₂, _hvalue₁, hvalue₂⟩
  by_cases hgap : s + 4 ≤ nextTime
  · exact hgap
  · exfalso
    have hcases : nextTime = s + 1 ∨ nextTime = s + 2 ∨
        nextTime = s + 3 := by omega
    rcases hcases with htime | htime | htime
    · subst nextTime
      simpa using hforced₁ hlegal
    · subst nextTime
      simpa using hforced₂ hlegal
    · subst nextTime
      have hlegal' : CanSubtract (s + 3) (stateAt (s + 2)) := by
        simpa using hlegal
      have hstep := a_succ_of_canSubtract hlegal'
      have hvalue₂' : a (s + 2) = blocker + 2 * s + 4 := by
        simpa using hvalue₂
      have hstep' : a (s + 3) = a (s + 2) - (s + 3) := by
        simpa [Nat.add_assoc] using hstep
      omega

/-- Parity strengthens the preceding gap by one clock.  Two adjacent fresh
entry values must occur in opposite triangular-parity classes, whereas a
four-clock shift preserves triangular parity. -/
theorem HistoryTerminatedComb.singleton_unitLadder_gap_five
    {s blocker nextTime : Nat}
    (hcomb : HistoryTerminatedComb s 0 blocker)
    (hnoninitial : 1 < s)
    (hlater : s < nextTime)
    (hlegal : CanSubtract nextTime (stateAt (nextTime - 1)))
    (hnextEntry : a nextTime = blocker + 2) :
    s + 5 ≤ nextTime := by
  have hgap := hcomb.singleton_unitLadder_gap_four
    hnoninitial hlater hlegal hnextEntry
  by_cases hstrong : s + 5 ≤ nextTime
  · exact hstrong
  · have htime : nextTime = s + 4 := by omega
    have hentry : a s + 1 = a nextTime := by
      have hstart := hcomb.blocker_eq
      simp only [Nat.mul_zero, Nat.add_zero] at hstart
      omega
    have hparity := adjacent_occurrence_opposite_parity hentry
    subst nextTime
    have hsame := upperTri_add_four s
    omega

/-- Six clocks add an odd triangular mass. -/
theorem upperTri_add_six (time : Nat) :
    upperTri (time + 6) = upperTri time + 6 * time + 21 := by
  have h4 := upperTri_add_four time
  have h5 : upperTri (time + 5) =
      upperTri (time + 4) + (time + 5) := by
    simpa [Nat.add_assoc] using upperTri_succ (time + 4)
  have h6 : upperTri (time + 6) =
      upperTri (time + 5) + (time + 6) := by
    simpa [Nat.add_assoc] using upperTri_succ (time + 5)
  omega

/-- The clock obstruction is only a sparsity condition, not a no-escape
theorem.  The coherent infinite schedule `time_j = 6*j` satisfies both the
five-clock gap and the required opposite triangular parity at every edge. -/
theorem singleton_unitLadder_clock_constraints_have_infinite_model
    (index : Nat) :
    let firstTime := 6 * index
    let nextTime := 6 * (index + 1)
    firstTime + 5 ≤ nextTime ∧
      (upperTri firstTime + upperTri nextTime) % 2 = 1 := by
  dsimp only
  have hclock : 6 * (index + 1) = 6 * index + 6 := by omega
  have htri := upperTri_add_six (6 * index)
  rw [hclock, htri]
  constructor <;> omega

/-! ## Fresh-entry reuse as a later terminal blocker -/

/-- If a later terminal blocker lies anywhere in an earlier comb's fresh
value interval, interval ordering forces it to be exactly the earlier entry.
Interior fresh rails can never be reused this way. -/
theorem HistoryTerminatedComb.later_blocker_on_freshInterval_eq_entry
    {s₁ k₁ blocker₁ s₂ k₂ blocker₂ : Nat}
    (h₁ : HistoryTerminatedComb s₁ k₁ blocker₁)
    (h₂ : HistoryTerminatedComb s₂ k₂ blocker₂)
    (hbefore : s₁ + 2 * k₁ < s₂)
    (hlower : blocker₁ < blocker₂)
    (hupper : blocker₂ ≤ a s₁) :
    blocker₂ = a s₁ := by
  have hblocker₂Entry : blocker₂ < a s₂ := by
    have hexit := h₂.episode.run.exit_value
    rw [h₂.blocker_eq] at hexit
    omega
  rcases h₁.fresh_intervals_ordered h₂ hbefore with
    hlaterLeft | hearlierLeft
  · omega
  · omega

/-- Reusing an earlier fresh entry as a later terminal blocker is possible
only when the later comb is shorter than the entry's subtraction clock.
This is the exact value restriction supplied by legal-origin provenance. -/
theorem HistoryTerminatedComb.later_blocker_eq_freshEntry_forces_short
    {s₁ k₁ blocker₁ s₂ k₂ blocker₂ : Nat}
    (h₁ : HistoryTerminatedComb s₁ k₁ blocker₁)
    (h₂ : HistoryTerminatedComb s₂ k₂ blocker₂)
    (hbefore : s₁ + 2 * k₁ < s₂)
    (hpositive : 0 < s₁)
    (hlegal : CanSubtract s₁ (stateAt (s₁ - 1)))
    (heq : blocker₂ = a s₁) :
    k₂ + 1 < s₁ := by
  have hfirst : FirstAt a blocker₂ s₁ := by
    rw [heq]
    exact h₁.episode.entry_first
  have hfirstBefore : s₁ < s₂ := by omega
  have habove := h₂.subtraction_origin_predecessor_above_entry
    hfirst hfirstBefore hpositive hlegal
  have hclock : s₁ - 1 + 1 = s₁ := by omega
  have hlegal' : CanSubtract (s₁ - 1 + 1) (stateAt (s₁ - 1)) := by
    simpa only [hclock] using hlegal
  have hstep := a_succ_of_canSubtract hlegal'
  rw [hclock] at hstep
  have hpredecessor : a (s₁ - 1) = a s₁ + s₁ := by
    have hpositiveStep : s₁ < a (s₁ - 1) := by
      simpa only [hclock, a] using hlegal'.1
    omega
  have hexit := h₂.episode.run.exit_value
  rw [h₂.blocker_eq] at hexit
  omega

private theorem historyTerminatedComb_38_13_25 :
    HistoryTerminatedComb 38 13 25 := by
  set_option maxRecDepth 100000 in
  set_option maxHeartbeats 8000000 in
  refine {
    episode := {
      entry_first := ?_
      run := ?_
    }
    final_forced := by decide
    blocker_eq := by decide
    blocker_seen := by decide
  }
  · simpa using firstAt_succ_of_canSubtract
      (n := 37) (by decide : CanSubtract 38 (stateAt 37))
  · intro i hi
    have hcases :
        i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨
        i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨
        i = 12 := by omega
    rcases hcases with h | h | h | h | h | h | h | h | h | h | h | h | h <;>
      subst i <;> constructor <;> decide

private theorem historyTerminatedComb_77_11_63 :
    HistoryTerminatedComb 77 11 63 := by
  set_option maxRecDepth 100000 in
  set_option maxHeartbeats 8000000 in
  refine {
    episode := {
      entry_first := ?_
      run := ?_
    }
    final_forced := by decide
    blocker_eq := by decide
    blocker_seen := by decide
  }
  · simpa using firstAt_succ_of_canSubtract
      (n := 76) (by decide : CanSubtract 77 (stateAt 76))
  · intro i hi
    have hcases :
        i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨
        i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 := by omega
    rcases hcases with h | h | h | h | h | h | h | h | h | h | h <;>
      subst i <;> constructor <;> decide

private theorem historyTerminatedComb_111_0_39 :
    HistoryTerminatedComb 111 0 39 := by
  set_option maxRecDepth 100000 in
  set_option maxHeartbeats 8000000 in
  refine {
    episode := {
      entry_first := ?_
      run := by intro i hi; omega
    }
    final_forced := by decide
    blocker_eq := by decide
    blocker_seen := by decide
  }
  simpa using firstAt_succ_of_canSubtract
    (n := 110) (by decide : CanSubtract 111 (stateAt 110))

/-- Unconditional fresh-entry no-return is false on the exact standard
prefix.  The target-4 comb with fresh entry 39 is followed by an intervening
terminal comb, after which 39 is reused as the blocker of the singleton
fresh-successor episode at time 111. -/
theorem freshLowEntry_later_terminalBlocker_counterexample :
    ∃ _h₁ : HistoryTerminatedComb 38 13 25,
      ∃ _hmiddle : HistoryTerminatedComb 77 11 63,
        ∃ _h₂ : HistoryTerminatedComb 111 0 39,
          a 38 = 39 ∧
          nextSubtractionCandidate 38 < 4 ∧
          nextSubtractionCandidate 77 < 4 ∧
          nextSubtractionCandidate 111 < 4 ∧
          38 + 2 * 13 < 77 ∧
          77 + 2 * 11 < 111 := by
  set_option maxRecDepth 100000 in
  set_option maxHeartbeats 8000000 in
    exact ⟨historyTerminatedComb_38_13_25,
      historyTerminatedComb_77_11_63,
      historyTerminatedComb_111_0_39,
      by decide, by decide, by decide, by decide, by decide, by decide⟩

end Recaman
