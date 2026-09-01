import Recaman.TargetLadderClock
import Recaman.TargetHighCandidateExcursion
import Recaman.ForcedCandidateReuseBalance

namespace Recaman

/-! # Consecutive target-terminal macro episodes

`HistoryTerminatedComb` forgets why two completed combs are consecutive for
one fixed target.  The minimal successor interface records that the second
entry is the first later target-low candidate after the first final low rail:
the open clock interval between them is strictly target-high.
-/

/-- Two maximal history-terminal combs which are consecutive in the
target-relative candidate word.  All fields are supplied by maximal low
extraction and choosing the least later low clock; no blocker-order or
no-return conclusion is assumed. -/
structure TargetMacroSuccessor
    (target tailStart s₁ k₁ blocker₁ s₂ k₂ blocker₂ : Nat) : Prop where
  tail : MissingPermanentAboveTail target tailStart
  first : HistoryTerminatedComb s₁ k₁ blocker₁
  second : HistoryTerminatedComb s₂ k₂ blocker₂
  first_inside_tail : tailStart < s₁
  chronological : s₁ + 2 * k₁ < s₂
  first_low : nextSubtractionCandidate s₁ < target
  second_low : nextSubtractionCandidate s₂ < target
  candidate_high_between : ∀ time,
    s₁ + 2 * k₁ < time → time < s₂ →
      target < nextSubtractionCandidate time

/-- The first target-low entry is produced by legal subtraction. -/
theorem TargetMacroSuccessor.first_entry_legal
    {target tailStart s₁ k₁ blocker₁ s₂ k₂ blocker₂ : Nat}
    (h : TargetMacroSuccessor target tailStart
      s₁ k₁ blocker₁ s₂ k₂ blocker₂) :
    CanSubtract s₁ (stateAt (s₁ - 1)) := by
  have hinside : tailStart < s₁ := h.first_inside_tail
  have hclock : s₁ - 1 + 1 = s₁ := by omega
  have htime : tailStart ≤ s₁ - 1 := by omega
  have hlow : nextSubtractionCandidate (s₁ - 1 + 1) < target := by
    simpa only [hclock] using h.first_low
  simpa only [hclock] using
    h.tail.candidateBelow_entry_legal htime hlow

/-- The high-between field explicitly implies that no same-target low
terminal comb can start strictly between the two selected macro episodes. -/
theorem TargetMacroSuccessor.no_intermediate_targetTerminal
    {target tailStart s₁ k₁ blocker₁ s₂ k₂ blocker₂ : Nat}
    (h : TargetMacroSuccessor target tailStart
      s₁ k₁ blocker₁ s₂ k₂ blocker₂) :
    ¬ ∃ middleStart middleLength middleBlocker,
      s₁ + 2 * k₁ < middleStart ∧ middleStart < s₂ ∧
      nextSubtractionCandidate middleStart < target ∧
      HistoryTerminatedComb middleStart middleLength middleBlocker := by
  rintro ⟨middleStart, middleLength, middleBlocker,
    hafter, hbefore, hlow, _hmiddle⟩
  have hhigh := h.candidate_high_between middleStart hafter hbefore
  omega

/-- The two terminal forced additions make the next target-low entry at
least three clocks later than the previous final low. -/
theorem TargetMacroSuccessor.second_start_gap
    {target tailStart s₁ k₁ blocker₁ s₂ k₂ blocker₂ : Nat}
    (h : TargetMacroSuccessor target tailStart
      s₁ k₁ blocker₁ s₂ k₂ blocker₂) :
    s₁ + 2 * k₁ + 3 ≤ s₂ := by
  let finalTime := s₁ + 2 * k₁
  have hinside : tailStart < s₁ := h.first_inside_tail
  have hchronological : s₁ + 2 * k₁ < s₂ := h.chronological
  rcases h.first.two_forced_launch with
    ⟨_hforced₁, _hforced₂, hvalue₁, hvalue₂⟩
  have hfirstTime : tailStart ≤ s₁ := by omega
  rcases h.first.tail_blocker_debtNormalProgress h.tail hfirstTime with
    ⟨_firstTime, htargetBlocker, _hfirst, _hfirstBefore,
      _hblockerEntry, _hdebt, _hprogress⟩
  have hhigh₁ : target < nextSubtractionCandidate (finalTime + 1) := by
    simp only [nextSubtractionCandidate]
    dsimp only [finalTime] at hvalue₁ ⊢
    rw [hvalue₁]
    omega
  have hhigh₂ : target < nextSubtractionCandidate (finalTime + 2) := by
    simp only [nextSubtractionCandidate]
    dsimp only [finalTime] at hvalue₂ ⊢
    rw [hvalue₂]
    omega
  by_cases hgap : finalTime + 3 ≤ s₂
  · simpa only [finalTime] using hgap
  · exfalso
    have hcases : s₂ = finalTime + 1 ∨ s₂ = finalTime + 2 := by
      dsimp only [finalTime] at hchronological hgap ⊢
      omega
    rcases hcases with htime | htime
    · have hlow := h.second_low
      rw [htime] at hlow
      omega
    · have hlow := h.second_low
      rw [htime] at hlow
      omega

/-- A successor is exactly one maximal high-candidate excursion followed by
its low exit. -/
theorem TargetMacroSuccessor.high_excursion
    {target tailStart s₁ k₁ blocker₁ s₂ k₂ blocker₂ : Nat}
    (h : TargetMacroSuccessor target tailStart
      s₁ k₁ blocker₁ s₂ k₂ blocker₂) :
    TargetHighCandidateExcursion target
      (s₁ + 2 * k₁ + 1) (s₂ - 1) := by
  refine {
    start_le_finish := by
      have hgap := h.second_start_gap
      omega
    high := ?_
    exit_low := by
      have hgap := h.second_start_gap
      have hclock : s₂ - 1 + 1 = s₂ := by omega
      simpa only [hclock] using h.second_low
  }
  intro time hstart hfinish
  apply h.candidate_high_between time
  · omega
  · have hgap := h.second_start_gap
    omega

/-- Exact residual left by a hypothetical return of the first fresh entry
as the second terminal blocker.  Every field below follows from the
successor interface and existing orbit theorems. -/
structure TargetMacroEntryReturnResidual
    {target tailStart s₁ k₁ blocker₁ s₂ k₂ blocker₂ : Nat}
    (source : TargetMacroSuccessor target tailStart
      s₁ k₁ blocker₁ s₂ k₂ blocker₂) : Prop where
  blocker_eq_entry : blocker₂ = a s₁
  blocker_first : FirstAt a blocker₂ s₁
  entry_incoming_legal : CanSubtract s₁ (stateAt (s₁ - 1))
  origin_predecessor_eq : a (s₁ - 1) = blocker₂ + s₁
  later_short : k₂ + 1 < s₁
  final_successor_first : FirstAt a (blocker₂ + 1) (s₂ + 2 * k₂)
  high_excursion : TargetHighCandidateExcursion target
    (s₁ + 2 * k₁ + 1) (s₂ - 1)

/-- Current APIs reduce the desired successor no-return statement to the
proof-carrying residual above, but do not eliminate it. -/
theorem TargetMacroSuccessor.entry_ne_or_returnResidual
    {target tailStart s₁ k₁ blocker₁ s₂ k₂ blocker₂ : Nat}
    (h : TargetMacroSuccessor target tailStart
      s₁ k₁ blocker₁ s₂ k₂ blocker₂) :
    blocker₂ ≠ a s₁ ∨ TargetMacroEntryReturnResidual h := by
  by_cases heq : blocker₂ = a s₁
  · apply Or.inr
    have hlegal := h.first_entry_legal
    have hinside : tailStart < s₁ := h.first_inside_tail
    have hpositive : 0 < s₁ := by omega
    have hshort := h.first.later_blocker_eq_freshEntry_forces_short
      h.second h.chronological hpositive hlegal heq
    have hfirst : FirstAt a blocker₂ s₁ := by
      rw [heq]
      exact h.first.episode.entry_first
    have hclock : s₁ - 1 + 1 = s₁ := by omega
    have hlegal' : CanSubtract (s₁ - 1 + 1)
        (stateAt (s₁ - 1)) := by
      simpa only [hclock] using hlegal
    have hstep := a_succ_of_canSubtract hlegal'
    rw [hclock] at hstep
    have hpredecessor : a (s₁ - 1) = blocker₂ + s₁ := by
      have hstepPositive : s₁ < a (s₁ - 1) := by
        simpa only [hclock, a] using hlegal'.1
      omega
    have hfinal := h.second.episode.final_first
    rw [h.second.blocker_eq] at hfinal
    exact {
      blocker_eq_entry := heq
      blocker_first := hfirst
      entry_incoming_legal := hlegal
      origin_predecessor_eq := hpredecessor
      later_short := hshort
      final_successor_first := hfinal
      high_excursion := h.high_excursion
    }
  · exact Or.inl heq

/-- If the old entry is exposed as a subtraction candidate during the
successor's high word, its previous visit forces addition.  The exposure
cannot be the last high clock, and together with the terminal repayment it
carries the exact reuse-ledger balance. -/
def TargetMacroEntryHighReuseCertificate
    {target tailStart s₁ k₁ blocker₁ s₂ k₂ blocker₂ : Nat}
    (source : TargetMacroSuccessor target tailStart
      s₁ k₁ blocker₁ s₂ k₂ blocker₂)
    (_residual : TargetMacroEntryReturnResidual source) : Prop :=
  ∃ exposureTime,
    s₁ + 2 * k₁ + 1 ≤ exposureTime ∧
    exposureTime < s₂ - 1 ∧
    nextSubtractionCandidate exposureTime = blocker₂ ∧
    (¬ CanSubtract (exposureTime + 1) (stateAt exposureTime)) ∧
    nextSubtractionCandidate (s₂ + 2 * k₂ + 1) = blocker₂ ∧
    (¬ CanSubtract (s₂ + 2 * k₂ + 2)
      (stateAt (s₂ + 2 * k₂ + 1))) ∧
    2 * (subSum (s₂ + 2 * k₂ + 1) - subSum exposureTime) +
        (s₂ + 2 * k₂ + 1 - exposureTime) +
        upperTri exposureTime = upperTri (s₂ + 2 * k₂ + 1)

/-- One residual return has exactly two possibilities at the present API
boundary.  Either the old entry is used during the high word, producing the
full forced-reuse balance above, or the entire high candidate word avoids it
until its mandatory exposure at the second terminal repayment. -/
theorem TargetMacroEntryReturnResidual.highReuse_or_avoidsHigh
    {target tailStart s₁ k₁ blocker₁ s₂ k₂ blocker₂ : Nat}
    {source : TargetMacroSuccessor target tailStart
      s₁ k₁ blocker₁ s₂ k₂ blocker₂}
    (residual : TargetMacroEntryReturnResidual source) :
    TargetMacroEntryHighReuseCertificate source residual ∨
      ∀ time,
        s₁ + 2 * k₁ + 1 ≤ time → time ≤ s₂ - 1 →
          nextSubtractionCandidate time ≠ blocker₂ := by
  classical
  by_cases hexposed : ∃ time,
      s₁ + 2 * k₁ + 1 ≤ time ∧ time ≤ s₂ - 1 ∧
        nextSubtractionCandidate time = blocker₂
  · left
    rcases hexposed with ⟨time, hstart, hfinish, hcandidate⟩
    have hinside : tailStart < s₁ := source.first_inside_tail
    have hchronological : s₁ + 2 * k₁ < s₂ := source.chronological
    have hs₁Time : s₁ ≤ time := by omega
    have hseen : blocker₂ ∈ valuesThrough time := by
      apply mem_valuesThrough_iff.mpr
      exact ⟨s₁, hs₁Time, residual.blocker_eq_entry.symm⟩
    have hforced : ¬ CanSubtract (time + 1) (stateAt time) := by
      intro hcan
      apply hcan.2
      change a time - (time + 1) ∈ valuesThrough time
      have hcandidateValue : a time - (time + 1) = blocker₂ := by
        simpa only [nextSubtractionCandidate] using hcandidate
      rw [hcandidateValue]
      exact hseen
    have htime₂ : tailStart ≤ s₂ := by omega
    rcases source.second.tail_blocker_debtNormalProgress
        source.tail htime₂ with
      ⟨_firstTime, htargetBlocker, _hfirst, _hfirstBefore,
        _hblockerEntry, _hdebt, _hprogress⟩
    have hblockerPositive : 0 < blocker₂ := by omega
    have hpositive : time + 1 < a time := by
      have hcandidateValue : a time - (time + 1) = blocker₂ := by
        simpa only [nextSubtractionCandidate] using hcandidate
      omega
    have hnextCandidate := nextCandidate_after_positive_forcedAddition
      hpositive hcandidate hforced
    have hbeforeLast : time < s₂ - 1 := by
      have hne : time ≠ s₂ - 1 := by
        intro htimeEq
        have hclock : time + 1 = s₂ := by omega
        have hlow := source.second_low
        rw [← hclock, hnextCandidate] at hlow
        omega
      omega
    let terminalPreTime := s₂ + 2 * k₂ + 1
    rcases source.second.two_forced_launch with
      ⟨_hterminalFirstForced, hterminalForced,
        hterminalValue, _hterminalNextValue⟩
    have hterminalCandidate :
        nextSubtractionCandidate terminalPreTime = blocker₂ := by
      simp only [nextSubtractionCandidate]
      dsimp only [terminalPreTime]
      rw [hterminalValue]
      omega
    have hterminalPositive :
        terminalPreTime + 1 < a terminalPreTime := by
      simp only [nextSubtractionCandidate] at hterminalCandidate
      omega
    have htimeOrder : time < terminalPreTime := by
      dsimp only [terminalPreTime]
      omega
    rcases same_positive_forcedCandidate_reuse_bundle
        htimeOrder hpositive hterminalPositive hcandidate
        hterminalCandidate hforced hterminalForced with
      ⟨_candidateFirstTime, _hcandidateFirst, _hfirstEarlier,
        _hfirstTerminal, hbalance⟩
    refine ⟨time, hstart, hbeforeLast, hcandidate, hforced, ?_, ?_, ?_⟩
    · simpa only [terminalPreTime] using hterminalCandidate
    · simpa only [terminalPreTime] using hterminalForced
    · simpa only [terminalPreTime] using hbalance
  · right
    intro time hstart hfinish hcandidate
    exact hexposed ⟨time, hstart, hfinish, hcandidate⟩

/-- Returning the first entry as the next blocker is possible only in the
triangular-parity-compatible class.  Thus the odd half of the empirical
parity-or-mass split is eliminated without any visited-history input. -/
theorem TargetMacroEntryReturnResidual.parity_compatible
    {target tailStart s₁ k₁ blocker₁ s₂ k₂ blocker₂ : Nat}
    {source : TargetMacroSuccessor target tailStart
      s₁ k₁ blocker₁ s₂ k₂ blocker₂}
    (residual : TargetMacroEntryReturnResidual source) :
    (upperTri s₁ + upperTri s₂ + (k₂ + 1)) % 2 = 0 := by
  have hfirst := parity_invariant s₁
  have hsecond := parity_invariant s₂
  have hentry := source.second.entry_eq_blocker_add_length
  have hreturn := residual.blocker_eq_entry
  omega

/-- A parity-incompatible immediate successor cannot return the old entry as
its terminal blocker.  This closes the odd half of the computational
parity-or-mass split unconditionally. -/
theorem TargetMacroSuccessor.entry_ne_of_parity_incompatible
    {target tailStart s₁ k₁ blocker₁ s₂ k₂ blocker₂ : Nat}
    (source : TargetMacroSuccessor target tailStart
      s₁ k₁ blocker₁ s₂ k₂ blocker₂)
    (hincompatible :
      (upperTri s₁ + upperTri s₂ + (k₂ + 1)) % 2 = 1) :
    blocker₂ ≠ a s₁ := by
  rcases source.entry_ne_or_returnResidual with hne | residual
  · exact hne
  · have hcompatible := residual.parity_compatible
    omega

end Recaman
