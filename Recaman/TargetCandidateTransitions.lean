import Recaman.PermanentAboveTail
import Recaman.OrbitCombValues

namespace Recaman

/-! # Target-relative subtraction-candidate transitions

Fix a hypothetical least missing target and pass to its permanent strictly
above tail.  At time `n`, the subtraction candidate for the next clock is
`a n - (n + 1)`.  Candidates below the target are already in the completed
history, so they force addition.  The candidate exposed one clock later is
then `a n - 1`; target omission upgrades the usual weak bound on this value
to a strict one.

Thus a below-target candidate state is isolated: the target-relative binary
word cannot contain `00` on the permanent tail.  This is the local transition
rule needed by the target-level charging approach.  The optional repayment
branch is exactly the existing `CombStep` interface.
-/

/-- The subtraction candidate presented by the transition after time `n`. -/
def nextSubtractionCandidate (n : Nat) : Nat :=
  a n - (n + 1)

/-- On a completed least-missing tail, every below-target candidate is an
old value and therefore forces addition. -/
theorem MissingPermanentAboveTail.candidateBelow_forcesAddition
    {target start n : Nat}
    (h : MissingPermanentAboveTail target start)
    (htime : start ≤ n)
    (hlow : nextSubtractionCandidate n < target) :
    ¬ CanSubtract (n + 1) (stateAt n) := by
  intro hcan
  apply hcan.2
  change nextSubtractionCandidate n ∈ valuesThrough n
  exact valuesThrough_mono htime (h.below_covered _ hlow)

/-- A forced addition above a missing target cannot expose the target itself
as the next subtraction candidate.  It therefore exposes a value strictly
above the target. -/
theorem MissingPermanentAboveTail.forcedAddition_candidate_strictAbove
    {target start n : Nat}
    (h : MissingPermanentAboveTail target start)
    (htime : start ≤ n)
    (hforced : ¬ CanSubtract (n + 1) (stateAt n)) :
    target < nextSubtractionCandidate (n + 1) := by
  have habove := h.strictly_above n htime
  have hnext := a_succ_of_not_canSubtract hforced
  have hcandidate : nextSubtractionCandidate (n + 1) = a n - 1 := by
    simp only [nextSubtractionCandidate]
    omega
  have hnotSuccessor : a n ≠ target + 1 := by
    intro hsuccessor
    have hcandidateTarget :
        nextSubtractionCandidate (n + 1) = target := by
      rw [hcandidate, hsuccessor]
      omega
    have hcanNext : CanSubtract (n + 2) (stateAt (n + 1)) := by
      constructor
      · change n + 2 < a (n + 1)
        rw [hnext, hsuccessor]
        have htargetPositive := h.target_positive
        omega
      · change nextSubtractionCandidate (n + 1) ∉
            valuesThrough (n + 1)
        rw [hcandidateTarget]
        intro hseen
        rcases mem_valuesThrough_iff.mp hseen with ⟨time, _, hvalue⟩
        exact h.target_missing ⟨time, hvalue⟩
    have hlanding := a_succ_of_canSubtract hcanNext
    have hlandingTarget : a (n + 2) = target := by
      change a (n + 2) = nextSubtractionCandidate (n + 1) at hlanding
      exact hlanding.trans hcandidateTarget
    exact h.target_missing ⟨n + 2, hlandingTarget⟩
  rw [hcandidate]
  omega

/-- Target-relative transition law: a low candidate forces the next orbit
step upward and the following candidate is strictly high. -/
theorem MissingPermanentAboveTail.candidateBelow_forces_highNext
    {target start n : Nat}
    (h : MissingPermanentAboveTail target start)
    (htime : start ≤ n)
    (hlow : nextSubtractionCandidate n < target) :
    ¬ CanSubtract (n + 1) (stateAt n) ∧
      target < nextSubtractionCandidate (n + 1) := by
  have hforced := h.candidateBelow_forcesAddition htime hlow
  exact ⟨hforced, h.forcedAddition_candidate_strictAbove htime hforced⟩

/-- In particular, the target-relative candidate word has no consecutive
low states on the permanent above tail. -/
theorem MissingPermanentAboveTail.not_two_consecutive_candidateBelow
    {target start n : Nat}
    (h : MissingPermanentAboveTail target start)
    (htime : start ≤ n) :
    ¬ (nextSubtractionCandidate n < target ∧
      nextSubtractionCandidate (n + 1) < target) := by
  rintro ⟨hlow, hlowNext⟩
  exact (Nat.not_lt_of_ge
    (Nat.le_of_lt (h.candidateBelow_forces_highNext htime hlow).2)) hlowNext

/-- If the high candidate exposed after a low state is fresh, the two-step
episode is precisely one existing comb period.  Otherwise its failure is a
historical blocker, not a positivity failure. -/
theorem MissingPermanentAboveTail.candidateBelow_comb_or_historyBlocker
    {target start n : Nat}
    (h : MissingPermanentAboveTail target start)
    (htime : start ≤ n)
    (hlow : nextSubtractionCandidate n < target) :
    CombStep n ∨
      (nextSubtractionCandidate (n + 1) ∈ valuesThrough (n + 1) ∧
        ¬ CanSubtract (n + 2) (stateAt (n + 1))) := by
  have htransition := h.candidateBelow_forces_highNext htime hlow
  rcases htransition with ⟨hforced, hhigh⟩
  by_cases hcanNext : CanSubtract (n + 2) (stateAt (n + 1))
  · exact Or.inl ⟨hforced, hcanNext⟩
  · apply Or.inr
    refine ⟨?_, hcanNext⟩
    have hpositive : n + 2 < (stateAt (n + 1)).value := by
      change n + 2 < a (n + 1)
      have hnext := a_succ_of_not_canSubtract hforced
      have hcandidatePositive :
          0 < nextSubtractionCandidate (n + 1) :=
        Nat.lt_trans h.target_positive hhigh
      simp only [nextSubtractionCandidate] at hcandidatePositive
      omega
    by_cases hmem :
        nextSubtractionCandidate (n + 1) ∈ valuesThrough (n + 1)
    · exact hmem
    · exact False.elim (hcanNext ⟨hpositive, hmem⟩)

/-! ## Maximal descending combs and one-use terminal blockers

A high-to-low transition lands on a fresh value.  The ensuing alternating
forced-addition/legal-subtraction episode is an `OrbitComb.CombRun`, shifted
to begin at that landing.  Recording freshness at the entry makes freshness
of the final low-rail value explicit.  If the next predecessor is historical,
it terminates the comb; the blocker `b` is then paired with the first
occurrence of `b+1`.  Consequently two temporally distinct completed combs
cannot use the same terminal blocker.
-/

/-- A comb run whose entry low-rail value is itself a fresh subtraction
landing. -/
structure FreshCombEpisode (s k : Nat) : Prop where
  entry_first : FirstAt a (a s) s
  run : CombRun s k

/-- Every low-rail landing of a fresh comb episode is a first occurrence. -/
theorem FreshCombEpisode.low_rail_first
    {s k i : Nat} (h : FreshCombEpisode s k) (hi : i ≤ k) :
    FirstAt a (a (s + 2 * i)) (s + 2 * i) := by
  by_cases hi0 : i = 0
  · subst i
    simpa using h.entry_first
  · have hipos : 0 < i := Nat.pos_of_ne_zero hi0
    have hstep : CombStep (s + 2 * (i - 1)) :=
      h.run (i - 1) (by omega)
    have hlegal :
        CanSubtract ((s + 2 * (i - 1) + 1) + 1)
          (stateAt (s + 2 * (i - 1) + 1)) := by
      simpa [Nat.add_assoc] using hstep.legal_down
    have hfirst := firstAt_succ_of_canSubtract hlegal
    have htime : s + 2 * (i - 1) + 1 + 1 = s + 2 * i := by
      omega
    simpa [htime] using hfirst

/-- The final low-rail landing of a fresh comb episode is also its first
occurrence. -/
theorem FreshCombEpisode.final_first
    {s k : Nat} (h : FreshCombEpisode s k) :
    FirstAt a (a (s + 2 * k)) (s + 2 * k) :=
  h.low_rail_first (Nat.le_refl _)

/-- Chronologically disjoint fresh comb episodes have disjoint low rails.
This is the interval-packing form of finite consumption: every tooth is a
globally fresh value, not merely a value unused inside its own episode. -/
theorem FreshCombEpisode.low_rail_ne_of_before
    {s₁ k₁ s₂ k₂ i j : Nat}
    (_h₁ : FreshCombEpisode s₁ k₁)
    (h₂ : FreshCombEpisode s₂ k₂)
    (hbefore : s₁ + 2 * k₁ < s₂)
    (hi : i ≤ k₁) (hj : j ≤ k₂) :
    a (s₁ + 2 * i) ≠ a (s₂ + 2 * j) := by
  intro hequal
  have hfirst₂ := h₂.low_rail_first hj
  exact hfirst₂.2 (s₁ + 2 * i) (by omega) hequal

/-- A fresh comb stopped by the already-seen predecessor of its final low
rail.  `final_forced` is the forced addition immediately after that landing;
the historical predecessor blocks repayment on the following clock. -/
structure HistoryTerminatedComb (s k blocker : Nat) : Prop where
  episode : FreshCombEpisode s k
  final_forced :
    ¬ CanSubtract (s + 2 * k + 1) (stateAt (s + 2 * k))
  blocker_eq : a (s + 2 * k) = blocker + 1
  blocker_seen : blocker ∈ valuesThrough (s + 2 * k)

/-- A terminal blocker cannot have been created on either rail of the comb
which it terminates.  Its occurrence is genuinely pre-entry history. -/
theorem HistoryTerminatedComb.blocker_occurs_before_entry
    {s k blocker : Nat} (h : HistoryTerminatedComb s k blocker) :
    ∃ earlier, earlier < s ∧ a earlier = blocker := by
  have hexit := h.episode.run.exit_value
  rw [h.blocker_eq] at hexit
  rcases h.episode.run.mem_valuesThrough_iff.mp h.blocker_seen with
    hbase | hhigh | hlow
  · rcases mem_valuesThrough_iff.mp hbase with
      ⟨earlier, hearlier, hvalue⟩
    refine ⟨earlier, ?_, hvalue⟩
    by_cases heq : earlier = s
    · subst earlier
      omega
    · omega
  · rcases hhigh with ⟨i, hi, hvalue⟩
    have hrail := h.episode.run.high_rail i hi
    omega
  · rcases hlow with ⟨i, hi, hvalue⟩
    have hrail := h.episode.run.low_rail (i + 1) (by omega)
    have htime : s + 2 * (i + 1) = s + 2 * i + 2 := by omega
    rw [htime] at hrail
    omega

/-- The terminal blocker has a canonical first occurrence strictly before
the comb entry. -/
theorem HistoryTerminatedComb.blocker_has_firstAt_before_entry
    {s k blocker : Nat} (h : HistoryTerminatedComb s k blocker) :
    ∃ firstTime, firstTime < s ∧ FirstAt a blocker firstTime := by
  rcases h.blocker_occurs_before_entry with
    ⟨earlier, hearlier, hvalue⟩
  rcases exists_firstAt_bounded a earlier blocker
      ⟨earlier, Nat.le_refl _, hvalue⟩ with
    ⟨firstTime, hfirstTime, hfirst⟩
  exact ⟨firstTime, Nat.lt_of_le_of_lt hfirstTime hearlier, hfirst⟩

/-- If the blocker's first occurrence was produced by a subtraction, its
predecessor lies strictly above the whole fresh low-rail interval.  Otherwise
that predecessor would have appeared before one of the interval's certified
first landings. -/
theorem HistoryTerminatedComb.subtraction_origin_predecessor_above_entry
    {s k blocker firstTime : Nat}
    (h : HistoryTerminatedComb s k blocker)
    (hfirst : FirstAt a blocker firstTime)
    (hfirstBefore : firstTime < s)
    (hpositive : 0 < firstTime)
    (hcan : CanSubtract firstTime (stateAt (firstTime - 1))) :
    a s < a (firstTime - 1) := by
  have hclock : firstTime - 1 + 1 = firstTime := by omega
  have hcan' : CanSubtract (firstTime - 1 + 1)
      (stateAt (firstTime - 1)) := by
    simpa only [hclock] using hcan
  have hstep := a_succ_of_canSubtract hcan'
  rw [hclock] at hstep
  have hpredecessorPositive : firstTime < a (firstTime - 1) := by
    simpa only [hclock, a] using hcan'.1
  have hexit := h.episode.run.exit_value
  rw [h.blocker_eq] at hexit
  by_cases habove : a s < a (firstTime - 1)
  · exact habove
  · have hpredecessorLe : a (firstTime - 1) ≤ a s :=
      Nat.le_of_not_gt habove
    let i := a s - a (firstTime - 1)
    have hi : i ≤ k := by
      simp only [i]
      have hfirstValue := hfirst.1
      omega
    have hrail := h.episode.run.low_rail i hi
    have hlanding : a (s + 2 * i) = a (firstTime - 1) := by
      simp only [i] at hrail
      simp only [i]
      omega
    have hlandingFirst := h.episode.low_rail_first hi
    exact False.elim
      (hlandingFirst.2 (firstTime - 1) (by omega) hlanding.symm)

/-- The recorded historical predecessor really forces the transition after
the final comb addition. -/
theorem HistoryTerminatedComb.repayment_forced
    {s k blocker : Nat} (h : HistoryTerminatedComb s k blocker) :
    ¬ CanSubtract (s + 2 * k + 2) (stateAt (s + 2 * k + 1)) := by
  have hadd := a_succ_of_not_canSubtract h.final_forced
  have hcandidate :
      a (s + 2 * k + 1) - (s + 2 * k + 2) = blocker := by
    rw [hadd, h.blocker_eq]
    omega
  have hseenLater : blocker ∈ valuesThrough (s + 2 * k + 1) :=
    valuesThrough_persist h.blocker_seen
  intro hcan
  apply hcan.2
  change a (s + 2 * k + 1) - (s + 2 * k + 2) ∈
    valuesThrough (s + 2 * k + 1)
  rw [hcandidate]
  exact hseenLater

/-- A terminal blocker is paired with a unique final landing time: using
`blocker` consumes the fresh successor `blocker+1`, so the same blocker
cannot terminate a second comb at a different time. -/
theorem HistoryTerminatedComb.same_blocker_finalTime_eq
    {s₁ k₁ s₂ k₂ blocker : Nat}
    (h₁ : HistoryTerminatedComb s₁ k₁ blocker)
    (h₂ : HistoryTerminatedComb s₂ k₂ blocker) :
    s₁ + 2 * k₁ = s₂ + 2 * k₂ := by
  have hfirst₁ := h₁.episode.final_first
  have hfirst₂ := h₂.episode.final_first
  rw [h₁.blocker_eq] at hfirst₁
  rw [h₂.blocker_eq] at hfirst₂
  by_cases hlt : s₁ + 2 * k₁ < s₂ + 2 * k₂
  · exact False.elim (hfirst₂.2 _ hlt hfirst₁.1)
  · by_cases hgt : s₂ + 2 * k₂ < s₁ + 2 * k₁
    · exact False.elim (hfirst₁.2 _ hgt hfirst₂.1)
    · omega

/-- Consecutive completed combs obey an interval-order dichotomy.  If the
first comb finishes before the second starts, then the second fresh interval
lies wholly below the first terminal blocker, or the second terminal blocker
jumps strictly above the first.  A fresh interval can never straddle an old
terminal blocker. -/
theorem HistoryTerminatedComb.next_entry_below_or_blocker_lt
    {s₁ k₁ blocker₁ s₂ k₂ blocker₂ : Nat}
    (h₁ : HistoryTerminatedComb s₁ k₁ blocker₁)
    (h₂ : HistoryTerminatedComb s₂ k₂ blocker₂)
    (hbefore : s₁ + 2 * k₁ < s₂) :
    a s₂ < blocker₁ ∨ blocker₁ < blocker₂ := by
  by_cases hentryBelow : a s₂ < blocker₁
  · exact Or.inl hentryBelow
  · apply Or.inr
    have hblockerNe : blocker₁ ≠ blocker₂ := by
      intro hequal
      subst blocker₂
      have hfinalEq := h₁.same_blocker_finalTime_eq h₂
      omega
    by_cases hnotLt : blocker₁ < blocker₂
    · exact hnotLt
    have hblocker₂Lt : blocker₂ < blocker₁ := by omega
    have hentryGe : blocker₁ ≤ a s₂ := Nat.le_of_not_gt hentryBelow
    let i := a s₂ - blocker₁
    have hfinalRail := h₂.episode.run.exit_value
    rw [h₂.blocker_eq] at hfinalRail
    have hi : i ≤ k₂ := by
      simp only [i]
      omega
    have hrail := h₂.episode.run.low_rail i hi
    have hlanding : a (s₂ + 2 * i) = blocker₁ := by
      simp only [i] at hrail
      simp only [i]
      omega
    have hfirst := h₂.episode.low_rail_first hi
    rcases mem_valuesThrough_iff.mp h₁.blocker_seen with
      ⟨earlier, hearlier, hvalue⟩
    exact False.elim
      (hfirst.2 earlier (by omega) (hvalue.trans hlanding.symm))

end Recaman
