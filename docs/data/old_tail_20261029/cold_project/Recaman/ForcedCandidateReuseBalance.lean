import Recaman.HighCandidateCausalReuse

namespace Recaman

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

/-! # The subtraction payment between two uses of one candidate

Selecting two orbit times at which the same positive subtraction candidate
is exposed gives a sharper endpoint specialization of the subtraction
ledger.  The time gap itself, rather than an arbitrary value difference,
appears in the balance.  The statement is useful for one reuse interval, but
different candidates' intervals can overlap heavily.
-/

/-- Two exposures of the same positive candidate force an exact subtraction
payment between their pre-states. -/
theorem same_positive_candidate_reuse_subtraction_balance
    {earlier later candidate : Nat}
    (htime : earlier < later)
    (hearlierPositive : earlier + 1 < a earlier)
    (hlaterPositive : later + 1 < a later)
    (hearlierCandidate : nextSubtractionCandidate earlier = candidate)
    (hlaterCandidate : nextSubtractionCandidate later = candidate) :
    2 * (subSum later - subSum earlier) + (later - earlier) +
        upperTri earlier = upperTri later := by
  have hledger := ledger_interval_balance (Nat.le_of_lt htime)
  simp only [nextSubtractionCandidate] at hearlierCandidate
  simp only [nextSubtractionCandidate] at hlaterCandidate
  omega

/-- The causal bundle for two forced uses: both uses share one earlier
first-occurrence witness, while the interval between their pre-states pays
the exact subtraction balance above.  This is the strongest unconditional
bundle available from raw candidate reuse. -/
theorem same_positive_forcedCandidate_reuse_bundle
    {earlier later candidate : Nat}
    (htime : earlier < later)
    (hearlierPositive : earlier + 1 < a earlier)
    (hlaterPositive : later + 1 < a later)
    (hearlierCandidate : nextSubtractionCandidate earlier = candidate)
    (hlaterCandidate : nextSubtractionCandidate later = candidate)
    (hearlierForced : ¬ CanSubtract (earlier + 1) (stateAt earlier))
    (_hlaterForced : ¬ CanSubtract (later + 1) (stateAt later)) :
    ∃ firstTime,
      FirstAt a candidate firstTime ∧
      firstTime < earlier + 1 ∧
      firstTime < later + 1 ∧
      2 * (subSum later - subSum earlier) + (later - earlier) +
          upperTri earlier = upperTri later := by
  rcases forcedAddition_positive_candidate_has_earlier_firstAt
      hearlierForced hearlierPositive with
    ⟨exposed, firstTime, hexposed, _, hfirst, hfirstTime⟩
  have hexposedCandidate : exposed = candidate := by
    calc
      exposed = a earlier - (earlier + 1) := hexposed
      _ = candidate := by
        simpa [nextSubtractionCandidate] using hearlierCandidate
  have hfirstCandidate : FirstAt a candidate firstTime := by
    simpa [hexposedCandidate] using hfirst
  exact ⟨firstTime, hfirstCandidate, hfirstTime, by omega,
    same_positive_candidate_reuse_subtraction_balance htime
      hearlierPositive hlaterPositive hearlierCandidate hlaterCandidate⟩

/-- A compact predicate for a positive forced use at a named clock. -/
def HighForcedCandidateUse
    (target candidate clock : Nat) : Prop :=
  0 < clock ∧
    target < candidate ∧
    nextSubtractionCandidate (clock - 1) = candidate ∧
    ¬ CanSubtract clock (stateAt (clock - 1))

/-- The endpoint order for a proper crossing of two open clock intervals. -/
def StrictlyCrossingIntervals
    (left₁ right₁ left₂ right₂ : Nat) : Prop :=
  left₁ < left₂ ∧ left₂ < right₁ ∧ right₁ < right₂

/-- Five candidate-reuse intervals already overlap in the exact standard
prefix.  Each of candidates `502, 499, 496, 493, 490` is used once no later
than clock `304` and again no earlier than clock `340`, while target `19`
remains absent.  Thus reuse-interval payments cannot be added using a
disjointness claim. -/
theorem five_high_candidate_reuse_intervals_overlap_counterexample :
    19 ∉ valuesThrough 348 ∧
      HighForcedCandidateUse 19 502 296 ∧
      HighForcedCandidateUse 19 502 340 ∧
      HighForcedCandidateUse 19 499 298 ∧
      HighForcedCandidateUse 19 499 342 ∧
      HighForcedCandidateUse 19 496 300 ∧
      HighForcedCandidateUse 19 496 344 ∧
      HighForcedCandidateUse 19 493 302 ∧
      HighForcedCandidateUse 19 493 346 ∧
      HighForcedCandidateUse 19 490 304 ∧
      HighForcedCandidateUse 19 490 348 := by
  unfold HighForcedCandidateUse
  decide

/-- A small certified structural counterexample to laminarity and to a
one-stack/noncrossing decomposition.  The two actual reuse intervals
`[296,340)` and `[298,342)` cross properly. -/
theorem high_candidate_reuse_intervals_cross_counterexample :
    19 ∉ valuesThrough 342 ∧
      HighForcedCandidateUse 19 502 296 ∧
      HighForcedCandidateUse 19 502 340 ∧
      HighForcedCandidateUse 19 499 298 ∧
      HighForcedCandidateUse 19 499 342 ∧
      StrictlyCrossingIntervals 296 340 298 342 := by
  unfold HighForcedCandidateUse StrictlyCrossingIntervals
  decide

end Recaman
