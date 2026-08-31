import Recaman.TargetCandidateTransitions
import Recaman.LeastTailLedgerProvenance

namespace Recaman

/-! # High subtraction-candidate excursions

Between two low target-relative candidate states, the orbit follows a
high-only excursion.  Its endpoint sums alone carry no new information:
they are exactly the subtraction-ledger identity.  What survives is a
prefix (ballot) condition.  Every proper point lies strictly on the high
side of the target line, and the exit crosses that line in one legal
subtraction.

This file records that surviving macro information.  The signed excess is
chosen so that an addition raises it by `n`, while a subtraction lowers it
by `n + 2`.
-/

/-- Signed height of the next subtraction candidate above `target`.  Unlike
`nextSubtractionCandidate`, this definition does not truncate at zero. -/
def targetCandidateExcess (target n : Nat) : Int :=
  (a n : Int) - (n : Int) - 1 - (target : Int)

theorem targetCandidateExcess_pos_iff
    {target n : Nat} :
    0 < targetCandidateExcess target n ↔
      target < nextSubtractionCandidate n := by
  simp [targetCandidateExcess, nextSubtractionCandidate]
  omega

theorem targetCandidateExcess_neg_iff
    {target n : Nat}
    (htarget : 0 < target) :
    targetCandidateExcess target n < 0 ↔
      nextSubtractionCandidate n < target := by
  simp [targetCandidateExcess, nextSubtractionCandidate]
  omega

/-- Addition has the small positive signed increment `n`. -/
theorem targetCandidateExcess_succ_of_not_canSubtract
    {target n : Nat}
    (hforced : ¬ CanSubtract (n + 1) (stateAt n)) :
    targetCandidateExcess target (n + 1) =
      targetCandidateExcess target n + Int.ofNat n := by
  have hstep := a_succ_of_not_canSubtract hforced
  simp [targetCandidateExcess, hstep]
  omega

/-- Subtraction has the clock-sized signed decrement `n + 2`. -/
theorem targetCandidateExcess_succ_of_canSubtract
    {target n : Nat}
    (hcan : CanSubtract (n + 1) (stateAt n)) :
    targetCandidateExcess target (n + 1) =
      targetCandidateExcess target n - Int.ofNat (n + 2) := by
  have hstep := a_succ_of_canSubtract hcan
  have hpositive := hcan.1
  have hle : n + 1 ≤ a n := by
    simpa [a] using Nat.le_of_lt hpositive
  simp only [targetCandidateExcess]
  rw [hstep]
  rw [Int.ofNat_sub hle]
  simp
  omega

/-- A nonempty maximal high-candidate block, including its first low state
as `finish + 1`. -/
structure TargetHighCandidateExcursion
    (target start finish : Nat) : Prop where
  start_le_finish : start ≤ finish
  high : ∀ n, start ≤ n → n ≤ finish →
    target < nextSubtractionCandidate n
  exit_low : nextSubtractionCandidate (finish + 1) < target

/-- The high-to-low exit cannot be an addition on a permanent missing tail;
it is necessarily a legal subtraction. -/
theorem TargetHighCandidateExcursion.exit_canSubtract
    {target tailStart start finish : Nat}
    (htail : MissingPermanentAboveTail target tailStart)
    (hstart : tailStart ≤ start)
    (h : TargetHighCandidateExcursion target start finish) :
    CanSubtract (finish + 1) (stateAt finish) := by
  by_cases hcan : CanSubtract (finish + 1) (stateAt finish)
  · exact hcan
  · have htime : tailStart ≤ finish :=
      Nat.le_trans hstart h.start_le_finish
    have hnextHigh :=
      htail.forcedAddition_candidate_strictAbove htime hcan
    exact False.elim
      ((Nat.not_lt_of_ge (Nat.le_of_lt hnextHigh)) h.exit_low)

/-- At the exit, the positive signed excess is smaller than the unique
clock-sized subtraction that crosses the target line. -/
theorem TargetHighCandidateExcursion.exit_window
    {target tailStart start finish : Nat}
    (htail : MissingPermanentAboveTail target tailStart)
    (hstart : tailStart ≤ start)
    (h : TargetHighCandidateExcursion target start finish) :
    0 < targetCandidateExcess target finish ∧
      targetCandidateExcess target finish < Int.ofNat (finish + 2) := by
  have hhigh := h.high finish h.start_le_finish (Nat.le_refl _)
  have hpositive := targetCandidateExcess_pos_iff.mpr hhigh
  have hnegative :=
    (targetCandidateExcess_neg_iff htail.target_positive).mpr h.exit_low
  have hcan := h.exit_canSubtract htail hstart
  have hstep := targetCandidateExcess_succ_of_canSubtract
    (target := target) hcan
  constructor
  · exact hpositive
  · omega

/-- Every prefix of a high excursion satisfies a strict clock-weighted
ballot inequality.  This is the non-endpoint information retained from the
ledger identity. -/
theorem TargetHighCandidateExcursion.prefix_ledger_strict
    {target start finish n : Nat}
    (h : TargetHighCandidateExcursion target start finish)
    (hstart : start ≤ n)
    (hfinish : n ≤ finish) :
    target + (n + 1) + 2 * (subSum n - subSum start) + upperTri start <
      a start + upperTri n := by
  have hhigh := h.high n hstart hfinish
  have hledger := ledger_interval_balance hstart
  simp only [nextSubtractionCandidate] at hhigh
  omega

/-- The first low state reverses the prefix inequality.  Together with
`prefix_ledger_strict`, this is an exact weighted first-passage corridor. -/
theorem TargetHighCandidateExcursion.exit_ledger_strict
    {target start finish : Nat}
    (htarget : 0 < target)
    (h : TargetHighCandidateExcursion target start finish) :
    a start + upperTri (finish + 1) <
      target + (finish + 2) +
        2 * (subSum (finish + 1) - subSum start) + upperTri start := by
  have htime : start ≤ finish + 1 :=
    Nat.le_trans h.start_le_finish (Nat.le_succ _)
  have hledger := ledger_interval_balance htime
  have hlow := h.exit_low
  simp only [nextSubtractionCandidate] at hlow
  omega

end Recaman
