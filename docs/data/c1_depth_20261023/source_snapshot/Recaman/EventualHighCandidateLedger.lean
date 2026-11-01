import Recaman.TargetHighCandidateExcursion

namespace Recaman

/-! # The weighted-ledger boundary of an eventual high-candidate tail

Without a first low exit, the strict prefix inequality of a high-candidate
excursion contains exactly the same information as the pointwise high
condition.  This file records that equivalence so the weighted ledger is not
mistaken for an additional decreasing potential.
-/

/-- At any endpoint after `start`, the strict weighted ledger inequality is
equivalent to saying that the next subtraction candidate is above `target`.
The interval ledger supplies the equivalence in both directions. -/
theorem target_lt_candidate_iff_interval_ledger_strict
    {target start n : Nat}
    (hstart : start ≤ n) :
    target < nextSubtractionCandidate n ↔
      target + (n + 1) + 2 * (subSum n - subSum start) + upperTri start <
        a start + upperTri n := by
  have hledger := ledger_interval_balance hstart
  simp only [nextSubtractionCandidate]
  omega

/-- Consequently an eventual high-candidate corridor is equivalent, not
merely sufficient, to the family of all strict prefix ledger inequalities. -/
theorem eventuallyHighCandidate_iff_forall_interval_ledger_strict
    {target start : Nat} :
    (∀ n, start ≤ n → target < nextSubtractionCandidate n) ↔
      ∀ n, start ≤ n →
        target + (n + 1) + 2 * (subSum n - subSum start) + upperTri start <
          a start + upperTri n := by
  constructor
  · intro hhigh n hstart
    exact (target_lt_candidate_iff_interval_ledger_strict hstart).mp
      (hhigh n hstart)
  · intro hledger n hstart
    exact (target_lt_candidate_iff_interval_ledger_strict hstart).mpr
      (hledger n hstart)

end Recaman
