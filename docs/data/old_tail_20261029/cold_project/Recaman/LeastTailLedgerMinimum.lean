import Recaman.TailStartTwoSided
import Recaman.SubtractionLedger

namespace Recaman

/-! # The least permanent tail in ledger coordinates

A hypothetical least missing target has a least start of its permanent
strictly-above tail.  Minimality of that start controls the first tail value:
the preceding orbit value is below the target, so entry into the tail is a
forced addition.  Combining this local bound with a minimum certificate,
quotient/remainder coordinates, and the subtraction ledger places the tail
minimum in the two lowest quotient bands and in a narrow ledger corridor.
-/

/-- At the minimum of the least strictly-above tail, the value is bounded by
the forced-addition entry value at the tail start. -/
private theorem leastTailMinimum_value_add_one_le
    {target start time firstTime : Nat}
    (htail : MissingStrictAboveTail target start)
    (hleast : ∀ other, MissingStrictAboveTail target other → start ≤ other)
    (htargetStart : target ≤ start)
    (hminimum : PermanentTailMinimumCertificate
      target start time firstTime) :
    a time + 1 ≤ target + start := by
  have hstartPos := missingStrictAboveTail_pos htail
  have hprevious := least_predecessor_below_target htail hleast
  have hforced :
      ¬ CanSubtract ((start - 1) + 1) (stateAt (start - 1)) := by
    intro hcan
    have hpositive : (start - 1) + 1 < a (start - 1) := by
      simpa [a] using hcan.1
    omega
  have hentry := a_succ_of_not_canSubtract hforced
  have hstartEq : (start - 1) + 1 = start := by omega
  have hentry' : a start = a (start - 1) + start := by
    simpa only [hstartEq] using hentry
  have hminimumLe := hminimum.minimum.minimal start (Nat.le_refl start)
  omega

/-- In the two lowest quotient bands, a permanent tail minimum is either
already bounded by `time + target`, or its first forced subtraction exposes
an earlier occurrence strictly between the target and the minimum.  Thus the
only unbounded `q = 1` case carries a concrete large-drop blocker. -/
theorem PermanentTailMinimumCertificate.lowQuotient_bounded_or_earlierBlocker
    {target start time firstTime q r : Nat}
    (htarget : 0 < target)
    (hminimum : PermanentTailMinimumCertificate
      target start time firstTime)
    (hcoordinates : CoordinatesAt time q r)
    (hquotient : q ≤ 1) :
    a time ≤ time + target ∨
      ∃ blockerTime,
        q = 1 ∧
        FirstAt a (r - 1) blockerTime ∧
        blockerTime < time ∧
        target ≤ r - 1 ∧
        r - 1 < a time := by
  have hcases : q = 0 ∨ q = 1 := by omega
  rcases hcases with hzero | hone
  · left
    subst q
    have hequation := hcoordinates.eqn
    have hremainder := hcoordinates.remainder_lt
    omega
  · subst q
    by_cases hremainderTarget : r ≤ target
    · left
      have hequation := hcoordinates.eqn
      omega
    · right
      have htargetRemainder : target < r := Nat.lt_of_not_ge hremainderTarget
      have hpositive : time + 1 < a time := by
        have hequation := hcoordinates.eqn
        omega
      have hcandidate : a time - (time + 1) = r - 1 := by
        have hequation := hcoordinates.eqn
        omega
      rcases not_canSubtract_cases hminimum.first_forced with
        hnonpositive | hseen
      · exact False.elim (by omega)
      · have hblockerSeen : r - 1 ∈ valuesThrough time := by
          simpa only [hcandidate] using hseen
        rcases history_member_has_firstAt hblockerSeen with
          ⟨blockerTime, hblockerLe, hblockerFirst⟩
        have hblockerBefore : blockerTime < time := by
          apply Nat.lt_of_le_of_ne hblockerLe
          intro hsame
          have hblockerValue := hblockerFirst.1
          have hequation := hcoordinates.eqn
          rw [hsame] at hblockerValue
          omega
        refine ⟨blockerTime, rfl, hblockerFirst, hblockerBefore, ?_, ?_⟩
        · omega
        · have hequation := hcoordinates.eqn
          omega

/-- A hypothetical least missing value yields a canonical least tail start,
a certified tail minimum, its quotient/remainder coordinates, and the sharp
height and subtraction-ledger bounds forced by those data.  Existing
structures carry all dynamical information; the theorem adds only the new
cross-structure inequalities. -/
theorem LeastMissingTarget.exists_leastTailLedgerMinimum
    {target : Nat} (h : LeastMissingTarget target) :
    ∃ start time firstTime q r,
      MissingStrictAboveTail target start ∧
      (∀ other, MissingStrictAboveTail target other → start ≤ other) ∧
      PermanentTailMinimumCertificate target start time firstTime ∧
      CoordinatesAt time q r ∧
      target + 2 ≤ a time ∧
      a time + 1 ≤ target + start ∧
      a time < 2 * time ∧
      q ≤ 1 ∧
      (-1 : Int) ≤ potential q r ∧
      2 * subSum time + (target + 2) ≤ upperTri time ∧
      upperTri time < 2 * subSum time + 2 * time := by
  rcases h.exists_missingPermanentAboveTail with ⟨someStart, hsomeTail⟩
  have hexists : ∃ start, MissingStrictAboveTail target start :=
    ⟨someStart, hsomeTail.toStrictAboveTail⟩
  rcases exists_least_missingStrictAboveTail hexists with
    ⟨start, htail, hleast⟩
  rcases exists_historyHorizon_covering_below h.below_occurs with
    ⟨historyHorizon, hcovered⟩
  have htargetStart : target ≤ start :=
    target_le_tailStart htail hcovered
  rcases htail.exists_minimumCertificate with
    ⟨time, firstTime, hminimum⟩
  have htargetMinimum : target + 2 ≤ a time := by
    have := hminimum.target_lt_predecessor
    omega
  have hminimumUpper : a time + 1 ≤ target + start :=
    leastTailMinimum_value_add_one_le htail hleast htargetStart hminimum
  have hstartPos := missingStrictAboveTail_pos htail
  have hstartTime := hminimum.minimum.start_le_time
  have htimePos : 0 < time := Nat.lt_of_lt_of_le hstartPos hstartTime
  have hminimumTwice : a time < 2 * time := by
    omega
  rcases exists_coordinatesAt htimePos with ⟨q, r, hcoordinates⟩
  have hquotient : q ≤ 1 := by
    by_cases hle : q ≤ 1
    · exact hle
    · have htwoLeQ : 2 ≤ q := by omega
      have hproduct : time * 2 ≤ time * q :=
        Nat.mul_le_mul_left time htwoLeQ
      have hequation := hcoordinates.eqn
      omega
  have hpotential : (-1 : Int) ≤ potential q r := by
    have hcases : q = 0 ∨ q = 1 := by omega
    rcases hcases with rfl | rfl <;> simp [potential, upperTri] <;> omega
  have hledger := ledger_identity time
  have hledgerLower :
      2 * subSum time + (target + 2) ≤ upperTri time := by
    omega
  have hledgerUpper :
      upperTri time < 2 * subSum time + 2 * time := by
    omega
  exact ⟨start, time, firstTime, q, r, htail, hleast, hminimum,
    hcoordinates, htargetMinimum, hminimumUpper, hminimumTwice,
    hquotient, hpotential, hledgerLower, hledgerUpper⟩

end Recaman
