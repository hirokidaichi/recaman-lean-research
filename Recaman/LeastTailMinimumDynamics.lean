import Recaman.LeastTailLedgerMinimum
import Recaman.CanonicalSSFreeSupply
import Recaman.DriftResetAccumulation
import Recaman.GlobalUnboundednessSupply
import Recaman.NoDoubleAdditionRun
import Recaman.SubtractionLedger

namespace Recaman

open Recaman.CanonicalSSFreeSupply
open Recaman.ShortPeriodicSupply
open Recaman.DriftResetAccumulation
open Recaman.GlobalUnboundednessSupply

/-! # Dynamical expansion and unsupplied drift at the least tail minimum

At the certified minimum of a least permanent tail, the orbit dynamics is
heavily constrained:
1. The immediate step `time + 1` is a forced addition, keeping `subSum` and `subCount`
   constant while expanding the value by `time + 1`.
2. The follow-up step `time + 2` is also a forced addition, again keeping `subSum` and
   `subCount` constant and elevating the value to `a time + 2 * time + 3`.
3. This two-step addition burst unconditionally lifts the orbit into quotient band `q ≥ 2`.
4. Furthermore, by `double_forcedAddition_extends`, either step `time` was an addition
   or step `time + 3` is forced to be an addition.
5. In every case, an `AAA` run (three consecutive additions) occurs at or adjacent to
   the tail minimum, forcing at least one unsupplied addition (`1 ≤ unsuppliedCount`).
-/

/-- Step `time + 1` from the tail minimum is a forced addition. -/
theorem tail_minimum_first_canonicalSign
    {target start time firstTime : Nat}
    (hmin : PermanentTailMinimumCertificate target start time firstTime) :
    canonicalSign (time : Int) = true := by
  rw [canonicalSign_nat]
  simp [hmin.first_forced]

/-- Value at `time + 1` increases by `time + 1`. -/
theorem tail_minimum_first_value
    {target start time firstTime : Nat}
    (hmin : PermanentTailMinimumCertificate target start time firstTime) :
    a (time + 1) = a time + time + 1 :=
  hmin.first_addition

/-- `subSum` remains constant at step `time + 1`. -/
theorem tail_minimum_first_subSum
    {target start time firstTime : Nat}
    (hmin : PermanentTailMinimumCertificate target start time firstTime) :
    subSum (time + 1) = subSum time := by
  rw [subSum_succ, if_neg hmin.first_forced]
  omega

/-- `subCount` remains constant at step `time + 1`. -/
theorem tail_minimum_first_subCount
    {target start time firstTime : Nat}
    (hmin : PermanentTailMinimumCertificate target start time firstTime) :
    subCount (time + 1) = subCount time := by
  rw [subCount_succ, if_neg hmin.first_forced]
  omega

/-- Step `time + 2` from the tail minimum is also a forced addition. -/
theorem tail_minimum_followup_canonicalSign
    {target start time firstTime : Nat}
    (hmin : PermanentTailMinimumCertificate target start time firstTime) :
    canonicalSign ((time + 1 : Nat) : Int) = true := by
  rw [canonicalSign_nat]
  have h2 : time + 1 + 1 = time + 2 := by omega
  have hforced := hmin.followup_forced
  have hterm : ¬ CanSubtract (time + 1 + 1) (stateAt (time + 1)) := by
    simpa [h2] using hforced
  exact decide_eq_true hterm

/-- Value at `time + 2` increases by `2 * time + 3` over `a time`. -/
theorem tail_minimum_followup_value
    {target start time firstTime : Nat}
    (hmin : PermanentTailMinimumCertificate target start time firstTime) :
    a (time + 2) = a time + 2 * time + 3 := by
  have h1 := hmin.first_addition
  have h2 : a (time + 2) = a (time + 1) + (time + 2) := by
    have hstep := a_succ_of_not_canSubtract hmin.followup_forced
    have heq : time + 1 + 1 = time + 2 := by omega
    simpa [heq] using hstep
  omega

/-- `subSum` remains constant across both forced addition steps. -/
theorem tail_minimum_followup_subSum
    {target start time firstTime : Nat}
    (hmin : PermanentTailMinimumCertificate target start time firstTime) :
    subSum (time + 2) = subSum time := by
  have h1 := tail_minimum_first_subSum hmin
  have heq : time + 1 + 1 = time + 2 := by omega
  have hsucc := subSum_succ (time + 1)
  rw [heq] at hsucc
  rw [hsucc, if_neg hmin.followup_forced]
  omega

/-- `subCount` remains constant across both forced addition steps. -/
theorem tail_minimum_followup_subCount
    {target start time firstTime : Nat}
    (hmin : PermanentTailMinimumCertificate target start time firstTime) :
    subCount (time + 2) = subCount time := by
  have h1 := tail_minimum_first_subCount hmin
  have heq : time + 1 + 1 = time + 2 := by omega
  have hsucc := subCount_succ (time + 1)
  rw [heq] at hsucc
  rw [hsucc, if_neg hmin.followup_forced]
  omega

/-- The ledger balance at `time + 1` with unshifted `subSum time`. -/
theorem tail_minimum_first_ledger_identity
    {target start time firstTime : Nat}
    (hmin : PermanentTailMinimumCertificate target start time firstTime) :
    a (time + 1) + 2 * subSum time = upperTri (time + 1) := by
  have hledger := ledger_identity (time + 1)
  have hsub := tail_minimum_first_subSum hmin
  rw [hsub] at hledger
  exact hledger

/-- The ledger balance at `time + 2` with unshifted `subSum time`. -/
theorem tail_minimum_followup_ledger_identity
    {target start time firstTime : Nat}
    (hmin : PermanentTailMinimumCertificate target start time firstTime) :
    a (time + 2) + 2 * subSum time = upperTri (time + 2) := by
  have hledger := ledger_identity (time + 2)
  have hsub := tail_minimum_followup_subSum hmin
  rw [hsub] at hledger
  exact hledger

/-- The two forced additions lift the orbit strictly into quotient band `q ≥ 2`. -/
theorem tail_minimum_followup_gt_twice_time
    {target start time firstTime : Nat}
    (hmin : PermanentTailMinimumCertificate target start time firstTime) :
    2 * (time + 2) < a (time + 2) := by
  have hval := tail_minimum_followup_value hmin
  have htarget_lt := hmin.target_lt_predecessor
  have : 2 ≤ a time := by omega
  omega

/-- In canonical quotient/remainder coordinates, the quotient at `time + 2` is at least 2. -/
theorem tail_minimum_followup_quotient_ge_two
    {target start time firstTime q2 r2 : Nat}
    (hmin : PermanentTailMinimumCertificate target start time firstTime)
    (hcoord : CoordinatesAt (time + 2) q2 r2) :
    2 ≤ q2 := by
  have hgt := tail_minimum_followup_gt_twice_time hmin
  have heqn := hcoord.eqn
  have hrem := hcoord.remainder_lt
  by_cases hq : q2 ≤ 1
  · have hprod : (time + 2) * q2 ≤ (time + 2) * 1 := Nat.mul_le_mul_left (time + 2) hq
    omega
  · omega

/-- Step `time + 3` is either an addition or a subtraction. -/
theorem tail_minimum_step3_cases
    {target start time firstTime : Nat}
    (hmin : PermanentTailMinimumCertificate target start time firstTime) :
    (¬ CanSubtract (time + 3) (stateAt (time + 2)) ∧
      a (time + 3) = a time + 3 * time + 6) ∨
    (CanSubtract (time + 3) (stateAt (time + 2)) ∧
      a (time + 3) = a time + time) := by
  have hval2 := tail_minimum_followup_value hmin
  have h3 : time + 2 + 1 = time + 3 := by omega
  by_cases hcan : CanSubtract (time + 3) (stateAt (time + 2))
  · right
    have hstep := a_succ_of_canSubtract hcan
    rw [h3] at hstep
    refine ⟨hcan, by omega⟩
  · left
    have hstep := a_succ_of_not_canSubtract hcan
    rw [h3] at hstep
    refine ⟨hcan, by omega⟩

/-- In both cases, the value at `time + 3` strictly exceeds `a time`. -/
theorem tail_minimum_step3_gt_minimum
    {target start time firstTime : Nat}
    (hmin : PermanentTailMinimumCertificate target start time firstTime)
    (htime : 0 < time) :
    a time < a (time + 3) := by
  rcases tail_minimum_step3_cases hmin with ⟨_, h⟩ | ⟨_, h⟩ <;> omega

/-- If step `time + 3` is a subtraction, step `time + 4` is forced to add
to preserve the tail minimum. -/
theorem tail_minimum_step3_subtraction_forces_step4_addition
    {target start time firstTime : Nat}
    (hmin : PermanentTailMinimumCertificate target start time firstTime)
    (hsub3 : CanSubtract (time + 3) (stateAt (time + 2))) :
    ¬ CanSubtract (time + 4) (stateAt (time + 3)) := by
  intro hcan4
  have hval2 := tail_minimum_followup_value hmin
  have h3 : time + 2 + 1 = time + 3 := by omega
  have h4 : time + 3 + 1 = time + 4 := by omega
  have hstep3 := a_succ_of_canSubtract hsub3
  rw [h3] at hstep3
  have hval3 : a (time + 3) = a time + time := by omega
  have hstep4 := a_succ_of_canSubtract hcan4
  rw [h4] at hstep4
  have hcan4_pos : time + 4 < a (time + 3) := hcan4.1
  have hfour_lt : 4 < a time := by omega
  have hval4_eq : a (time + 4) = a time - 4 := by omega
  have htime4 : start ≤ time + 4 := by
    have hstart := hmin.minimum.start_le_time
    omega
  have hmin4 := hmin.minimum.minimal (time + 4) htime4
  omega

/-- Step `time` is an addition, OR step `time + 3` is a forced addition. -/
theorem tail_minimum_step_before_addition_or_step3_addition
    {target start time firstTime : Nat}
    (hmin : PermanentTailMinimumCertificate target start time firstTime)
    (htime : 0 < time) :
    (¬ CanSubtract time (stateAt (time - 1))) ∨
    (¬ CanSubtract (time + 3) (stateAt (time + 2))) := by
  by_cases hsub : CanSubtract time (stateAt (time - 1))
  · right
    let n := time - 1
    have hn1 : n + 1 = time := by omega
    have hn2 : n + 2 = time + 1 := by omega
    have hn3 : n + 3 = time + 2 := by omega
    have hn4 : n + 4 = time + 3 := by omega
    have hsub' : CanSubtract (n + 1) (stateAt n) := by
      simpa [hn1] using hsub
    have hadd1' : ¬ CanSubtract (n + 2) (stateAt (n + 1)) := by
      simpa [hn1, hn2] using hmin.first_forced
    have hadd2' : ¬ CanSubtract (n + 3) (stateAt (n + 2)) := by
      simpa [hn2, hn3] using hmin.followup_forced
    have hadd3' := double_forcedAddition_extends hsub' hadd1' hadd2'
    simpa [hn3, hn4] using hadd3'
  · left
    exact hsub

/-- Three consecutive additions unconditionally occur around the tail minimum. -/
theorem tail_minimum_forces_three_consecutive_additions
    {target start time firstTime : Nat}
    (hmin : PermanentTailMinimumCertificate target start time firstTime)
    (htime : 0 < time) :
    ∃ t : Int,
      (t = ((time - 1 : Nat) : Int) ∨ t = (time : Int)) ∧
      canonicalSign t = true ∧
      canonicalSign (t + 1) = true ∧
      canonicalSign (t + 2) = true := by
  rcases tail_minimum_step_before_addition_or_step3_addition hmin htime with
    hbefore | hafter
  · refine ⟨((time - 1 : Nat) : Int), Or.inl rfl, ?_, ?_, ?_⟩
    · rw [canonicalSign_nat]
      have : time - 1 + 1 = time := by omega
      simpa [this] using hbefore
    · have h1 : ((time - 1 : Nat) : Int) + 1 = (time : Int) := by omega
      rw [h1]
      exact tail_minimum_first_canonicalSign hmin
    · have h2 : ((time - 1 : Nat) : Int) + 2 = ((time + 1 : Nat) : Int) := by omega
      rw [h2]
      exact tail_minimum_followup_canonicalSign hmin
  · refine ⟨(time : Int), Or.inr rfl, ?_, ?_, ?_⟩
    · exact tail_minimum_first_canonicalSign hmin
    · have h1 : (time : Int) + 1 = ((time + 1 : Nat) : Int) := by omega
      rw [h1]
      exact tail_minimum_followup_canonicalSign hmin
    · have h2 : (time : Int) + 2 = ((time + 2 : Nat) : Int) := by omega
      rw [h2]
      rw [canonicalSign_nat]
      have : time + 2 + 1 = time + 3 := by omega
      simpa [this] using hafter

/-- Every canonical tail minimum unconditionally forces at least one unsupplied addition. -/
theorem tail_minimum_forces_unsupplied_addition
    {target start time firstTime : Nat}
    (hmin : PermanentTailMinimumCertificate target start time firstTime)
    (htime : 0 < time) :
    ∃ t : Int,
      (t = ((time - 1 : Nat) : Int) ∨ t = (time : Int)) ∧
      1 ≤ unsuppliedCount canonicalSign t 3 := by
  rcases tail_minimum_forces_three_consecutive_additions hmin htime with
    ⟨t, hor, h0, h1, h2⟩
  refine ⟨t, hor, ?_⟩
  exact three_consecutive_additions_unsupplied canonicalSign t h0 h1 h2

/-- Pattern exclusion at the tail minimum:
A fully supplied regime (`unsuppliedCount = 0`) cannot hold at the tail minimum. -/
theorem tail_minimum_incompatible_with_all_supplied
    {target start time firstTime : Nat}
    (hmin : PermanentTailMinimumCertificate target start time firstTime)
    (htime : 0 < time) :
    ¬ (unsuppliedCount canonicalSign ((time - 1 : Nat) : Int) 3 = 0 ∧
       unsuppliedCount canonicalSign (time : Int) 3 = 0) := by
  rcases tail_minimum_forces_unsupplied_addition hmin htime with ⟨t, hor, hpos⟩
  rcases hor with rfl | rfl
  · intro ⟨hzero, _⟩
    omega
  · intro ⟨_, hzero⟩
    omega

/-- A hypothetical least missing target forces an unsupplied addition deficit
in the ledger corridor at its certified tail minimum. -/
theorem least_missing_tail_ledger_unsupplied_deficit
    {target : Nat} (h : LeastMissingTarget target) :
    ∃ start time firstTime q r,
      ∃ t : Int,
        MissingStrictAboveTail target start ∧
        PermanentTailMinimumCertificate target start time firstTime ∧
        CoordinatesAt time q r ∧
        q ≤ 1 ∧
        2 * subSum time + (target + 2) ≤ upperTri time ∧
        upperTri time < 2 * subSum time + 2 * time ∧
        (t = ((time - 1 : Nat) : Int) ∨ t = (time : Int)) ∧
        1 ≤ unsuppliedCount canonicalSign t 3 := by
  rcases h.exists_leastTailLedgerMinimum with
    ⟨start, time, firstTime, q, r, htail, _hleast, hmin,
     hcoord, _htargetMin, _hminUpper, _hminTwice,
     hq, _hpot, hledgLower, hledgUpper⟩
  have hstartPos := missingStrictAboveTail_pos htail
  have htimePos : 0 < time :=
    Nat.lt_of_lt_of_le hstartPos hmin.minimum.start_le_time
  rcases tail_minimum_forces_unsupplied_addition hmin htimePos with
    ⟨t, hor, hdef⟩
  exact ⟨start, time, firstTime, q, r, t,
    htail, hmin, hcoord, hq, hledgLower, hledgUpper, hor, hdef⟩

end Recaman
