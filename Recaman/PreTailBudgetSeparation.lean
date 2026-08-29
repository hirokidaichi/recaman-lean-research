import Recaman.ReplayDoubleSubtractDescent

namespace Recaman

/-! # A counting budget for the region before the permanent tail

The discharge certificate constrains the orbit only from the tail start
onwards.  Every attempt to eliminate a replay branch whose data lives strictly
before the tail start therefore stalls for want of a pre-tail constraint.
This module supplies one, by counting rather than by dynamics.

The count is `coveredBelowCount k n`, the number of values below `k` already
present in the history stored at time `n`.  It is the exact complement of the
existing `missingBelowCount`.  Three facts drive everything: one time step
adds at most one new value, a time step whose orbit value is at least `k` adds
none, and the initial history holds a single value.  Together they give the
pigeonhole `coveredBelowCount k n ≤ n + 1`.

Applied to a surviving replay this yields a genuine pre-tail bound.  Every
value below the target is covered, and the tail is strictly above the target,
so all of those values are covered strictly before the tail start; the minimum
predecessor supplies one more covered value above the target at a pre-tail
time.  The pigeonhole then forces `target < tailStart`, a bound that needs no
kernel computation and no clock enumeration, and that holds for every replay.

The module also records what the tail minimum's own local analysis yields
towards an occurrence of the value two below the tail minimum.  The step into
the tail minimum is a subtraction whenever the minimum is reached after the
tail start, which makes the minimum time the first occurrence of the minimum
value; and the blocked step at the minimum yields an occurrence of
`M - (m + 1)`.  Neither reaches `M - 2`: the predecessor witness sits one
above it and the blocked-step witness sits `m - 1 ≥ 1` below it.
-/

/-- Number of values below `k` already present in the history stored at time
`n`.  Exact complement of `missingBelowCount`. -/
def coveredBelowCount : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, n =>
      coveredBelowCount k n +
        if k ∈ valuesThrough n then 1 else 0

@[simp] theorem coveredBelowCount_zero (n : Nat) :
    coveredBelowCount 0 n = 0 := rfl

@[simp] theorem coveredBelowCount_succ (k n : Nat) :
    coveredBelowCount (k + 1) n =
      coveredBelowCount k n +
        if k ∈ valuesThrough n then 1 else 0 := rfl

/-- Covered and missing counts partition the levels below `k`. -/
theorem coveredBelowCount_add_missingBelowCount (n : Nat) :
    ∀ k, coveredBelowCount k n + missingBelowCount k n = k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [coveredBelowCount_succ, missingBelowCount_succ]
      by_cases hmem : k ∈ valuesThrough n
      · simp only [if_pos hmem]
        omega
      · simp only [if_neg hmem]
        omega

/-- The initial history holds a single value. -/
theorem coveredBelowCount_initial : ∀ k, coveredBelowCount k 0 ≤ 1 := by
  intro k
  induction k with
  | zero =>
      show (0 : Nat) ≤ 1
      omega
  | succ k ih =>
      by_cases hk : k = 0
      · subst hk
        have hmem : (0 : Nat) ∈ valuesThrough 0 := by
          simp [valuesThrough, stateAt, initial]
        simp only [coveredBelowCount_succ, if_pos hmem]
        have hz : coveredBelowCount 0 0 = 0 := rfl
        omega
      · have hnot : k ∉ valuesThrough 0 := by
          intro hmem
          have hzero : k = 0 := by
            simpa [valuesThrough, stateAt, initial] using hmem
          exact hk hzero
        simp only [coveredBelowCount_succ, if_neg hnot]
        omega

/-- A time step whose orbit value is not below `k` adds no covered level. -/
theorem coveredBelowCount_step_of_above (n : Nat) :
    ∀ k, k ≤ a (n + 1) →
      coveredBelowCount k (n + 1) ≤ coveredBelowCount k n := by
  intro k
  induction k with
  | zero =>
      intro _
      exact Nat.le_refl _
  | succ k ih =>
      intro hk
      have hih := ih (by omega)
      have hne : k ≠ a (n + 1) := by omega
      have hiff : (k ∈ valuesThrough (n + 1)) ↔ (k ∈ valuesThrough n) := by
        rw [valuesThrough_succ]
        constructor
        · intro hmem
          rcases List.mem_cons.mp hmem with heq | hmem'
          · exact absurd heq hne
          · exact hmem'
        · intro hmem
          exact List.mem_cons.mpr (Or.inr hmem)
      by_cases hmem : k ∈ valuesThrough n
      · have hmem1 : k ∈ valuesThrough (n + 1) := hiff.mpr hmem
        simp only [coveredBelowCount_succ, if_pos hmem, if_pos hmem1]
        omega
      · have hmem1 : k ∉ valuesThrough (n + 1) := fun h => hmem (hiff.mp h)
        simp only [coveredBelowCount_succ, if_neg hmem, if_neg hmem1]
        omega

/-- One time step adds at most one covered level. -/
theorem coveredBelowCount_step_le (n : Nat) :
    ∀ k, coveredBelowCount k (n + 1) ≤ coveredBelowCount k n + 1 := by
  intro k
  induction k with
  | zero =>
      show (0 : Nat) ≤ 0 + 1
      omega
  | succ k ih =>
      by_cases hcase : k = a (n + 1)
      · have hle : coveredBelowCount k (n + 1) ≤ coveredBelowCount k n :=
          coveredBelowCount_step_of_above n k (by omega)
        simp only [coveredBelowCount_succ]
        by_cases hmem : k ∈ valuesThrough n
        · simp only [if_pos hmem]
          have hmem1 : k ∈ valuesThrough (n + 1) :=
            valuesThrough_mono (by omega) hmem
          simp only [if_pos hmem1]
          omega
        · simp only [if_neg hmem]
          by_cases hmem1 : k ∈ valuesThrough (n + 1)
          · simp only [if_pos hmem1]
            omega
          · simp only [if_neg hmem1]
            omega
      · have hne : k ≠ a (n + 1) := hcase
        have hiff : (k ∈ valuesThrough (n + 1)) ↔ (k ∈ valuesThrough n) := by
          rw [valuesThrough_succ]
          constructor
          · intro hmem
            rcases List.mem_cons.mp hmem with heq | hmem'
            · exact absurd heq hne
            · exact hmem'
          · intro hmem
            exact List.mem_cons.mpr (Or.inr hmem)
        by_cases hmem : k ∈ valuesThrough n
        · have hmem1 : k ∈ valuesThrough (n + 1) := hiff.mpr hmem
          simp only [coveredBelowCount_succ, if_pos hmem, if_pos hmem1]
          omega
        · have hmem1 : k ∉ valuesThrough (n + 1) := fun h => hmem (hiff.mp h)
          simp only [coveredBelowCount_succ, if_neg hmem, if_neg hmem1]
          omega

/-- Pigeonhole: by time `n` at most `n + 1` levels can be covered. -/
theorem coveredBelowCount_le_time (k : Nat) :
    ∀ n, coveredBelowCount k n ≤ n + 1 := by
  intro n
  induction n with
  | zero => exact coveredBelowCount_initial k
  | succ n ih =>
      have hstep := coveredBelowCount_step_le n k
      omega

/-- The count is monotone in the level. -/
theorem coveredBelowCount_mono_level {n : Nat} (k : Nat) :
    ∀ k', k ≤ k' → coveredBelowCount k n ≤ coveredBelowCount k' n := by
  intro k'
  induction k' with
  | zero =>
      intro h
      have hzero : k = 0 := by omega
      subst hzero
      exact Nat.le_refl _
  | succ k' ih =>
      intro h
      rcases Nat.eq_or_lt_of_le h with heq | hlt
      · rw [heq]
        exact Nat.le_refl _
      · have hih := ih (by omega)
        simp only [coveredBelowCount_succ]
        by_cases hmem : k' ∈ valuesThrough n
        · simp only [if_pos hmem]
          omega
        · simp only [if_neg hmem]
          omega

/-- Full coverage below `k` makes the count exact. -/
theorem coveredBelowCount_eq_of_covered {n : Nat} :
    ∀ k, (∀ v, v < k → v ∈ valuesThrough n) → coveredBelowCount k n = k := by
  intro k
  induction k with
  | zero =>
      intro _
      rfl
  | succ k ih =>
      intro hcov
      have hih := ih (fun v hv => hcov v (by omega))
      have hmem : k ∈ valuesThrough n := hcov k (by omega)
      simp only [coveredBelowCount_succ, if_pos hmem]
      omega

/-- A stretch of times whose orbit values all clear `k` adds no covered
level. -/
theorem coveredBelowCount_le_of_above {k s : Nat} :
    ∀ n, s ≤ n → (∀ t, s < t → t ≤ n → k ≤ a t) →
      coveredBelowCount k n ≤ coveredBelowCount k s := by
  intro n
  induction n with
  | zero =>
      intro hsn _
      have hzero : s = 0 := by omega
      subst hzero
      exact Nat.le_refl _
  | succ n ih =>
      intro hsn habove
      rcases Nat.eq_or_lt_of_le hsn with heq | hlt
      · rw [heq]
        exact Nat.le_refl _
      · have hstep : coveredBelowCount k (n + 1) ≤ coveredBelowCount k n :=
          coveredBelowCount_step_of_above n k
            (habove (n + 1) (by omega) (by omega))
        exact Nat.le_trans hstep
          (ih (by omega) (fun t ht1 ht2 => habove t ht1 (by omega)))

noncomputable section

namespace TerminalExactDischargeReplayCertificate

variable {target start : Nat} {parent : PhaseSearchNode}
variable {source : PermanentTailDischargeReturnCertificate target start parent}

/-- The permanent tail cannot start at time zero. -/
theorem tailStart_pos
    (_r : TerminalExactDischargeReplayCertificate source) :
    0 < source.tailStart := by
  have hbefore := source.historical_minimum.firstTime_before_tail
  omega

/-- The minimum predecessor's first occurrence is positive. -/
theorem firstTime_pos
    (r : TerminalExactDischargeReplayCertificate source) :
    0 < source.historicalFirstTime := by
  have hp1 : a source.historicalFirstTime =
      a source.historicalMinimumTime - 1 :=
    source.historical_minimum.predecessor_first.1
  have hthree := r.tailMinimum_ge_three
  by_cases hz : source.historicalFirstTime = 0
  · rw [hz] at hp1
    have hbase : a 0 = 0 := rfl
    omega
  · omega

/-- Hence the tail minimum time is at least two. -/
theorem two_le_minimumTime
    (r : TerminalExactDischargeReplayCertificate source) :
    2 ≤ source.historicalMinimumTime := by
  have hpos := r.firstTime_pos
  have hbefore := source.historical_minimum.firstTime_before_tail
  have hle := source.historical_minimum.minimum.start_le_time
  omega

/-- Every value below the target is covered strictly before the tail start:
coverage holds somewhere, and the tail itself is strictly above the target. -/
theorem belowTarget_covered_preTail
    (_r : TerminalExactDischargeReplayCertificate source) :
    ∀ v, v < target → v ∈ valuesThrough (source.tailStart - 1) := by
  intro v hv
  have hcov := source.combined.tail.below_covered v hv
  rcases mem_valuesThrough_iff.mp hcov with ⟨t, hle, hval⟩
  have hlt : t < source.tailStart := by
    by_cases hlt : t < source.tailStart
    · exact hlt
    · have habove := source.historical_tail.strictly_above t (by omega)
      omega
  exact mem_valuesThrough_iff.mpr ⟨t, by omega, hval⟩

/-- The minimum predecessor is covered strictly before the tail start too, and
it lies strictly above the target. -/
theorem predecessor_covered_preTail
    (_r : TerminalExactDischargeReplayCertificate source) :
    a source.historicalFirstTime ∈ valuesThrough (source.tailStart - 1) := by
  have hpred := source.historical_minimum.predecessor_first
  have hbefore := source.historical_minimum.firstTime_before_tail
  exact mem_valuesThrough_iff.mpr
    ⟨source.historicalFirstTime, by omega, rfl⟩

/-- Pre-tail budget separation: the permanent tail cannot start until after
the target.  This is a constraint on the region the discharge certificate
otherwise leaves free, and it uses no orbit computation. -/
theorem target_lt_tailStart
    (r : TerminalExactDischargeReplayCertificate source) :
    target < source.tailStart := by
  have hpos := r.tailStart_pos
  have hcovT : coveredBelowCount target (source.tailStart - 1) = target :=
    coveredBelowCount_eq_of_covered target r.belowTarget_covered_preTail
  have hmemP := r.predecessor_covered_preTail
  have hlt : target < a source.historicalFirstTime := by
    have hp1 : a source.historicalFirstTime =
        a source.historicalMinimumTime - 1 :=
      source.historical_minimum.predecessor_first.1
    have htgt := source.historical_minimum.target_lt_predecessor
    omega
  have hmono := coveredBelowCount_mono_level (n := source.tailStart - 1)
    target (a source.historicalFirstTime) (by omega)
  have hstep : coveredBelowCount (a source.historicalFirstTime + 1)
        (source.tailStart - 1) =
      coveredBelowCount (a source.historicalFirstTime)
        (source.tailStart - 1) + 1 := by
    simp only [coveredBelowCount_succ, if_pos hmemP]
  have hbound := coveredBelowCount_le_time
    (a source.historicalFirstTime + 1) (source.tailStart - 1)
  omega

/-- Values below the tail minimum are confined to pre-tail times, so their
count never exceeds the tail start. -/
theorem coveredBelowCount_tailMinimum_bound
    (r : TerminalExactDischargeReplayCertificate source) (n : Nat) :
    coveredBelowCount (a source.historicalMinimumTime) n ≤
      source.tailStart := by
  have hpos := r.tailStart_pos
  by_cases hsmall : n ≤ source.tailStart - 1
  · have hle := coveredBelowCount_le_time
      (a source.historicalMinimumTime) n
    omega
  · have hge : source.tailStart - 1 ≤ n := by omega
    have hstable :=
      coveredBelowCount_le_of_above
        (k := a source.historicalMinimumTime)
        (s := source.tailStart - 1) n hge
        (fun t ht1 _ =>
          source.historical_minimum.minimum.minimal t (by omega))
    have hle := coveredBelowCount_le_time
      (a source.historicalMinimumTime) (source.tailStart - 1)
    omega

/-- Trichotomy collapse for the separation.  Either the tail minimum clears
the target by three, or the whole replay is pinned into one rigid
configuration: the tail minimum is exactly two above the target, the branch is
forced to be the double subtraction, and the three orbit values around the
minimum predecessor are determined by the target and the predecessor clock
alone. -/
theorem tailMinimum_gap_or_pinned
    (r : TerminalExactDischargeReplayCertificate source)
    (hvalue : a source.historicalFirstTime + 1 <
      source.historicalMinimumTime)
    (horder : source.historicalFirstTime + 2 <
      source.historicalMinimumTime) :
    target + 2 < a source.historicalMinimumTime ∨
      (a source.historicalMinimumTime = target + 2 ∧
        a source.historicalFirstTime = target + 1 ∧
        a (source.historicalFirstTime + 1) =
          target - source.historicalFirstTime ∧
        a (source.historicalFirstTime + 2) =
          target - 2 * source.historicalFirstTime - 2 ∧
        2 * source.historicalFirstTime + 2 < target ∧
        target < source.tailStart) := by
  by_cases hgap : target + 2 < a source.historicalMinimumTime
  · exact Or.inl hgap
  · right
    have hthree := r.tailMinimum_ge_three
    have htgt := source.historical_minimum.target_lt_predecessor
    have hp1 : a source.historicalFirstTime =
        a source.historicalMinimumTime - 1 :=
      source.historical_minimum.predecessor_first.1
    have hpre := r.target_lt_tailStart
    rcases r.minimum_predecessor_followUp_refined hvalue horder with
      ⟨_, hsep⟩ | ⟨hd, _, _, _⟩
    · exact False.elim (hgap hsep)
    · have hfirst := hd.first_value
      have hsecond := hd.second_value
      have hclock := hd.clock_bound
      exact ⟨by omega, by omega, by omega, by omega, by omega, hpre⟩

/-- The step into the tail minimum is a subtraction whenever the minimum is
reached strictly after the tail start: an addition would place a value below
the minimum inside the tail.  Consequently the tail minimum time is the first
occurrence of the tail minimum value. -/
theorem tailMinimum_transition_subtracts
    (r : TerminalExactDischargeReplayCertificate source)
    (hlate : source.tailStart < source.historicalMinimumTime) :
    a (source.historicalMinimumTime - 1) =
        a source.historicalMinimumTime + source.historicalMinimumTime ∧
      FirstAt a (a source.historicalMinimumTime)
        source.historicalMinimumTime := by
  have h2 := r.two_le_minimumTime
  obtain ⟨k, hk⟩ : ∃ k, source.historicalMinimumTime = k + 1 :=
    ⟨source.historicalMinimumTime - 1, by omega⟩
  have hpred_eq : source.historicalMinimumTime - 1 = k := by omega
  have hlate' : source.tailStart ≤ k := by omega
  have hcan : CanSubtract (k + 1) (stateAt k) := by
    by_cases hcan : CanSubtract (k + 1) (stateAt k)
    · exact hcan
    · have hadd := a_succ_of_not_canSubtract hcan
      have hmin := source.historical_minimum.minimum.minimal k hlate'
      rw [hk] at hmin
      omega
  have hsubvalue := a_succ_of_canSubtract hcan
  have hposv : k + 1 < (stateAt k).value := hcan.1
  have hposv' : (stateAt k).value = a k := rfl
  rw [hpred_eq, hk]
  exact ⟨by omega, firstAt_succ_of_canSubtract hcan⟩

/-- The blocked step at the tail minimum yields either a small tail minimum or
an occurrence of the value `M - (m + 1)`. -/
theorem tailMinimum_firstForced_cases
    (_r : TerminalExactDischargeReplayCertificate source) :
    a source.historicalMinimumTime ≤ source.historicalMinimumTime + 1 ∨
      ∃ time, a time = a source.historicalMinimumTime -
        (source.historicalMinimumTime + 1) := by
  rcases not_canSubtract_cases source.historical_minimum.first_forced with
    hsmall | hseen
  · exact Or.inl hsmall
  · rcases mem_valuesThrough_iff.mp hseen with ⟨t, _, hval⟩
    exact Or.inr ⟨t, hval⟩

/-- Precise obstruction for the tail minimum's local analysis: the predecessor
witness sits one above the value two below the tail minimum, and the
blocked-step witness sits at least one below it.  Neither can serve as the
occurrence that `tailMinimum_gap_of_attainment` asks for. -/
theorem tailMinimum_local_witnesses_miss_gap
    (r : TerminalExactDischargeReplayCertificate source)
    (hlarge : source.historicalMinimumTime + 1 <
      a source.historicalMinimumTime) :
    a source.historicalMinimumTime - 2 + 1 =
        a source.historicalMinimumTime - 1 ∧
      a source.historicalMinimumTime -
          (source.historicalMinimumTime + 1) <
        a source.historicalMinimumTime - 2 := by
  have hthree := r.tailMinimum_ge_three
  have h2 := r.two_le_minimumTime
  exact ⟨by omega, by omega⟩

end TerminalExactDischargeReplayCertificate

end

end Recaman
