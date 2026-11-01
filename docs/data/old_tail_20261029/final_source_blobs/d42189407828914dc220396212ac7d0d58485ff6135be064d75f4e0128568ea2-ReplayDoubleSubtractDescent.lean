import Recaman.ReplayWitnessDescent

namespace Recaman

noncomputable section

/-! # The double-subtraction branch of the minimum predecessor

The witnessed follow-up dichotomy has two branches.  The blocked branch was
settled separately: it yields one edge of the well-founded earlier-and-smaller
order and, as a by-product, the separation `target + 2 < a m` between the
missing target and the tail minimum.  This module works out the other branch,
where the minimum predecessor subtracts twice in a row.

Two consecutive legal subtractions out of a first occurrence pin the next two
orbit values exactly and make both of them fresh first occurrences.  Writing
`M` for the tail minimum and `f` for the first occurrence of the minimum
predecessor `M - 1`, the branch gives

* `a (f + 1) = M - f - 2` and `a (f + 2) = M - 2 * f - 4`, both fresh,
* the clock bound `2 * f + 4 < M`, hence the exact identity
  `a (f + 2) + (2 * f + 4) = M`,
* `f + 2 < tailStart`, because a value strictly below the tail minimum cannot
  be produced at or after the tail start.

So the branch does descend, and much faster than the blocked branch: the value
drops by `2 * f + 3` in two steps.  What it does not do is descend in *time*.
Both new occurrences are first occurrences at times `f + 1` and `f + 2`, which
are strictly *later* than `f`, so there is no earlier-and-smaller edge here —
the branch runs in the opposite direction to the witness descent.

The separation `target + 2 < M` also fails to transport, and the reason is
arithmetic rather than structural.  That separation needs an actual occurrence
of the value `M - 2`; the blocked branch produced one because its forced
addition makes `M - 2` the very next subtraction candidate.  The two values
this branch produces undershoot `M - 2` by `f` and by `2 * f + 2`
respectively, and `0 < f` holds here, so neither can serve as the witness.
`doubleSubtract_values_below_predecessorGap` records that undershoot as a
theorem, and `tailMinimum_gap_of_attainment` isolates the exact residual
obligation: any occurrence at all of `M - 2` upgrades the separation to an
unconditional one.

The branch itself survives, and the reason is visible in the times.  The
replay corridor pins `f + 2 < target`, which sharpens the clock bound on the
minimum predecessor to `f + 3 < M - 1` and gives the unconditional separation
`f + 4 < M`; but every time the branch talks about — `f`, `f + 1`, `f + 2` —
lies strictly before `tailStart`, and before the tail start the certificate
imposes no lower bound whatsoever on the orbit.  The only two global hooks
reaching into that region are the identity `a f = M - 1` and the missing
target, and both are already spent.  So the elimination of this branch cannot
come from the tail; it has to come from a constraint on the pre-tail region,
which the discharge certificate currently does not carry.
-/

/-- Two consecutive legal subtractions out of a first occurrence. -/
structure DoubleSubtractStep (value time : Nat) : Prop where
  first : FirstAt a value time
  subtract_one : CanSubtract (time + 1) (stateAt time)
  subtract_two : CanSubtract (time + 2) (stateAt (time + 1))

namespace DoubleSubtractStep

variable {value time : Nat}

/-- The recorded value is the orbit value at the recorded time. -/
theorem value_eq (h : DoubleSubtractStep value time) :
    a time = value := h.first.1

/-- The first subtraction lands exactly one clock below the value. -/
theorem first_value (h : DoubleSubtractStep value time) :
    a (time + 1) = value - (time + 1) := by
  have hstep := a_succ_of_canSubtract h.subtract_one
  have hvalue : a time = value := h.first.1
  omega

/-- The second subtraction lands two clocks below again. -/
theorem second_value (h : DoubleSubtractStep value time) :
    a (time + 2) = value - (time + 1) - (time + 2) := by
  have hfirst := h.first_value
  have hstep : a (time + 1 + 1) = a (time + 1) - (time + 1 + 1) :=
    a_succ_of_canSubtract (n := time + 1) h.subtract_two
  have hstep' : a (time + 2) = a (time + 1) - (time + 2) := by
    simpa using hstep
  omega

/-- Both subtractions must stay positive, so the value clears twice its clock
by three. -/
theorem clock_bound (h : DoubleSubtractStep value time) :
    2 * time + 3 < value := by
  have hone : time + 1 < (stateAt time).value := h.subtract_one.1
  have hone' : (stateAt time).value = a time := rfl
  have hvalue : a time = value := h.first.1
  have htwo : time + 2 < (stateAt (time + 1)).value := h.subtract_two.1
  have htwo' : (stateAt (time + 1)).value = a (time + 1) := rfl
  have hfirst := h.first_value
  omega

/-- The branch cannot start at time zero. -/
theorem time_pos (h : DoubleSubtractStep value time) : 0 < time := by
  have hvalue : a time = value := h.first.1
  have hclock := h.clock_bound
  by_cases hzero : time = 0
  · rw [hzero] at hvalue
    have hbase : a 0 = 0 := rfl
    omega
  · omega

/-- The landing value of the double subtraction is positive. -/
theorem second_pos (h : DoubleSubtractStep value time) :
    0 < a (time + 2) := by
  have hsecond := h.second_value
  have hclock := h.clock_bound
  omega

/-- Two steps drop the value by exactly twice the clock plus three. -/
theorem exact_drop (h : DoubleSubtractStep value time) :
    a (time + 2) + (2 * time + 3) = value := by
  have hsecond := h.second_value
  have hclock := h.clock_bound
  omega

/-- Both landings are strictly below the starting value, in the right
order. -/
theorem strict_drop (h : DoubleSubtractStep value time) :
    a (time + 2) < a (time + 1) ∧ a (time + 1) < value := by
  have hfirst := h.first_value
  have hsecond := h.second_value
  have hclock := h.clock_bound
  exact ⟨by omega, by omega⟩

/-- A legal subtraction always lands fresh, so the first landing is a first
occurrence. -/
theorem first_fresh (h : DoubleSubtractStep value time) :
    FirstAt a (a (time + 1)) (time + 1) :=
  firstAt_succ_of_canSubtract h.subtract_one

/-- The second landing is a first occurrence as well. -/
theorem second_fresh (h : DoubleSubtractStep value time) :
    FirstAt a (a (time + 2)) (time + 2) :=
  firstAt_succ_of_canSubtract (n := time + 1) h.subtract_two

/-- Both landings occur strictly after the starting first occurrence, so
neither is an edge of the earlier-and-smaller order: this branch descends in
value but ascends in time, the opposite direction to the witness descent. -/
theorem no_earlierSmaller_landings (_h : DoubleSubtractStep value time) :
    ¬ EarlierSmaller ⟨a (time + 1), time + 1⟩ ⟨value, time⟩ ∧
      ¬ EarlierSmaller ⟨a (time + 2), time + 2⟩ ⟨value, time⟩ := by
  constructor
  · intro hedge
    have hlt : time + 1 < time := hedge.2
    omega
  · intro hedge
    have hlt : time + 2 < time := hedge.2
    omega

end DoubleSubtractStep

namespace TerminalExactDischargeReplayCertificate

variable {target start : Nat} {parent : PhaseSearchNode}
variable {source : PermanentTailDischargeReturnCertificate target start parent}

/-- The replay corridor pins the minimum predecessor clock strictly below the
target: the first occurrence precedes the downcross, the downcross precedes
the old crossing, and the old crossing clock clears the target by two. -/
theorem minimum_predecessor_clock_below_target
    (r : TerminalExactDischargeReplayCertificate source) :
    source.historicalFirstTime + 2 < target := by
  have hfd := source.downcross.horizon_le_time
  have helig := r.eligible
  have htime := r.time_eq
  have hlt := r.crossingTime_lt_target
  omega

/-- Sharpened form of the clock bound on the minimum predecessor value: the
corridor bound routes through the target, gaining two over the bound that
routes through the crossing alone. -/
theorem minimum_predecessor_value_above_clock_sharp
    (r : TerminalExactDischargeReplayCertificate source) :
    source.historicalFirstTime + 3 < a source.historicalFirstTime := by
  have hclock := r.minimum_predecessor_clock_below_target
  have hp1 : a source.historicalFirstTime =
      a source.historicalMinimumTime - 1 :=
    source.historical_minimum.predecessor_first.1
  have htgt := source.historical_minimum.target_lt_predecessor
  omega

/-- Unconditional separation between the tail minimum and the minimum
predecessor clock, valid in both branches of the follow-up dichotomy. -/
theorem tailMinimum_above_clock
    (r : TerminalExactDischargeReplayCertificate source) :
    source.historicalFirstTime + 4 < a source.historicalMinimumTime := by
  have hsharp := r.minimum_predecessor_value_above_clock_sharp
  have hp1 : a source.historicalFirstTime =
      a source.historicalMinimumTime - 1 :=
    source.historical_minimum.predecessor_first.1
  have hthree := r.tailMinimum_ge_three
  omega

/-- In the double-subtraction branch the minimum predecessor is a
double-subtraction step in the sense of this module. -/
theorem minimum_predecessor_doubleSubtract
    (_r : TerminalExactDischargeReplayCertificate source)
    (hsub1 : CanSubtract (source.historicalFirstTime + 1)
      (stateAt source.historicalFirstTime))
    (hsub2 : CanSubtract (source.historicalFirstTime + 2)
      (stateAt (source.historicalFirstTime + 1))) :
    DoubleSubtractStep (a source.historicalFirstTime)
      source.historicalFirstTime := by
  refine ⟨?_, hsub1, hsub2⟩
  have hpred := source.historical_minimum.predecessor_first
  have hp1 : a source.historicalFirstTime =
      a source.historicalMinimumTime - 1 := hpred.1
  rw [hp1]
  exact hpred

/-- The tail minimum clears twice the predecessor clock by four. -/
theorem doubleSubtract_clock_bound
    (r : TerminalExactDischargeReplayCertificate source)
    (hsub1 : CanSubtract (source.historicalFirstTime + 1)
      (stateAt source.historicalFirstTime))
    (hsub2 : CanSubtract (source.historicalFirstTime + 2)
      (stateAt (source.historicalFirstTime + 1))) :
    2 * source.historicalFirstTime + 4 <
      a source.historicalMinimumTime := by
  have hd := r.minimum_predecessor_doubleSubtract hsub1 hsub2
  have hclock := hd.clock_bound
  have hp1 : a source.historicalFirstTime =
      a source.historicalMinimumTime - 1 :=
    source.historical_minimum.predecessor_first.1
  have hthree := r.tailMinimum_ge_three
  omega

/-- The double subtraction lands an exact distance below the tail minimum. -/
theorem doubleSubtract_exact_gap
    (r : TerminalExactDischargeReplayCertificate source)
    (hsub1 : CanSubtract (source.historicalFirstTime + 1)
      (stateAt source.historicalFirstTime))
    (hsub2 : CanSubtract (source.historicalFirstTime + 2)
      (stateAt (source.historicalFirstTime + 1))) :
    a (source.historicalFirstTime + 2) +
        (2 * source.historicalFirstTime + 4) =
      a source.historicalMinimumTime := by
  have hd := r.minimum_predecessor_doubleSubtract hsub1 hsub2
  have hdrop := hd.exact_drop
  have hclock := hd.clock_bound
  have hp1 : a source.historicalFirstTime =
      a source.historicalMinimumTime - 1 :=
    source.historical_minimum.predecessor_first.1
  have hthree := r.tailMinimum_ge_three
  omega

/-- Both landings stay strictly below the tail minimum. -/
theorem doubleSubtract_below_tailMinimum
    (r : TerminalExactDischargeReplayCertificate source)
    (hsub1 : CanSubtract (source.historicalFirstTime + 1)
      (stateAt source.historicalFirstTime))
    (hsub2 : CanSubtract (source.historicalFirstTime + 2)
      (stateAt (source.historicalFirstTime + 1))) :
    a (source.historicalFirstTime + 1) < a source.historicalMinimumTime ∧
      a (source.historicalFirstTime + 2) <
        a source.historicalMinimumTime := by
  have hd := r.minimum_predecessor_doubleSubtract hsub1 hsub2
  have hfirst := hd.first_value
  have hsecond := hd.second_value
  have hclock := hd.clock_bound
  have hp1 : a source.historicalFirstTime =
      a source.historicalMinimumTime - 1 :=
    source.historical_minimum.predecessor_first.1
  have hthree := r.tailMinimum_ge_three
  exact ⟨by omega, by omega⟩

/-- A value strictly below the tail minimum cannot be produced at or after the
tail start, so the whole double subtraction happens before the permanent
tail. -/
theorem doubleSubtract_before_tailStart
    (r : TerminalExactDischargeReplayCertificate source)
    (hsub1 : CanSubtract (source.historicalFirstTime + 1)
      (stateAt source.historicalFirstTime))
    (hsub2 : CanSubtract (source.historicalFirstTime + 2)
      (stateAt (source.historicalFirstTime + 1))) :
    source.historicalFirstTime + 2 < source.tailStart := by
  have hbelow := r.doubleSubtract_below_tailMinimum hsub1 hsub2
  by_cases hbefore : source.historicalFirstTime + 2 < source.tailStart
  · exact hbefore
  · have hle : source.tailStart ≤ source.historicalFirstTime + 2 := by omega
    have hmin := source.historical_minimum.minimum.minimal
      (source.historicalFirstTime + 2) hle
    omega

/-- Neither landing can recur inside the permanent tail. -/
theorem doubleSubtract_landings_off_tail
    (r : TerminalExactDischargeReplayCertificate source)
    (hsub1 : CanSubtract (source.historicalFirstTime + 1)
      (stateAt source.historicalFirstTime))
    (hsub2 : CanSubtract (source.historicalFirstTime + 2)
      (stateAt (source.historicalFirstTime + 1)))
    (time : Nat) (htime : source.tailStart ≤ time) :
    a time ≠ a (source.historicalFirstTime + 1) ∧
      a time ≠ a (source.historicalFirstTime + 2) := by
  have hbelow := r.doubleSubtract_below_tailMinimum hsub1 hsub2
  have hmin := source.historical_minimum.minimum.minimal time htime
  exact ⟨by omega, by omega⟩

/-- Both landings are genuinely attained, hence differ from the missing
target. -/
theorem doubleSubtract_landings_ne_target
    (_r : TerminalExactDischargeReplayCertificate source)
    (_hsub1 : CanSubtract (source.historicalFirstTime + 1)
      (stateAt source.historicalFirstTime))
    (_hsub2 : CanSubtract (source.historicalFirstTime + 2)
      (stateAt (source.historicalFirstTime + 1))) :
    a (source.historicalFirstTime + 1) ≠ target ∧
      a (source.historicalFirstTime + 2) ≠ target := by
  have hmissing := source.historical_tail.target_missing
  exact ⟨fun heq => hmissing ⟨source.historicalFirstTime + 1, heq⟩,
    fun heq => hmissing ⟨source.historicalFirstTime + 2, heq⟩⟩

/-- The precise obstruction to reproducing the blocked branch's separation:
both landings undershoot the value two below the tail minimum, by `f` and by
`2 * f + 2` respectively, and the predecessor clock is positive.  Hence
neither landing can witness that `a m - 2` is attained. -/
theorem doubleSubtract_values_below_predecessorGap
    (r : TerminalExactDischargeReplayCertificate source)
    (hsub1 : CanSubtract (source.historicalFirstTime + 1)
      (stateAt source.historicalFirstTime))
    (hsub2 : CanSubtract (source.historicalFirstTime + 2)
      (stateAt (source.historicalFirstTime + 1))) :
    0 < source.historicalFirstTime ∧
      a (source.historicalFirstTime + 1) +
          source.historicalFirstTime =
        a source.historicalMinimumTime - 2 ∧
      a (source.historicalFirstTime + 2) +
          (2 * source.historicalFirstTime + 2) =
        a source.historicalMinimumTime - 2 := by
  have hd := r.minimum_predecessor_doubleSubtract hsub1 hsub2
  have hpos := hd.time_pos
  have hfirst := hd.first_value
  have hsecond := hd.second_value
  have hclock := hd.clock_bound
  have hp1 : a source.historicalFirstTime =
      a source.historicalMinimumTime - 1 :=
    source.historical_minimum.predecessor_first.1
  have hthree := r.tailMinimum_ge_three
  exact ⟨hpos, by omega, by omega⟩

/-- Residual obligation for an unconditional separation: a single occurrence
anywhere of the value two below the tail minimum already forces the target to
sit at least three below it.  The blocked branch supplies such an occurrence;
the double-subtraction branch does not. -/
theorem tailMinimum_gap_of_attainment
    (r : TerminalExactDischargeReplayCertificate source)
    (hattained : ∃ time, a time = a source.historicalMinimumTime - 2) :
    target + 2 < a source.historicalMinimumTime := by
  have hthree := r.tailMinimum_ge_three
  have htgt := source.historical_minimum.target_lt_predecessor
  have hmissing := source.historical_tail.target_missing
  rcases hattained with ⟨time, hvalue⟩
  by_cases hgap : target + 2 < a source.historicalMinimumTime
  · exact hgap
  · exact False.elim (hmissing ⟨time, by omega⟩)

/-- Refined follow-up dichotomy, with each branch's yield attached.  The
separation `target + 2 < a m` appears only on the blocked side; the
double-subtraction side pays in a much larger value drop, an exact gap to the
tail minimum, and a stronger bound on where the permanent tail can start. -/
theorem minimum_predecessor_followUp_refined
    (r : TerminalExactDischargeReplayCertificate source)
    (hvalue : a source.historicalFirstTime + 1 <
      source.historicalMinimumTime)
    (horder : source.historicalFirstTime + 2 <
      source.historicalMinimumTime) :
    (BlockedFirstOccurrence (a source.historicalFirstTime)
        source.historicalFirstTime ∧
      target + 2 < a source.historicalMinimumTime) ∨
    (DoubleSubtractStep (a source.historicalFirstTime)
        source.historicalFirstTime ∧
      source.historicalFirstTime + 2 < source.tailStart ∧
      2 * source.historicalFirstTime + 4 <
        a source.historicalMinimumTime ∧
      a (source.historicalFirstTime + 2) +
          (2 * source.historicalFirstTime + 4) =
        a source.historicalMinimumTime) := by
  rcases r.minimum_predecessor_followUp hvalue horder with
    ⟨_hseen, hblocked⟩ | ⟨hsub1, hsub2⟩
  · exact Or.inl ⟨r.minimum_predecessor_blocked hblocked,
      r.tailMinimum_gap_of_blocked hblocked⟩
  · exact Or.inr ⟨r.minimum_predecessor_doubleSubtract hsub1 hsub2,
      r.doubleSubtract_before_tailStart hsub1 hsub2,
      r.doubleSubtract_clock_bound hsub1 hsub2,
      r.doubleSubtract_exact_gap hsub1 hsub2⟩

/-- In the double-subtraction branch the tail minimum has to clear the
predecessor clock twice over, roughly doubling the unconditional bound. -/
theorem doubleSubtract_tailMinimum_above_twice_clock
    (r : TerminalExactDischargeReplayCertificate source)
    (hsub1 : CanSubtract (source.historicalFirstTime + 1)
      (stateAt source.historicalFirstTime))
    (hsub2 : CanSubtract (source.historicalFirstTime + 2)
      (stateAt (source.historicalFirstTime + 1))) :
    2 * source.historicalFirstTime + 4 <
        a source.historicalMinimumTime ∧
      source.historicalFirstTime + 4 <
        a source.historicalMinimumTime := by
  exact ⟨r.doubleSubtract_clock_bound hsub1 hsub2, r.tailMinimum_above_clock⟩

end TerminalExactDischargeReplayCertificate

end

end Recaman
