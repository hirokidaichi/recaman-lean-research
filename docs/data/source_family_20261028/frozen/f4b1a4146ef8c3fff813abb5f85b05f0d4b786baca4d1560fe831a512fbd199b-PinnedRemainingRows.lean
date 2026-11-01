import Recaman.PinnedMiddleRow
import Recaman.TailStartHorizonBound

namespace Recaman

noncomputable section

/-! # The two backward rows which survive

`PinnedBackwardStep.backward_trichotomy` left three shapes for the two steps
before the pinned predecessor clock, and `PinnedMiddleRow` removed the middle
one.  What remains is the dichotomy "both steps subtract" or "both steps add".

This module records what the counting tools still say about each side.

The subtracting row stores `a (clock - 1) = target + clock + 1` and
`a (clock - 2) = target + 2 * clock`, both comfortably at or above
`target + 2`.  So the two idle pre-tail times which killed the middle row are
present here as well and the refined separation `target + 3 <= tailStart`
holds verbatim.  What is missing on this side is a target for late
recurrence: the stored value `target + 2 * clock` is not the tail minimum
`target + 2`, so the separation improves the pre-tail bound without closing
the row.

The adding row is the genuinely hard one.  Both stored values,
`a (clock - 1) = target + 1 - clock` and `a (clock - 2) = target + 2 - 2 *
clock`, lie strictly below the target, so neither time is idle at any level
the counting argument can use, and the pre-tail bound stays at
`target < tailStart`.  The obstruction is recorded below as an explicit
statement about the row rather than left implicit: the row places two more
sub-target values on pre-tail times, which is exactly the wrong direction for
the pigeonhole.
-/

namespace TerminalExactDischargeReplayCertificate

variable {target start : Nat} {parent : PhaseSearchNode}
variable {source : PermanentTailDischargeReturnCertificate target start parent}

/-- The pinned predecessor value sits in the pre-tail history at level
`target + 1`.  This is the shared input of every refined separation below. -/
theorem pinned_predecessor_covered
    (r : TerminalExactDischargeReplayCertificate source)
    (hminimum : a source.historicalMinimumTime = target + 2) :
    (target + 1) ∈ valuesThrough (source.tailStart - 1) := by
  have hpred : a source.historicalFirstTime =
      a source.historicalMinimumTime - 1 :=
    source.historical_minimum.predecessor_first.1
  have hvalue : a source.historicalFirstTime = target + 1 := by omega
  have hmem := r.predecessor_covered_preTail
  rw [← hvalue]
  exact hmem

/-- Refined separation for the subtracting row.  Its two backward values are
both at or above `target + 2`, so the two idle pre-tail times are available
and the tail start clears the target by three. -/
theorem firstRow_target_add_three_le_tailStart
    (r : TerminalExactDischargeReplayCertificate source)
    (hminimum : a source.historicalMinimumTime = target + 2)
    {base : Nat} (hclock : source.historicalFirstTime = base + 2)
    (hp : PinnedTailMinimumConfiguration target (base + 2))
    (hprevious : a (base + 1) = target + base + 3)
    (hsecond : a base = target + 2 * base + 4) :
    target + 3 ≤ source.tailStart := by
  have hbase : 0 < base := by
    have hthree := hp.three_le_clock
    omega
  have hbefore := source.historical_minimum.firstTime_before_tail
  exact target_add_three_le_tailStart
    (target := target) (tailStart := source.tailStart)
    (t1 := base) (t2 := base + 1)
    r.belowTarget_covered_preTail (r.pinned_predecessor_covered hminimum)
    hbase (by omega) (by omega) (by omega) (by omega)

/-- The adding row keeps both backward values strictly below the target, so
neither of its times is idle at the level the pigeonhole uses.  This is the
exact reason the refined separation does not transport to this side. -/
theorem lastRow_values_below_target
    {base : Nat}
    (hp : PinnedTailMinimumConfiguration target (base + 2))
    (hprevious : a (base + 1) + base + 2 = target + 1)
    (hsecond : a base + 2 * base + 2 = target) :
    a (base + 1) < target ∧ a base < target := by
  have hclock := hp.clock_bound
  exact ⟨by omega, by omega⟩

/-- The adding row forces the step into the clock to be a forced addition,
because a legal subtraction would have raised the previous value instead of
lowering it. -/
theorem lastRow_forced_addition
    {base : Nat}
    (hp : PinnedTailMinimumConfiguration target (base + 2))
    (hprevious : a (base + 1) + base + 2 = target + 1) :
    ¬ CanSubtract (base + 1 + 1) (stateAt (base + 1)) := by
  intro hsub
  have hvalue : a (base + 2) = target + 1 := hp.value_eq
  have hstep : a (base + 1 + 1) = a (base + 1) - (base + 1 + 1) :=
    a_succ_of_canSubtract hsub
  have hpos : base + 1 + 1 < a (base + 1) := hsub.1
  have hstep' : a (base + 2) = a (base + 1) - (base + 2) := by
    simpa using hstep
  omega

/-- Exact residue of the adding row.  The forced addition can only be caused
by a stored value, and the stored value is pinned: `target - 2 * clock + 1`
already occurs at or before `clock - 1`.  Closing this row therefore needs a
statement about that early occurrence, not another pigeonhole. -/
theorem lastRow_blocked_witness
    {base : Nat}
    (hp : PinnedTailMinimumConfiguration target (base + 2))
    (hprevious : a (base + 1) + base + 2 = target + 1) :
    target - 2 * base - 3 ∈ valuesThrough (base + 1) := by
  have hclock := hp.clock_bound
  have hnot := lastRow_forced_addition hp hprevious
  rcases not_canSubtract_cases hnot with hsmall | hseen
  · omega
  · have hrewrite : a (base + 1) - (base + 1 + 1) = target - 2 * base - 3 := by
      omega
    rw [hrewrite] at hseen
    exact hseen

/-- Surviving dichotomy with the pre-tail bound attached where it is
available.  The subtracting row now carries `target + 3 <= tailStart`; the
adding row carries only the two sub-target values which block that argument
and the unrefined bound `target < tailStart`. -/
theorem pinned_backward_dichotomy_with_bound
    (r : TerminalExactDischargeReplayCertificate source)
    (hminimum : a source.historicalMinimumTime = target + 2)
    {base : Nat} (hclock : source.historicalFirstTime = base + 2)
    (hp : PinnedTailMinimumConfiguration target (base + 2)) :
    (a (base + 1) = target + base + 3 ∧
        a base = target + 2 * base + 4 ∧
        target + 3 ≤ source.tailStart) ∨
      (a (base + 1) + base + 2 = target + 1 ∧
        a base + 2 * base + 2 = target ∧
        a (base + 1) < target ∧ a base < target ∧
        target < source.tailStart) := by
  rcases r.pinned_backward_dichotomy hminimum hclock hp with
    ⟨hone, htwo⟩ | ⟨hone, htwo⟩
  · exact Or.inl ⟨hone, htwo,
      r.firstRow_target_add_three_le_tailStart hminimum hclock hp hone htwo⟩
  · have hbelow := lastRow_values_below_target hp hone htwo
    exact Or.inr ⟨hone, htwo, hbelow.1, hbelow.2, r.target_lt_tailStart⟩

/-- What the subtracting row still needs.  The refined separation is already
available there, so the row closes as soon as the value it stores two steps
before the clock is shown to recur at, or to be excluded from, the tail.  The
statement below is the precise late-recurrence hook: it fires at any tail time
exceeding the stored value. -/
theorem firstRow_forbids_late_repeat
    {base m : Nat}
    (hsecond : a base = target + 2 * base + 4)
    (hlate : base < m) (hbig : target + 2 * base + 4 < m) :
    a m ≠ target + 2 * base + 4 := by
  intro hm
  exact value_no_late_recurrence (v := target + 2 * base + 4) (w := base)
    (m := m) hsecond hlate hbig hm

end TerminalExactDischargeReplayCertificate

end

end Recaman
