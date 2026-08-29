import Recaman.PinnedBackwardStep
import Recaman.PreTailBudgetSeparation

namespace Recaman

noncomputable section

/-! # Eliminating the middle backward row of the pinned configuration

`PinnedBackwardStep.backward_trichotomy` leaves three shapes.  The middle one
stores `a (clock - 2) = target + 2`, which is exactly the pinned tail minimum
value, so late recurrence kills it as soon as the tail minimum time exceeds
`target + 2`.  The counting separation of `PreTailBudgetSeparation` only
reaches `target < tailStart`, two short.

The two missing units are supplied by the middle row itself.  The pigeonhole
`coveredBelowCount k n ≤ n + 1` charges one covered level to every time up to
`n`, but a time whose orbit value is at or above `k` covers nothing.  In the
middle row the two times `clock - 1` and `clock - 2` both carry values at or
above `target + 2` and both lie before the tail, so two of the pre-tail times
are idle at that level.  Charging them back gives `target + 3 ≤ tailStart`,
hence `target + 2 < tailStart ≤ minimumTime`, and the row dies.

The counting refinement is proved here in the same elementary style: a
telescoping bound across a time interval, then two applications of the
existing "a step above the level covers nothing" lemma.
-/

/-! ## Pigeonhole with two idle times -/

/-- Telescoping form of the one-step bound: over an interval the covered
count grows by at most one per time. -/
theorem coveredBelowCount_le_shift (k m : Nat) :
    ∀ n, m ≤ n → coveredBelowCount k n ≤ coveredBelowCount k m + (n - m) := by
  intro n
  induction n with
  | zero =>
      intro hm
      have hzero : m = 0 := by omega
      subst hzero
      omega
  | succ n ih =>
      intro hm
      rcases Nat.eq_or_lt_of_le hm with heq | hlt
      · subst heq
        omega
      · have hle : m ≤ n := by omega
        have hih := ih hle
        have hstep := coveredBelowCount_step_le n k
        omega

/-- Pigeonhole with two idle times.  If two distinct positive times at or
before `n` carry orbit values at or above the level, they cover nothing, so
the covered count falls two below the plain bound. -/
theorem coveredBelowCount_two_above {k t1 t2 n : Nat}
    (ht1 : 0 < t1) (ht12 : t1 < t2) (ht2n : t2 ≤ n)
    (ha1 : k ≤ a t1) (ha2 : k ≤ a t2) :
    coveredBelowCount k n + 1 ≤ n := by
  obtain ⟨p1, rfl⟩ : ∃ p, t1 = p + 1 := ⟨t1 - 1, by omega⟩
  obtain ⟨p2, rfl⟩ : ∃ p, t2 = p + 1 := ⟨t2 - 1, by omega⟩
  have hgap : p1 + 1 ≤ p2 := by omega
  have hA : coveredBelowCount k (p1 + 1) ≤ coveredBelowCount k p1 :=
    coveredBelowCount_step_of_above p1 k ha1
  have hB : coveredBelowCount k p1 ≤ p1 + 1 :=
    coveredBelowCount_le_time k p1
  have hC : coveredBelowCount k p2 ≤
      coveredBelowCount k (p1 + 1) + (p2 - (p1 + 1)) :=
    coveredBelowCount_le_shift k (p1 + 1) p2 hgap
  have hD : coveredBelowCount k (p2 + 1) ≤ coveredBelowCount k p2 :=
    coveredBelowCount_step_of_above p2 k ha2
  have hE : coveredBelowCount k n ≤
      coveredBelowCount k (p2 + 1) + (n - (p2 + 1)) :=
    coveredBelowCount_le_shift k (p2 + 1) n ht2n
  omega

/-! ## The refined pre-tail separation -/

/-- Counting separation sharpened by two idle pre-tail times.  All levels
below the target are covered before the tail, the pinned predecessor value
`target + 1` is covered as well, and two pre-tail times sit at or above
`target + 2`.  Those `target + 2` covered levels then need `target + 3`
pre-tail times. -/
theorem target_add_three_le_tailStart
    {target tailStart t1 t2 : Nat}
    (hcover : ∀ v, v < target → v ∈ valuesThrough (tailStart - 1))
    (hpred : (target + 1) ∈ valuesThrough (tailStart - 1))
    (ht1 : 0 < t1) (ht12 : t1 < t2) (ht2 : t2 < tailStart)
    (ha1 : target + 2 ≤ a t1) (ha2 : target + 2 ≤ a t2) :
    target + 3 ≤ tailStart := by
  have hpos : 0 < tailStart := by omega
  have hbelow : coveredBelowCount target (tailStart - 1) = target :=
    coveredBelowCount_eq_of_covered target hcover
  have hmid : coveredBelowCount (target + 1) (tailStart - 1) =
      coveredBelowCount target (tailStart - 1) +
        (if target ∈ valuesThrough (tailStart - 1) then 1 else 0) :=
    coveredBelowCount_succ target (tailStart - 1)
  have hmid' : coveredBelowCount target (tailStart - 1) ≤
      coveredBelowCount (target + 1) (tailStart - 1) := by
    rw [hmid]
    split <;> omega
  have htop : coveredBelowCount (target + 2) (tailStart - 1) =
      coveredBelowCount (target + 1) (tailStart - 1) + 1 := by
    simp only [coveredBelowCount_succ, if_pos hpred]
  have hidle : coveredBelowCount (target + 2) (tailStart - 1) + 1 ≤
      tailStart - 1 :=
    coveredBelowCount_two_above ht1 ht12 (by omega) ha1 ha2
  omega

/-! ## The middle row dies -/

namespace PinnedTailMinimumConfiguration

variable {target clock : Nat}

/-- The pinned clock is at least three, so the second backward step lands at
a positive time.  A clock of two would need its target below three and above
six at the same time. -/
theorem three_le_clock (h : PinnedTailMinimumConfiguration target clock) :
    3 ≤ clock := by
  have hpos := h.clock_pos
  have hbound := h.clock_bound
  have htri := h.upperTri_bound
  by_cases hone : clock = 1
  · subst hone
    have hone' : upperTri 1 = 1 := by decide
    omega
  · by_cases htwo : clock = 2
    · subst htwo
      have htwo' : upperTri 2 = 3 := by decide
      omega
    · omega

end PinnedTailMinimumConfiguration

namespace TerminalExactDischargeReplayCertificate

variable {target start : Nat} {parent : PhaseSearchNode}
variable {source : PermanentTailDischargeReturnCertificate target start parent}

/-- Refined pre-tail separation for a replay whose tail minimum sits at
`target + 2` and whose two times before the minimum predecessor clock both
carry values at or above `target + 2`. -/
theorem target_add_two_lt_tailStart_of_two_above
    (r : TerminalExactDischargeReplayCertificate source)
    (hminimum : a source.historicalMinimumTime = target + 2)
    {t1 t2 : Nat} (ht1 : 0 < t1) (ht12 : t1 < t2)
    (ht2 : t2 < source.tailStart)
    (ha1 : target + 2 ≤ a t1) (ha2 : target + 2 ≤ a t2) :
    target + 2 < source.tailStart := by
  have hpred : a source.historicalFirstTime =
      a source.historicalMinimumTime - 1 :=
    source.historical_minimum.predecessor_first.1
  have hvalue : a source.historicalFirstTime = target + 1 := by omega
  have hmem := r.predecessor_covered_preTail
  have hmem' : (target + 1) ∈ valuesThrough (source.tailStart - 1) := by
    rw [← hvalue]
    exact hmem
  have hbound := target_add_three_le_tailStart
    (target := target) (tailStart := source.tailStart)
    r.belowTarget_covered_preTail hmem' ht1 ht12 ht2 ha1 ha2
  omega

/-- The middle backward row is impossible.  Its two idle pre-tail times push
the tail start past `target + 2`, and the tail minimum value `target + 2`
then recurs too late at the tail minimum time. -/
theorem middle_row_absurd
    (r : TerminalExactDischargeReplayCertificate source)
    (hminimum : a source.historicalMinimumTime = target + 2)
    {base : Nat} (hclock : source.historicalFirstTime = base + 2)
    (hbase : 0 < base)
    (hprevious : target + 2 ≤ a (base + 1))
    (hmiddle : a base = target + 2) : False := by
  have hbefore := source.historical_minimum.firstTime_before_tail
  have htail := source.historical_minimum.minimum.start_le_time
  have hstart : target + 2 < source.tailStart :=
    r.target_add_two_lt_tailStart_of_two_above hminimum hbase
      (Nat.lt_succ_self base) (by omega) (by omega) hprevious
  exact value_no_late_recurrence (v := target + 2) (w := base)
    (m := source.historicalMinimumTime) hmiddle (by omega) (by omega)
    hminimum

/-- The same, with the companion value read off the backward trichotomy
instead of assumed.  Only the middle row can store `target + 2` two steps
before the clock, and that row also pins the intermediate value high. -/
theorem middle_row_absurd_of_pinned
    (r : TerminalExactDischargeReplayCertificate source)
    (hminimum : a source.historicalMinimumTime = target + 2)
    {base : Nat} (hclock : source.historicalFirstTime = base + 2)
    (hp : PinnedTailMinimumConfiguration target (base + 2))
    (hmiddle : a base = target + 2) : False := by
  have hbase : 0 < base := by
    have hthree := hp.three_le_clock
    omega
  rcases hp.backward_trichotomy with ⟨hone, htwo⟩ | ⟨hone, htwo⟩ |
    ⟨hone, htwo⟩
  · omega
  · exact r.middle_row_absurd hminimum hclock hbase (by omega) hmiddle
  · omega

/-- Headline.  With the middle row eliminated the pinned backward shape is a
dichotomy: the two steps before the clock either both subtract, or both add.
The mixed shapes are gone — one by `not_add_then_subtract`, the other by the
refined counting separation above. -/
theorem pinned_backward_dichotomy
    (r : TerminalExactDischargeReplayCertificate source)
    (hminimum : a source.historicalMinimumTime = target + 2)
    {base : Nat} (hclock : source.historicalFirstTime = base + 2)
    (hp : PinnedTailMinimumConfiguration target (base + 2)) :
    (a (base + 1) = target + base + 3 ∧
        a base = target + 2 * base + 4) ∨
      (a (base + 1) + base + 2 = target + 1 ∧
        a base + 2 * base + 2 = target) := by
  rcases hp.backward_trichotomy with hone | htwo | hthree
  · exact Or.inl hone
  · exact False.elim
      (r.middle_row_absurd_of_pinned hminimum hclock hp htwo.2)
  · exact Or.inr hthree

end TerminalExactDischargeReplayCertificate

end

end Recaman
