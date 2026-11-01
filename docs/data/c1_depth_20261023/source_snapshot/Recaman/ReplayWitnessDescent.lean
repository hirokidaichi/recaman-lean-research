import Recaman.PermanentAboveCorridorMinimumFollowUp

namespace Recaman

noncomputable section

/-! # Witness descent out of the blocked immediate addition

The witnessed follow-up dichotomy leaves one branch in which the minimum
predecessor cannot subtract even though its clock is small enough: the
subtraction defect `a f - (f + 1)` is already stored in the history at time
`f`.  A stored value has a genuine first occurrence no later than `f`, and it
is strictly smaller than the predecessor value, so the branch always hands
back a strictly earlier and strictly smaller first occurrence.  That is one
edge of the well-founded order `EarlierSmaller` already used by the blocker
machinery.

This module isolates that edge as a self-contained notion,
`BlockedFirstOccurrence`, and records exactly what does and does not
transport along it.

Transported: the witness is a genuine first occurrence, it is positive, it is
strictly smaller than the parent value, its time is strictly smaller than the
parent time and still positive, the affine gap `value - time` strictly drops,
and — in the replay setting — the witness stays below the tail minimum and
its first occurrence stays before the permanent tail, so it can never recur
inside the tail.

Not transported: the two hypotheses that make the branch a *blocked* one,
namely the clock bound `g + 1 < w` and the history blockage at `g + 1`.
Nothing in the branch forces the witness clock to remain below the witness
value, so the chain can stop after a single step.  `regenerate` names those
two residual obligations, and
`blockedFirstOccurrence_impossible_of_regeneration` shows that supplying them
uniformly would eliminate every blocked first occurrence at once, hence the
blocked branch of every replay, with no reference to any clock floor.

Independently of the descent, the branch also pins the immediate future: the
forced addition at `f + 1` makes `a f - 1` the next subtraction candidate, so
the value one below the minimum predecessor either receives its very first
occurrence two steps after `f` — and then the permanent tail cannot have
started yet — or it was already present strictly before `f`.  Either way that
value is attained, hence differs from the missing target, and the tail
minimum clears the target by at least three rather than by two.
-/

/-- A first occurrence whose immediate follow-up subtraction fails for a
purely historical reason: the clock is small enough to subtract, yet the
subtraction defect has already been recorded. -/
structure BlockedFirstOccurrence (value time : Nat) : Prop where
  first : FirstAt a value time
  clock_below_value : time + 1 < value
  blocked : ¬ CanSubtract (time + 1) (stateAt time)

namespace BlockedFirstOccurrence

variable {value time : Nat}

/-- The recorded value is the orbit value at the recorded time. -/
theorem value_eq (h : BlockedFirstOccurrence value time) :
    a time = value := h.first.1

/-- The blockage is historical: the defect is already stored. -/
theorem defect_seen (h : BlockedFirstOccurrence value time) :
    value - (time + 1) ∈ valuesThrough time := by
  have hvalue : a time = value := h.first.1
  have hclock := h.clock_below_value
  rcases not_canSubtract_cases h.blocked with hsmall | hseen
  · exact False.elim (by omega)
  · rw [hvalue] at hseen
    exact hseen

/-- The defect witness is positive. -/
theorem defect_pos (h : BlockedFirstOccurrence value time) :
    0 < value - (time + 1) := by
  have hclock := h.clock_below_value
  omega

/-- The defect witness is strictly below the blocked value. -/
theorem defect_lt (h : BlockedFirstOccurrence value time) :
    value - (time + 1) < value := by
  have hclock := h.clock_below_value
  omega

/-- The forced addition value at the blocked clock. -/
theorem next_value (h : BlockedFirstOccurrence value time) :
    a (time + 1) = value + (time + 1) := by
  have hstep := a_succ_of_not_canSubtract h.blocked
  have hvalue : a time = value := h.first.1
  omega

/-- After the forced addition the next subtraction candidate is exactly one
below the blocked value. -/
theorem second_candidate (h : BlockedFirstOccurrence value time) :
    a (time + 1) - (time + 2) = value - 1 := by
  have hnext := h.next_value
  have hclock := h.clock_below_value
  omega

/-- Any first occurrence of the defect witness is strictly earlier than the
blocked time. -/
theorem defect_firstTime_lt {earlier : Nat}
    (h : BlockedFirstOccurrence value time)
    (hfirst : FirstAt a (value - (time + 1)) earlier) :
    earlier < time := by
  have hclock := h.clock_below_value
  have hvalue : a time = value := h.first.1
  rcases mem_valuesThrough_iff.mp h.defect_seen with ⟨u, hu, hau⟩
  have hnotlt : ¬ u < earlier := by
    intro hlt
    exact hfirst.2 u hlt hau
  have hle : earlier ≤ time := by omega
  have hne : earlier ≠ time := by
    intro heq
    have hfv : a earlier = value - (time + 1) := hfirst.1
    rw [heq] at hfv
    omega
  omega

/-- The defect witness has a genuine first occurrence strictly before the
blocked time, and that time is itself positive. -/
theorem exists_defect_firstAt (h : BlockedFirstOccurrence value time) :
    ∃ earlier, earlier < time ∧ 0 < earlier ∧
      FirstAt a (value - (time + 1)) earlier := by
  rcases history_member_has_firstAt h.defect_seen with
    ⟨earlier, _, hfirst⟩
  refine ⟨earlier, h.defect_firstTime_lt hfirst, ?_, hfirst⟩
  have hpos := h.defect_pos
  have hfv : a earlier = value - (time + 1) := hfirst.1
  by_cases hzero : earlier = 0
  · rw [hzero] at hfv
    have hbase : a 0 = 0 := rfl
    omega
  · omega

/-- The blocked branch produces one edge of the well-founded
earlier-and-smaller order. -/
theorem earlierSmaller {earlier : Nat}
    (h : BlockedFirstOccurrence value time)
    (hfirst : FirstAt a (value - (time + 1)) earlier) :
    EarlierSmaller ⟨value - (time + 1), earlier⟩ ⟨value, time⟩ := by
  refine ⟨?_, ?_⟩
  · show value - (time + 1) < value
    exact h.defect_lt
  · show earlier < time
    exact h.defect_firstTime_lt hfirst

/-- The affine gap between value and time also strictly drops along the
edge, so a continued chain is short as well as well-founded. -/
theorem gap_drop {earlier : Nat}
    (h : BlockedFirstOccurrence value time)
    (hfirst : FirstAt a (value - (time + 1)) earlier) :
    value - (time + 1) - earlier < value - time := by
  have hclock := h.clock_below_value
  have hlt := h.defect_firstTime_lt hfirst
  omega

/-- The two residual obligations of the descent, named explicitly: nothing in
the blocked branch forces either of them at the witness. -/
theorem regenerate {earlier : Nat}
    (hfirst : FirstAt a (value - (time + 1)) earlier)
    (hclock : earlier + 1 < value - (time + 1))
    (hblocked : ¬ CanSubtract (earlier + 1) (stateAt earlier)) :
    BlockedFirstOccurrence (value - (time + 1)) earlier :=
  ⟨hfirst, hclock, hblocked⟩

/-- Local future of a blocked first occurrence: the value one below it either
receives its first occurrence exactly two steps later, or it was already
present strictly before the blocked time. -/
theorem predecessor_dichotomy (h : BlockedFirstOccurrence value time) :
    (a (time + 2) = value - 1 ∧ FirstAt a (value - 1) (time + 2)) ∨
      (∃ earlier, earlier < time ∧ FirstAt a (value - 1) earlier) := by
  have hnext := h.next_value
  have hclock := h.clock_below_value
  have hvalue : a time = value := h.first.1
  by_cases hsub : CanSubtract (time + 2) (stateAt (time + 1))
  · left
    have hstep : a (time + 1 + 1) = a (time + 1) - (time + 1 + 1) :=
      a_succ_of_canSubtract (n := time + 1) hsub
    have hstep' : a (time + 2) = a (time + 1) - (time + 2) := by
      simpa using hstep
    have hval : a (time + 2) = value - 1 := by omega
    refine ⟨hval, ?_⟩
    have hfresh : FirstAt a (a (time + 1 + 1)) (time + 1 + 1) :=
      firstAt_succ_of_canSubtract (n := time + 1) hsub
    have hfresh' : FirstAt a (a (time + 2)) (time + 2) := by
      simpa using hfresh
    rw [hval] at hfresh'
    exact hfresh'
  · right
    rcases not_canSubtract_cases (n := time + 1) hsub with hsmall | hseen
    · exact False.elim (by omega)
    · have heq : a (time + 1) - (time + 1 + 1) = value - 1 := by omega
      rw [heq] at hseen
      rcases history_member_has_firstAt hseen with ⟨earlier, hle, hfirst⟩
      refine ⟨earlier, ?_, hfirst⟩
      have hfv : a earlier = value - 1 := hfirst.1
      rcases Nat.lt_or_ge earlier time with hlt | hge
      · exact hlt
      · exfalso
        have hcases : earlier = time ∨ earlier = time + 1 := by omega
        rcases hcases with rfl | rfl
        · omega
        · omega

end BlockedFirstOccurrence

/-- Well-founded packaging: no property of occurrences can descend forever in
the earlier-and-smaller order. -/
theorem no_earlierSmaller_descent {S : Occurrence → Prop}
    (hstep : ∀ node, S node → ∃ child, S child ∧ EarlierSmaller child node) :
    ∀ node, ¬ S node := by
  intro node
  refine earlierSmaller_wellFounded.induction (C := fun n => ¬ S n) node ?_
  intro x ih hx
  rcases hstep x hx with ⟨child, hchild, hlt⟩
  exact ih child hlt hchild

/-- Conditional general elimination.  Were the blocked configuration to
regenerate at its own defect witness, the well-founded order would rule out
every blocked first occurrence at once — with no reference to any clock
floor.  The hypothesis is exactly the pair of obligations named by
`BlockedFirstOccurrence.regenerate`. -/
theorem blockedFirstOccurrence_impossible_of_regeneration
    (hregen : ∀ value time earlier, BlockedFirstOccurrence value time →
      FirstAt a (value - (time + 1)) earlier →
      BlockedFirstOccurrence (value - (time + 1)) earlier) :
    ∀ value time, ¬ BlockedFirstOccurrence value time := by
  have hstep : ∀ node : Occurrence,
      BlockedFirstOccurrence node.value node.time →
      ∃ child, BlockedFirstOccurrence child.value child.time ∧
        EarlierSmaller child node := by
    intro node hnode
    rcases hnode.exists_defect_firstAt with ⟨earlier, _, _, hfirst⟩
    exact ⟨⟨node.value - (node.time + 1), earlier⟩,
      hregen _ _ _ hnode hfirst, hnode.earlierSmaller hfirst⟩
  intro value time hblocked
  exact no_earlierSmaller_descent hstep ⟨value, time⟩ hblocked

namespace TerminalExactDischargeReplayCertificate

variable {target start : Nat} {parent : PhaseSearchNode}
variable {source : PermanentTailDischargeReturnCertificate target start parent}

/-- The tail minimum of a surviving replay is at least three: the minimum
predecessor already exceeds the positive target. -/
theorem tailMinimum_ge_three
    (_r : TerminalExactDischargeReplayCertificate source) :
    3 ≤ a source.historicalMinimumTime := by
  have htgt := source.historical_minimum.target_lt_predecessor
  have hpos := source.historical_tail.target_positive
  omega

/-- In the blocked branch the minimum predecessor is a blocked first
occurrence in the sense of this module. -/
theorem minimum_predecessor_blocked
    (r : TerminalExactDischargeReplayCertificate source)
    (hblocked : ¬ CanSubtract (source.historicalFirstTime + 1)
      (stateAt source.historicalFirstTime)) :
    BlockedFirstOccurrence (a source.historicalFirstTime)
      source.historicalFirstTime := by
  refine ⟨?_, r.minimum_predecessor_value_above_clock, hblocked⟩
  have hpred := source.historical_minimum.predecessor_first
  have hp1 : a source.historicalFirstTime =
      a source.historicalMinimumTime - 1 := hpred.1
  rw [hp1]
  exact hpred

/-- The blocked branch hands back a strictly smaller value with a strictly
earlier, still positive first occurrence: one edge of the well-founded
earlier-and-smaller order, obtained without any clock enumeration. -/
theorem minimum_predecessor_blocked_descent
    (r : TerminalExactDischargeReplayCertificate source)
    (hblocked : ¬ CanSubtract (source.historicalFirstTime + 1)
      (stateAt source.historicalFirstTime)) :
    ∃ earlier, earlier < source.historicalFirstTime ∧ 0 < earlier ∧
      FirstAt a (a source.historicalFirstTime -
        (source.historicalFirstTime + 1)) earlier ∧
      EarlierSmaller
        ⟨a source.historicalFirstTime -
          (source.historicalFirstTime + 1), earlier⟩
        ⟨a source.historicalFirstTime, source.historicalFirstTime⟩ := by
  have hblock := r.minimum_predecessor_blocked hblocked
  rcases hblock.exists_defect_firstAt with ⟨earlier, hlt, hpos, hfirst⟩
  exact ⟨earlier, hlt, hpos, hfirst, hblock.earlierSmaller hfirst⟩

/-- What the descent transports: the witness stays strictly below the tail
minimum and its first occurrence stays strictly before the permanent tail. -/
theorem minimum_predecessor_blocked_witness_belowTail
    (r : TerminalExactDischargeReplayCertificate source)
    (hblocked : ¬ CanSubtract (source.historicalFirstTime + 1)
      (stateAt source.historicalFirstTime))
    {earlier : Nat}
    (hfirst : FirstAt a (a source.historicalFirstTime -
      (source.historicalFirstTime + 1)) earlier) :
    a source.historicalFirstTime - (source.historicalFirstTime + 1) <
        a source.historicalMinimumTime ∧
      earlier < source.tailStart := by
  have hblock := r.minimum_predecessor_blocked hblocked
  have hlt := hblock.defect_firstTime_lt hfirst
  have hbefore := source.historical_minimum.firstTime_before_tail
  have hp1 : a source.historicalFirstTime =
      a source.historicalMinimumTime - 1 :=
    source.historical_minimum.predecessor_first.1
  have hthree := r.tailMinimum_ge_three
  exact ⟨by omega, by omega⟩

/-- Consequently the descended witness can never recur inside the permanent
tail. -/
theorem minimum_predecessor_blocked_witness_off_tail
    (r : TerminalExactDischargeReplayCertificate source)
    (_hblocked : ¬ CanSubtract (source.historicalFirstTime + 1)
      (stateAt source.historicalFirstTime))
    (time : Nat) (htime : source.tailStart ≤ time) :
    a time ≠ a source.historicalFirstTime -
      (source.historicalFirstTime + 1) := by
  have hmin := source.historical_minimum.minimum.minimal time htime
  have hp1 : a source.historicalFirstTime =
      a source.historicalMinimumTime - 1 :=
    source.historical_minimum.predecessor_first.1
  have hthree := r.tailMinimum_ge_three
  omega

/-- Local future of the blocked branch: the value two below the tail minimum
either receives its very first occurrence two steps after the minimum
predecessor — and then the permanent tail has not started yet — or it was
already present strictly before the minimum predecessor. -/
theorem minimum_predecessor_blocked_second_step
    (r : TerminalExactDischargeReplayCertificate source)
    (hblocked : ¬ CanSubtract (source.historicalFirstTime + 1)
      (stateAt source.historicalFirstTime)) :
    (a (source.historicalFirstTime + 2) =
          a source.historicalMinimumTime - 2 ∧
        FirstAt a (a source.historicalMinimumTime - 2)
          (source.historicalFirstTime + 2) ∧
        source.historicalFirstTime + 2 < source.tailStart) ∨
      (∃ earlier, earlier < source.historicalFirstTime ∧
        FirstAt a (a source.historicalMinimumTime - 2) earlier) := by
  have hblock := r.minimum_predecessor_blocked hblocked
  have hp1 : a source.historicalFirstTime =
      a source.historicalMinimumTime - 1 :=
    source.historical_minimum.predecessor_first.1
  have hthree := r.tailMinimum_ge_three
  have hshift : a source.historicalFirstTime - 1 =
      a source.historicalMinimumTime - 2 := by omega
  rcases hblock.predecessor_dichotomy with ⟨hval, hfresh⟩ | ⟨earlier, hlt,
    hfirst⟩
  · left
    rw [hshift] at hval hfresh
    refine ⟨hval, hfresh, ?_⟩
    by_cases hbefore : source.historicalFirstTime + 2 < source.tailStart
    · exact hbefore
    · have hle : source.tailStart ≤ source.historicalFirstTime + 2 := by
        omega
      have hmin := source.historical_minimum.minimum.minimal
        (source.historicalFirstTime + 2) hle
      omega
  · right
    rw [hshift] at hfirst
    exact ⟨earlier, hlt, hfirst⟩

/-- Either way the value two below the tail minimum is genuinely attained,
so it cannot be the missing target: in the blocked branch the tail minimum
clears the target by at least three, strengthening the certificate's own
`target_lt_predecessor`. -/
theorem tailMinimum_gap_of_blocked
    (r : TerminalExactDischargeReplayCertificate source)
    (hblocked : ¬ CanSubtract (source.historicalFirstTime + 1)
      (stateAt source.historicalFirstTime)) :
    target + 2 < a source.historicalMinimumTime := by
  have hthree := r.tailMinimum_ge_three
  have htgt := source.historical_minimum.target_lt_predecessor
  have hmissing := source.historical_tail.target_missing
  have hattained : ∃ time, a time = a source.historicalMinimumTime - 2 := by
    rcases r.minimum_predecessor_blocked_second_step hblocked with
      ⟨hval, _, _⟩ | ⟨earlier, _, hfirst⟩
    · exact ⟨source.historicalFirstTime + 2, hval⟩
    · exact ⟨earlier, hfirst.1⟩
  rcases hattained with ⟨time, hvalue⟩
  by_cases hgap : target + 2 < a source.historicalMinimumTime
  · exact hgap
  · exact False.elim (hmissing ⟨time, by omega⟩)

/-- Conditional elimination of the blocked branch.  If the blocked
configuration regenerated at its own defect witness, the well-founded order
would forbid the branch outright, so every surviving replay would have to
subtract immediately at the minimum predecessor. -/
theorem minimum_predecessor_canSubtract_of_regeneration
    (hregen : ∀ value time earlier, BlockedFirstOccurrence value time →
      FirstAt a (value - (time + 1)) earlier →
      BlockedFirstOccurrence (value - (time + 1)) earlier)
    (r : TerminalExactDischargeReplayCertificate source) :
    CanSubtract (source.historicalFirstTime + 1)
      (stateAt source.historicalFirstTime) := by
  by_cases hsub : CanSubtract (source.historicalFirstTime + 1)
      (stateAt source.historicalFirstTime)
  · exact hsub
  · exact False.elim
      (blockedFirstOccurrence_impossible_of_regeneration hregen _ _
        (r.minimum_predecessor_blocked hsub))

/-- Under the same conditional hypothesis the witnessed dichotomy collapses
to its double-subtraction branch. -/
theorem minimum_predecessor_doubleSubtract_of_regeneration
    (hregen : ∀ value time earlier, BlockedFirstOccurrence value time →
      FirstAt a (value - (time + 1)) earlier →
      BlockedFirstOccurrence (value - (time + 1)) earlier)
    (r : TerminalExactDischargeReplayCertificate source)
    (hvalue : a source.historicalFirstTime + 1 <
      source.historicalMinimumTime)
    (horder : source.historicalFirstTime + 2 <
      source.historicalMinimumTime) :
    CanSubtract (source.historicalFirstTime + 1)
        (stateAt source.historicalFirstTime) ∧
      CanSubtract (source.historicalFirstTime + 2)
        (stateAt (source.historicalFirstTime + 1)) := by
  have hsub := r.minimum_predecessor_canSubtract_of_regeneration hregen
  refine ⟨hsub, ?_⟩
  rcases r.minimum_predecessor_shape hvalue horder with hnosub | hsub2
  · exact absurd hsub hnosub
  · exact hsub2

end TerminalExactDischargeReplayCertificate

end

end Recaman
