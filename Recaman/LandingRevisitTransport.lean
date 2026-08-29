import Recaman.PermanentAboveCorridorLeastMissingSummit
import Recaman.PermanentAboveCorridorPrefixSuccessorCoverage

namespace Recaman

noncomputable section

/-! # Transporting the replay tools onto the landing fixed point

The unified terminal outcome has three branches, but only the discharge
replay has been attacked.  Its three weapons — record exclusion, the
downcross prefix bound, and revisit elimination — all rest on one chain:
the discharge downcross sits at or above the missing target
(`FutureDowncrossStep.start_at_or_above`), it dominates the stored
historical first time (`horizon_le_time`), and the replay clock is
literally the parent's old crossing and is eligible
(`time_eq`, `eligible`).  Together these place a certified above-target
event strictly before the replay clock.

The landing fixed point has no such chain.  This module first shows what
does transport unconditionally, then isolates exactly what does not.

Unconditionally: the whole landing window `[landing, crossing]` stays below
the target, so no above-target event lives inside it; the tail minimum can
never revisit a value whose occurrence and size both predate the tail, so
revisit elimination transports verbatim onto the combined certificate; and
the parent's stored crossing is pinned relative to the landing clock —
either it precedes the clock, and then record exclusion together with a
prefix bound fires exactly as on the replay side, or it sits at the clock,
or beyond it but no further than the clock value.

Conditionally: as soon as the tail-minimum predecessor first occurs before
the landing clock, the prefix-successor coverage engine transports too, and
kernel computation through time 131 raises the landing clock floor to
thirty-two in one step — with no `target = 19` escape.

What is missing is therefore a single ordering fact, and it is sharp: the
landing window dichotomy shows the tail-minimum predecessor first occurs
either before the landing or after the crossing, and nothing in the landing
branch decides which.  The replay side decides it through its downcross;
the landing side, whose clock is only anchored from below by a fresh
history landing, does not.
-/

/-- Between a below-target landing and its canonical first upcrossing the
orbit never reaches the target: an intermediate breach would itself be a
weak upcrossing from the landing, contradicting minimality. -/
theorem FirstWeakUpcrossingStep.window_below
    {target landingTime crossingTime : Nat}
    (h : FirstWeakUpcrossingStep target landingTime crossingTime)
    (hstart : a landingTime < target) :
    ∀ time, landingTime ≤ time → time ≤ crossingTime → a time < target := by
  have aux : ∀ offset, landingTime + offset ≤ crossingTime →
      a (landingTime + offset) < target := by
    intro offset
    induction offset with
    | zero => intro _; simpa using hstart
    | succ offset ih =>
        intro hle
        show a (landingTime + offset + 1) < target
        have hprev : a (landingTime + offset) < target := ih (by omega)
        by_cases hbreach : target ≤ a (landingTime + offset + 1)
        · have hforced : ¬ CanSubtract (landingTime + offset + 1)
              (stateAt (landingTime + offset)) := by
            intro hcan
            have hstep := a_succ_of_canSubtract hcan
            omega
          have hstep : WeakUpcrossingStep target landingTime
              (landingTime + offset) := {
            start_le := by omega
            below := hprev
            endpoint_ge := hbreach
            forced_addition := hforced
          }
          exact False.elim (h.first (landingTime + offset) (by omega) hstep)
        · omega
  intro time hlow hhigh
  have hsplit : time = landingTime + (time - landingTime) := by omega
  rw [hsplit]
  exact aux _ (by omega)

/-- Record exclusion, transported to the shared fixed-point core: any
above-target orbit event strictly before the clock dominates the clock
value, so the clock cannot be a running maximum. -/
theorem TailFixedPointCore.crossingTime_not_record_of_prefixAbove
    {target : Nat} {parent : PhaseSearchNode} {crossingTime : Nat}
    (core : TailFixedPointCore target parent crossingTime)
    {witnessTime : Nat} (hbefore : witnessTime < crossingTime)
    (habove : target ≤ a witnessTime) :
    ∃ time, time < crossingTime ∧ a crossingTime < a time := by
  have hbelow := core.below
  exact ⟨witnessTime, hbefore, by omega⟩

namespace PermanentTailCombinedCertificate

variable {target start : Nat} {parent : PhaseSearchNode}
variable {minimumTime predecessorFirstTime : Nat}

/-- Any orbit value at or below the missing target occurs before the
permanent tail begins. -/
theorem lowWitness_lt_start
    (h : PermanentTailCombinedCertificate target start parent minimumTime
      predecessorFirstTime)
    {witness : Nat} (hlow : a witness ≤ target) : witness < start := by
  by_cases hbefore : witness < start
  · exact hbefore
  · have habove := h.tail.strictly_above witness (Nat.le_of_not_gt hbefore)
    omega

/-- Revisit elimination transported onto the combined certificate: the tail
minimum is the successor of its own predecessor value, so any early
occurrence of that successor — early both in time and in size, measured by
a cutoff whose own value is at or below the target — makes the tail minimum
a forbidden late revisit. -/
theorem minimum_revisit_absurd
    (h : PermanentTailCombinedCertificate target start parent minimumTime
      predecessorFirstTime)
    {cutoff witness : Nat}
    (hlow : a cutoff ≤ target)
    (hwitness_time : witness ≤ cutoff)
    (hwitness_value : a witness ≤ cutoff)
    (hsuccessor : a witness = a predecessorFirstTime + 1) : False := by
  have hcutoff := h.lowWitness_lt_start hlow
  have hminimum := h.minimum.minimum.start_le_time
  have hpredecessor := h.minimum.predecessor_first.1
  have htarget := h.minimum.target_lt_predecessor
  have hpositive := h.tail.target_positive
  have hvalue : a minimumTime = a witness := by omega
  exact value_no_late_recurrence (v := a witness) (w := witness)
    (m := minimumTime) rfl (by omega) (by omega) hvalue

/-- The prefix-successor coverage engine transports to any fixed-point core
whose clock dominates the tail-minimum predecessor's first occurrence. -/
theorem impossible_of_prefixSuccessorCoverage
    {crossingTime : Nat}
    (h : PermanentTailCombinedCertificate target start parent minimumTime
      predecessorFirstTime)
    (core : TailFixedPointCore target parent crossingTime)
    (prefix_bound : predecessorFirstTime < crossingTime)
    {cutoff : Nat}
    (hlow : a cutoff ≤ target)
    (hcoverage : ReplayPrefixSuccessorCoverage crossingTime cutoff) :
    False := by
  have hpredecessor := h.minimum.predecessor_first.1
  have htarget := h.minimum.target_lt_predecessor
  have hbelow := core.below
  have habove : a crossingTime < a predecessorFirstTime := by omega
  rcases hcoverage predecessorFirstTime prefix_bound habove with
    ⟨witness, hwitnessTime, hwitnessValue, hwitnessBound⟩
  exact h.minimum_revisit_absurd hlow hwitnessTime hwitnessBound
    hwitnessValue

/-- Uniform coverage below a ceiling raises the fixed-point clock floor in
one step, once the predecessor prefix bound is available. -/
theorem crossingTime_ge_of_prefixSuccessorCoverage
    {crossingTime : Nat}
    (h : PermanentTailCombinedCertificate target start parent minimumTime
      predecessorFirstTime)
    (core : TailFixedPointCore target parent crossingTime)
    (prefix_bound : predecessorFirstTime < crossingTime)
    {ceiling cutoff : Nat}
    (hlow : a cutoff ≤ target)
    (hcoverage : ∀ clock, clock < ceiling →
      ReplayPrefixSuccessorCoverage clock cutoff) :
    ceiling ≤ crossingTime := by
  by_cases hceiling : ceiling ≤ crossingTime
  · exact hceiling
  · exact False.elim (h.impossible_of_prefixSuccessorCoverage core
      prefix_bound hlow (hcoverage crossingTime (Nat.lt_of_not_ge hceiling)))

set_option maxRecDepth 100000 in
/-- Concrete instance of the coverage engine.  Every prefix time below
thirty-one whose value can exceed the target has its successor witnessed by
time 131, whose own value four lies below the unconditional target floor
nineteen.  Hence a fixed-point clock that dominates the tail-minimum
predecessor's first occurrence is at least thirty-two — with no
`target = 19` escape left over. -/
theorem thirtytwo_le_crossingTime_of_prefixBound
    {crossingTime : Nat}
    (h : PermanentTailCombinedCertificate target start parent minimumTime
      predecessorFirstTime)
    (core : TailFixedPointCore target parent crossingTime)
    (prefix_bound : predecessorFirstTime < crossingTime) :
    32 ≤ crossingTime := by
  by_cases hbig : 32 ≤ crossingTime
  · exact hbig
  · have hmissing := h.tail.target_missing
    have hnineteen := core.nineteen_le_target hmissing
    have hpredecessor := h.minimum.predecessor_first.1
    have htarget := h.minimum.target_lt_predecessor
    have habove : 19 < a predecessorFirstTime := by omega
    have h131 : a 131 = 4 := by decide
    have hlow : a 131 ≤ target := by omega
    have hkill : ∀ witness, witness ≤ 131 → a witness ≤ 131 →
        a witness = a predecessorFirstTime + 1 → False := by
      intro witness hwitness hvalue hsuccessor
      exact h.minimum_revisit_absurd hlow hwitness hvalue hsuccessor
    have hcases : predecessorFirstTime = 0 ∨
        predecessorFirstTime = 1 ∨ predecessorFirstTime = 2 ∨
        predecessorFirstTime = 3 ∨ predecessorFirstTime = 4 ∨
        predecessorFirstTime = 5 ∨ predecessorFirstTime = 6 ∨
        predecessorFirstTime = 7 ∨ predecessorFirstTime = 8 ∨
        predecessorFirstTime = 9 ∨ predecessorFirstTime = 10 ∨
        predecessorFirstTime = 11 ∨ predecessorFirstTime = 12 ∨
        predecessorFirstTime = 13 ∨ predecessorFirstTime = 14 ∨
        predecessorFirstTime = 15 ∨ predecessorFirstTime = 16 ∨
        predecessorFirstTime = 17 ∨ predecessorFirstTime = 18 ∨
        predecessorFirstTime = 19 ∨ predecessorFirstTime = 20 ∨
        predecessorFirstTime = 21 ∨ predecessorFirstTime = 22 ∨
        predecessorFirstTime = 23 ∨ predecessorFirstTime = 24 ∨
        predecessorFirstTime = 25 ∨ predecessorFirstTime = 26 ∨
        predecessorFirstTime = 27 ∨ predecessorFirstTime = 28 ∨
        predecessorFirstTime = 29 ∨ predecessorFirstTime = 30 := by
      omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
    · exact absurd habove (by decide)
    · exact absurd habove (by decide)
    · exact absurd habove (by decide)
    · exact absurd habove (by decide)
    · exact absurd habove (by decide)
    · exact absurd habove (by decide)
    · exact absurd habove (by decide)
    · exact False.elim (hkill 9 (by omega) (by decide) (by decide))
    · exact absurd habove (by decide)
    · exact False.elim (hkill 11 (by omega) (by decide) (by decide))
    · exact absurd habove (by decide)
    · exact False.elim (hkill 13 (by omega) (by decide) (by decide))
    · exact absurd habove (by decide)
    · exact False.elim (hkill 15 (by omega) (by decide) (by decide))
    · exact absurd habove (by decide)
    · exact False.elim (hkill 17 (by omega) (by decide) (by decide))
    · exact absurd habove (by decide)
    · exact False.elim (hkill 64 (by omega) (by decide) (by decide))
    · exact False.elim (hkill 28 (by omega) (by decide) (by decide))
    · exact False.elim (hkill 21 (by omega) (by decide) (by decide))
    · exact False.elim (hkill 18 (by omega) (by decide) (by decide))
    · exact False.elim (hkill 99 (by omega) (by decide) (by decide))
    · exact False.elim (hkill 20 (by omega) (by decide) (by decide))
    · exact absurd habove (by decide)
    · exact False.elim (hkill 18 (by omega) (by decide) (by decide))
    · exact absurd habove (by decide)
    · exact False.elim (hkill 28 (by omega) (by decide) (by decide))
    · exact absurd habove (by decide)
    · exact False.elim (hkill 30 (by omega) (by decide) (by decide))
    · exact absurd habove (by decide)
    · exact False.elim (hkill 32 (by omega) (by decide) (by decide))

/-- Numeric content of the parent's stored crossing: a forced-addition
upcrossing of the missing target whose value is the parent anchor. -/
theorem exists_parentCrossing
    (h : PermanentTailCombinedCertificate target start parent minimumTime
      predecessorFirstTime) :
    ∃ oldTime, parent.anchorParent = a oldTime ∧ a oldTime < target ∧
      target < a (oldTime + 1) ∧
      a (oldTime + 1) = a oldTime + (oldTime + 1) := by
  rcases h.crossing.ready_crossing.crossing with
    ⟨oldAnchor, oldTime, quotient, remainder, hold⟩
  refine ⟨oldTime, ?_, hold.recovery.crossing.1,
    hold.recovery.crossing.2.1, hold.recovery.crossing.2.2⟩
  simpa using congrArg PhaseSearchNode.anchorParent hold.node_eq

/-- The parent's stored crossing is pinned relative to any fixed-point
clock of the same node.  It cannot sit one step before the clock, because
its own forced addition would then move the shared anchor value.  So either
it lies at least two steps before the clock — and its endpoint is then an
above-target prefix event, exactly the datum the discharge downcross
supplies — or it is the clock itself, or it lies beyond the clock, in which
case late-recurrence forbids it to exceed the clock value. -/
theorem aboveTarget_before_crossing_or_pinnedParent
    {crossingTime : Nat}
    (h : PermanentTailCombinedCertificate target start parent minimumTime
      predecessorFirstTime)
    (core : TailFixedPointCore target parent crossingTime) :
    (∃ time, time < crossingTime ∧ target < a time) ∨
      (∃ oldTime, a oldTime = a crossingTime ∧ crossingTime ≤ oldTime ∧
        (oldTime = crossingTime ∨ oldTime ≤ a crossingTime)) := by
  rcases h.exists_parentCrossing with
    ⟨oldTime, hanchor, hbelow, habove, hforced⟩
  have hsame : a oldTime = a crossingTime :=
    hanchor.symm.trans core.anchor_eq.symm
  by_cases hlt : oldTime < crossingTime
  · have hne : oldTime + 1 ≠ crossingTime := by
      intro heq
      rw [← heq] at hsame
      omega
    exact Or.inl ⟨oldTime + 1, by omega, habove⟩
  · by_cases heq : oldTime = crossingTime
    · exact Or.inr ⟨oldTime, hsame, by omega, Or.inl heq⟩
    · have hgt : crossingTime < oldTime := by omega
      have hbound : oldTime ≤ a crossingTime := by
        by_cases hb : oldTime ≤ a crossingTime
        · exact hb
        · exact False.elim (value_no_late_recurrence (v := a crossingTime)
            (w := crossingTime) (m := oldTime) rfl hgt (by omega) hsame)
      exact Or.inr ⟨oldTime, hsame, by omega, Or.inr hbound⟩

end PermanentTailCombinedCertificate

/-- The tail-minimum predecessor never first occurs inside the landing
window: its value strictly exceeds the target, while the whole window from
the landing to its first upcrossing stays strictly below the target. -/
theorem landing_predecessorFirstTime_outside_window
    {target start : Nat} {parent : PhaseSearchNode}
    {minimumTime predecessorFirstTime value landingTime crossingTime : Nat}
    (combined : PermanentTailCombinedCertificate target start parent
      minimumTime predecessorFirstTime)
    (value_below : value < target)
    (landing_first : FirstAt a value landingTime)
    (next_crossing : FirstWeakUpcrossingStep target landingTime
      crossingTime) :
    predecessorFirstTime < landingTime ∨
      crossingTime < predecessorFirstTime := by
  have hlanding : a landingTime < target := by
    rw [landing_first.1]
    exact value_below
  have hwindow := next_crossing.window_below hlanding
  have hpredecessor := combined.minimum.predecessor_first.1
  have htarget := combined.minimum.target_lt_predecessor
  by_cases hbefore : predecessorFirstTime < landingTime
  · exact Or.inl hbefore
  · by_cases hafter : crossingTime < predecessorFirstTime
    · exact Or.inr hafter
    · have hin := hwindow predecessorFirstTime (by omega) (by omega)
      omega

/-- Record exclusion for the landing fixed point, with its exact residue:
either the landing crossing is dominated by an earlier orbit value, or the
tail-minimum predecessor first occurs after the crossing clock. -/
theorem landing_crossingTime_not_record_or_gap
    {target start : Nat} {parent : PhaseSearchNode}
    {minimumTime predecessorFirstTime value landingTime crossingTime : Nat}
    (combined : PermanentTailCombinedCertificate target start parent
      minimumTime predecessorFirstTime)
    (value_below : value < target)
    (landing_first : FirstAt a value landingTime)
    (next_crossing : FirstWeakUpcrossingStep target landingTime
      crossingTime)
    (core : TailFixedPointCore target parent crossingTime) :
    (∃ time, time < crossingTime ∧ a crossingTime < a time) ∨
      crossingTime < predecessorFirstTime := by
  rcases landing_predecessorFirstTime_outside_window combined value_below
      landing_first next_crossing with hbefore | hafter
  · have hstart := next_crossing.crossing.start_le
    have hpredecessor := combined.minimum.predecessor_first.1
    have htarget := combined.minimum.target_lt_predecessor
    exact Or.inl (core.crossingTime_not_record_of_prefixAbove
      (witnessTime := predecessorFirstTime) (by omega) (by omega))
  · exact Or.inr hafter

/-- Exact position of the remaining landing gap.  The landing fixed point
already carries a clock floor of thirty-two — strictly better than the
shared kernel floor `18 ≤ crossingTime ∨ target = 19` — unless the
tail-minimum predecessor first occurs after the crossing clock.  Nothing in
the landing branch decides that ordering: the crossing is anchored only from
below, by a fresh history landing, whereas the discharge replay pins its
clock to the parent's stored crossing and its downcross to an earlier time.
Supplying this single ordering fact would transport the entire replay
toolchain onto the landing side. -/
theorem landing_thirtytwo_le_crossingTime_or_gap
    {target start : Nat} {parent : PhaseSearchNode}
    {minimumTime predecessorFirstTime value landingTime crossingTime : Nat}
    (combined : PermanentTailCombinedCertificate target start parent
      minimumTime predecessorFirstTime)
    (value_below : value < target)
    (landing_first : FirstAt a value landingTime)
    (next_crossing : FirstWeakUpcrossingStep target landingTime
      crossingTime)
    (core : TailFixedPointCore target parent crossingTime) :
    32 ≤ crossingTime ∨ crossingTime < predecessorFirstTime := by
  rcases landing_predecessorFirstTime_outside_window combined value_below
      landing_first next_crossing with hbefore | hafter
  · have hstart := next_crossing.crossing.start_le
    exact Or.inl (combined.thirtytwo_le_crossingTime_of_prefixBound core
      (by omega))
  · exact Or.inr hafter

/-- Unified outcome with the landing branch upgraded.  Both fixed-point
branches now carry a clock floor of thirty-two — the replay from its own
kernel sweep, the landing from the transported coverage engine — except for
the single unresolved landing configuration in which the tail-minimum
predecessor first occurs after the crossing clock.  That residue is the
whole remaining distance between the two branches. -/
theorem PermanentTailUnifiedOutcome.semantic_or_thirtytwo_or_landingGap
    {target start : Nat}
    (h : PermanentTailUnifiedOutcome target start) :
    (∃ stepParent child : PhaseSearchNode,
      PhaseSemanticInvariant target child ∧
        PhaseSearchProgress target child stepParent) ∨
    (∃ (parent : PhaseSearchNode) (crossingTime : Nat),
      ∃ _core : TailFixedPointCore target parent crossingTime,
        32 ≤ crossingTime ∧ 19 ≤ target) ∨
    (∃ (parent : PhaseSearchNode) (crossingTime predecessorFirstTime : Nat),
      ∃ _core : TailFixedPointCore target parent crossingTime,
        crossingTime < predecessorFirstTime ∧
          target < a predecessorFirstTime ∧ 19 ≤ target) := by
  cases h with
  | semantic_progress stepParent child semantic progress =>
      exact Or.inl ⟨stepParent, child, semantic, progress⟩
  | discharge_replay replayParent replaySource replay core =>
      have hmissing := replay.target_missing
      have hfloor := replay.onehundredtwelve_le_crossingTime
      exact Or.inr (Or.inl ⟨replayParent, replay.crossingTime, core,
        by omega, core.nineteen_le_target hmissing⟩)
  | landing_cycle parent minimumTime predecessorFirstTime combined value
      landingTime crossingTime value_below landing_first next_crossing
      crossing_before_start core =>
      have hmissing := combined.tail.target_missing
      have hnineteen := core.nineteen_le_target hmissing
      rcases landing_thirtytwo_le_crossingTime_or_gap combined value_below
          landing_first next_crossing core with hfloor | hgap
      · exact Or.inr (Or.inl ⟨parent, crossingTime, core, hfloor,
          hnineteen⟩)
      · have hpredecessor := combined.minimum.predecessor_first.1
        have htarget := combined.minimum.target_lt_predecessor
        exact Or.inr (Or.inr ⟨parent, crossingTime, predecessorFirstTime,
          core, hgap, by omega, hnineteen⟩)

end

end Recaman
