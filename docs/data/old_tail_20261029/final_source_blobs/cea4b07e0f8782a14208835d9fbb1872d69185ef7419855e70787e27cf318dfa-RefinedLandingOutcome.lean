import Recaman.LandingRevisitTransport

namespace Recaman

noncomputable section

/-! # Restoring the erased chronology cursor of the landing fixed point

The landing fixed point is missing exactly one ordering fact: some
above-target orbit event must be placed strictly before the landing clock,
and the tail-minimum predecessor must be placed before it too.  Both facts
exist at the generation site of a history edge and are erased there.

Every history edge of the terminal analysis is produced from a discharge
return certificate, and the parent cursor of the edge is one of three
concrete discharge times: `downTime + 1`, a finite window endpoint
dominating `downTime + 1`, or the stored old crossing.  The first two
strictly dominate the discharge downcross, whose value is at or above the
target; the third is a stored weak upcrossing, whose endpoint value is
above the target.  So every origin can supply an above-target cursor at or
just after its parent time, and the first two can supply the stronger
`downTime < parentTime`.

None of that survives.  The history edge is packaged as the bare budget
drop `TerminalChronologyHistoryProgress target childTime parentTime`, whose
unfolding is only `missingBelowCount target childTime < missingBelowCount
target parentTime`; the parent cursor becomes an anonymous natural number
with no orbit content, and the landing branch inherits only
`parentTime < landingTime`, which then also disappears from
`PermanentTailUnifiedOutcome.landing_cycle`.

This module defines the refined landing interface `RefinedLandingCycle`,
which adds back the single field `downTime < parentTime`, and proves the
payoff: the landing clock floor becomes thirty-two with no `target = 19`
escape, matching the replay side's first deep floor.  It also proves the
origin lemmas showing that the field is genuinely available where history
edges are made.

Independently of the refinement, one new unconditional kernel tool is
proved here.  A clock with no above-target event anywhere in its prefix
straddles the far narrower band above its whole prefix maximum, and every
clock below thirty-two then dies by kernel computation except clock six
with target nineteen and clock eighteen with target sixty-one.  So the
unconditional residue of either fixed-point branch is: clock at least
thirty-two, one of those two pinned stragglers, or an above-target prefix
event — and the refined interface is exactly what converts the last case
into the first.
-/

set_option maxRecDepth 100000 in
/-- Kernel enumeration of prefix cursors.  Every time at most thirty whose
orbit value exceeds the target floor nineteen has its successor value
witnessed by time 131, with the witness value itself at most 131. -/
theorem prefixCursor_successor_witness
    {target cursor : Nat} (hnineteen : 19 ≤ target)
    (hcursor : target < a cursor) (hle : cursor ≤ 30) :
    ∃ witness, witness ≤ 131 ∧ a witness ≤ 131 ∧
      a witness = a cursor + 1 := by
  have habove : 19 < a cursor := by omega
  have hcases : cursor = 0 ∨ cursor = 1 ∨ cursor = 2 ∨ cursor = 3 ∨
      cursor = 4 ∨ cursor = 5 ∨ cursor = 6 ∨ cursor = 7 ∨
      cursor = 8 ∨ cursor = 9 ∨ cursor = 10 ∨ cursor = 11 ∨
      cursor = 12 ∨ cursor = 13 ∨ cursor = 14 ∨ cursor = 15 ∨
      cursor = 16 ∨ cursor = 17 ∨ cursor = 18 ∨ cursor = 19 ∨
      cursor = 20 ∨ cursor = 21 ∨ cursor = 22 ∨ cursor = 23 ∨
      cursor = 24 ∨ cursor = 25 ∨ cursor = 26 ∨ cursor = 27 ∨
      cursor = 28 ∨ cursor = 29 ∨ cursor = 30 := by
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
  · exact ⟨9, by omega, by decide, by decide⟩
  · exact absurd habove (by decide)
  · exact ⟨11, by omega, by decide, by decide⟩
  · exact absurd habove (by decide)
  · exact ⟨13, by omega, by decide, by decide⟩
  · exact absurd habove (by decide)
  · exact ⟨15, by omega, by decide, by decide⟩
  · exact absurd habove (by decide)
  · exact ⟨17, by omega, by decide, by decide⟩
  · exact absurd habove (by decide)
  · exact ⟨64, by omega, by decide, by decide⟩
  · exact ⟨28, by omega, by decide, by decide⟩
  · exact ⟨21, by omega, by decide, by decide⟩
  · exact ⟨18, by omega, by decide, by decide⟩
  · exact ⟨99, by omega, by decide, by decide⟩
  · exact ⟨20, by omega, by decide, by decide⟩
  · exact absurd habove (by decide)
  · exact ⟨18, by omega, by decide, by decide⟩
  · exact absurd habove (by decide)
  · exact ⟨28, by omega, by decide, by decide⟩
  · exact absurd habove (by decide)
  · exact ⟨30, by omega, by decide, by decide⟩
  · exact absurd habove (by decide)
  · exact ⟨32, by omega, by decide, by decide⟩

set_option maxRecDepth 100000 in
/-- Prefix-maximum band elimination.  A fixed-point clock with no
above-target orbit event anywhere in its own prefix pins the target into the
band above the whole prefix maximum, which is far narrower than the plain
straddle band.  Every clock below thirty-two then dies by kernel
computation, except the two deep stragglers: clock six with target nineteen
and clock eighteen with target sixty-one. -/
theorem TailFixedPointCore.thirtytwo_le_crossingTime_of_prefixBelow
    {target : Nat} {parent : PhaseSearchNode} {crossingTime : Nat}
    (core : TailFixedPointCore target parent crossingTime)
    (missing : ¬ ∃ time, a time = target)
    (hprefix : ∀ time, time ≤ crossingTime → a time < target) :
    32 ≤ crossingTime ∨ (crossingTime = 6 ∧ target = 19) ∨
      (crossingTime = 18 ∧ target = 61) := by
  by_cases hbig : 32 ≤ crossingTime
  · exact Or.inl hbig
  · have hnineteen := core.nineteen_le_target missing
    have hendpoint := core.endpoint_ge
    have hforced := core.forced
    have hclocks : crossingTime = 0 ∨ crossingTime = 1 ∨
        crossingTime = 2 ∨ crossingTime = 3 ∨ crossingTime = 4 ∨
        crossingTime = 5 ∨ crossingTime = 6 ∨ crossingTime = 7 ∨
        crossingTime = 8 ∨ crossingTime = 9 ∨ crossingTime = 10 ∨
        crossingTime = 11 ∨ crossingTime = 12 ∨ crossingTime = 13 ∨
        crossingTime = 14 ∨ crossingTime = 15 ∨ crossingTime = 16 ∨
        crossingTime = 17 ∨ crossingTime = 18 ∨ crossingTime = 19 ∨
        crossingTime = 20 ∨ crossingTime = 21 ∨ crossingTime = 22 ∨
        crossingTime = 23 ∨ crossingTime = 24 ∨ crossingTime = 25 ∨
        crossingTime = 26 ∨ crossingTime = 27 ∨ crossingTime = 28 ∨
        crossingTime = 29 ∨ crossingTime = 30 ∨ crossingTime = 31 := by
      omega
    rcases hclocks with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl
    · have hend : target ≤ a 1 := by simpa using hendpoint
      have hvalue : a 1 = 1 := by decide
      exact False.elim (by omega)
    · have hend : target ≤ a 2 := by simpa using hendpoint
      have hvalue : a 2 = 3 := by decide
      exact False.elim (by omega)
    · have hend : target ≤ a 3 := by simpa using hendpoint
      have hvalue : a 3 = 6 := by decide
      exact False.elim (by omega)
    · have hend : target ≤ a 4 := by simpa using hendpoint
      have hvalue : a 4 = 2 := by decide
      exact False.elim (by omega)
    · have hend : target ≤ a 5 := by simpa using hendpoint
      have hvalue : a 5 = 7 := by decide
      exact False.elim (by omega)
    · have hend : target ≤ a 6 := by simpa using hendpoint
      have hvalue : a 6 = 13 := by decide
      exact False.elim (by omega)
    · have hend : target ≤ a 7 := by simpa using hendpoint
      have hmax := hprefix 6 (by omega)
      have hv6 : a 6 = 13 := by decide
      have hv7 : a 7 = 20 := by decide
      have hband : target = 19 ∨ target = 20 := by omega
      rcases hband with rfl | rfl
      · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      · exact absurd ⟨7, by decide⟩ missing
    · have hend : target ≤ a 8 := by simpa using hendpoint
      have hvalue : a 8 = 12 := by decide
      exact False.elim (by omega)
    · have hend : target ≤ a 9 := by simpa using hendpoint
      have hmax := hprefix 7 (by omega)
      have hvmax : a 7 = 20 := by decide
      have hvend : a 9 = 21 := by decide
      exact absurd (⟨9, by omega⟩ : ∃ time, a time = target)
        missing
    · have hend : target ≤ a 10 := by simpa using hendpoint
      have hvalue : a 10 = 11 := by decide
      exact False.elim (by omega)
    · have hend : target ≤ a 11 := by simpa using hendpoint
      have hmax := hprefix 9 (by omega)
      have hvmax : a 9 = 21 := by decide
      have hvend : a 11 = 22 := by decide
      exact absurd (⟨11, by omega⟩ : ∃ time, a time = target)
        missing
    · have hend : target ≤ a 12 := by simpa using hendpoint
      have hvalue : a 12 = 10 := by decide
      exact False.elim (by omega)
    · have hend : target ≤ a 13 := by simpa using hendpoint
      have hmax := hprefix 11 (by omega)
      have hvmax : a 11 = 22 := by decide
      have hvend : a 13 = 23 := by decide
      exact absurd (⟨13, by omega⟩ : ∃ time, a time = target)
        missing
    · have hend : target ≤ a 14 := by simpa using hendpoint
      have hvalue : a 14 = 9 := by decide
      exact False.elim (by omega)
    · have hend : target ≤ a 15 := by simpa using hendpoint
      have hmax := hprefix 13 (by omega)
      have hvmax : a 13 = 23 := by decide
      have hvend : a 15 = 24 := by decide
      exact absurd (⟨15, by omega⟩ : ∃ time, a time = target)
        missing
    · have hend : target ≤ a 16 := by simpa using hendpoint
      have hvalue : a 16 = 8 := by decide
      exact False.elim (by omega)
    · have hend : target ≤ a 17 := by simpa using hendpoint
      have hmax := hprefix 15 (by omega)
      have hvmax : a 15 = 24 := by decide
      have hvend : a 17 = 25 := by decide
      exact absurd (⟨17, by omega⟩ : ∃ time, a time = target)
        missing
    · have hend : target ≤ a 18 := by simpa using hendpoint
      have hmax := hprefix 17 (by omega)
      have hvmax : a 17 = 25 := by decide
      have hvend : a 18 = 43 := by decide
      have hband : target = 26 ∨ target = 27 ∨ target = 28 ∨
          target = 29 ∨ target = 30 ∨ target = 31 ∨ target = 32 ∨
          target = 33 ∨ target = 34 ∨ target = 35 ∨ target = 36 ∨
          target = 37 ∨ target = 38 ∨ target = 39 ∨ target = 40 ∨
          target = 41 ∨ target = 42 ∨ target = 43 := by omega
      rcases hband with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl
      · exact absurd ⟨64, by decide⟩ missing
      · exact absurd ⟨62, by decide⟩ missing
      · exact absurd ⟨60, by decide⟩ missing
      · exact absurd ⟨58, by decide⟩ missing
      · exact absurd ⟨56, by decide⟩ missing
      · exact absurd ⟨54, by decide⟩ missing
      · exact absurd ⟨52, by decide⟩ missing
      · exact absurd ⟨50, by decide⟩ missing
      · exact absurd ⟨48, by decide⟩ missing
      · exact absurd ⟨46, by decide⟩ missing
      · exact absurd ⟨44, by decide⟩ missing
      · exact absurd ⟨42, by decide⟩ missing
      · exact absurd ⟨40, by decide⟩ missing
      · exact absurd ⟨38, by decide⟩ missing
      · exact absurd ⟨111, by decide⟩ missing
      · exact absurd ⟨22, by decide⟩ missing
      · exact absurd ⟨20, by decide⟩ missing
      · exact absurd ⟨18, by decide⟩ missing
    · have hend : target ≤ a 19 := by simpa using hendpoint
      have hmax := hprefix 18 (by omega)
      have hvmax : a 18 = 43 := by decide
      have hvend : a 19 = 62 := by decide
      have hband : target = 44 ∨ target = 45 ∨ target = 46 ∨
          target = 47 ∨ target = 48 ∨ target = 49 ∨ target = 50 ∨
          target = 51 ∨ target = 52 ∨ target = 53 ∨ target = 54 ∨
          target = 55 ∨ target = 56 ∨ target = 57 ∨ target = 58 ∨
          target = 59 ∨ target = 60 ∨ target = 61 ∨ target = 62 := by omega
      rcases hband with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl
      · exact absurd ⟨28, by decide⟩ missing
      · exact absurd ⟨30, by decide⟩ missing
      · exact absurd ⟨32, by decide⟩ missing
      · exact absurd ⟨222, by decide⟩ missing
      · exact absurd ⟨220, by decide⟩ missing
      · exact absurd ⟨218, by decide⟩ missing
      · exact absurd ⟨216, by decide⟩ missing
      · exact absurd ⟨214, by decide⟩ missing
      · exact absurd ⟨212, by decide⟩ missing
      · exact absurd ⟨210, by decide⟩ missing
      · exact absurd ⟨208, by decide⟩ missing
      · exact absurd ⟨206, by decide⟩ missing
      · exact absurd ⟨204, by decide⟩ missing
      · exact absurd ⟨202, by decide⟩ missing
      · exact absurd ⟨200, by decide⟩ missing
      · exact absurd ⟨198, by decide⟩ missing
      · exact absurd ⟨196, by decide⟩ missing
      · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
      · exact absurd ⟨19, by decide⟩ missing
    · exact absurd hforced (by decide)
    · have hend : target ≤ a 21 := by simpa using hendpoint
      have hmax := hprefix 19 (by omega)
      have hvmax : a 19 = 62 := by decide
      have hvend : a 21 = 63 := by decide
      exact absurd (⟨21, by omega⟩ : ∃ time, a time = target)
        missing
    · exact absurd hforced (by decide)
    · have hend : target ≤ a 23 := by simpa using hendpoint
      have hvalue : a 23 = 18 := by decide
      exact False.elim (by omega)
    · have hend : target ≤ a 24 := by simpa using hendpoint
      have hmax := hprefix 21 (by omega)
      have hvmax : a 21 = 63 := by decide
      have hvend : a 24 = 42 := by decide
      exact False.elim (by omega)
    · have hend : target ≤ a 25 := by simpa using hendpoint
      have hvalue : a 25 = 17 := by decide
      exact False.elim (by omega)
    · have hend : target ≤ a 26 := by simpa using hendpoint
      have hmax := hprefix 21 (by omega)
      have hvmax : a 21 = 63 := by decide
      have hvend : a 26 = 43 := by decide
      exact False.elim (by omega)
    · have hend : target ≤ a 27 := by simpa using hendpoint
      have hvalue : a 27 = 16 := by decide
      exact False.elim (by omega)
    · have hend : target ≤ a 28 := by simpa using hendpoint
      have hmax := hprefix 21 (by omega)
      have hvmax : a 21 = 63 := by decide
      have hvend : a 28 = 44 := by decide
      exact False.elim (by omega)
    · have hend : target ≤ a 29 := by simpa using hendpoint
      have hvalue : a 29 = 15 := by decide
      exact False.elim (by omega)
    · have hend : target ≤ a 30 := by simpa using hendpoint
      have hmax := hprefix 21 (by omega)
      have hvmax : a 21 = 63 := by decide
      have hvend : a 30 = 45 := by decide
      exact False.elim (by omega)
    · have hend : target ≤ a 31 := by simpa using hendpoint
      have hvalue : a 31 = 14 := by decide
      exact False.elim (by omega)
    · have hend : target ≤ a 32 := by simpa using hendpoint
      have hmax := hprefix 21 (by omega)
      have hvmax : a 21 = 63 := by decide
      have hvend : a 32 = 46 := by decide
      exact False.elim (by omega)

/-- Bounded search: on any prefix the orbit either stays strictly below the
target throughout, or reaches it somewhere. -/
theorem prefixBelow_or_prefixAbove (target : Nat) :
    ∀ bound, (∀ time, time ≤ bound → a time < target) ∨
      (∃ time, time ≤ bound ∧ target ≤ a time) := by
  intro bound
  induction bound with
  | zero =>
      by_cases hzero : target ≤ a 0
      · exact Or.inr ⟨0, Nat.le_refl _, hzero⟩
      · refine Or.inl (fun time hle => ?_)
        have heq : time = 0 := by omega
        subst heq
        omega
  | succ bound ih =>
      rcases ih with hall | hex
      · by_cases hstep : target ≤ a (bound + 1)
        · exact Or.inr ⟨bound + 1, Nat.le_refl _, hstep⟩
        · refine Or.inl (fun time hle => ?_)
          by_cases hsmall : time ≤ bound
          · exact hall time hsmall
          · have heq : time = bound + 1 := by omega
            subst heq
            omega
      · rcases hex with ⟨time, hle, habove⟩
        exact Or.inr ⟨time, by omega, habove⟩

/-- Unconditional residue of the shared fixed-point core.  Either the clock
is already at thirty-two, or one of the two deep stragglers is pinned
exactly, or the clock carries an above-target prefix event — which is
precisely the datum the refined landing interface makes explicit, and which
the discharge replay obtains from its downcross. -/
theorem TailFixedPointCore.thirtytwo_or_straggler_or_prefixAbove
    {target : Nat} {parent : PhaseSearchNode} {crossingTime : Nat}
    (core : TailFixedPointCore target parent crossingTime)
    (missing : ¬ ∃ time, a time = target) :
    32 ≤ crossingTime ∨ (crossingTime = 6 ∧ target = 19) ∨
      (crossingTime = 18 ∧ target = 61) ∨
      (∃ time, time < crossingTime ∧ target ≤ a time) := by
  rcases prefixBelow_or_prefixAbove target crossingTime with hbelow | habove
  · rcases core.thirtytwo_le_crossingTime_of_prefixBelow missing hbelow with
      hfloor | hsix | heighteen
    · exact Or.inl hfloor
    · exact Or.inr (Or.inl hsix)
    · exact Or.inr (Or.inr (Or.inl heighteen))
  · rcases habove with ⟨time, hle, hvalue⟩
    have hcrossing := core.below
    refine Or.inr (Or.inr (Or.inr ⟨time, ?_, hvalue⟩))
    by_cases heq : time = crossingTime
    · subst heq
      omega
    · omega


/-- Any above-target cursor at or just after the parent cursor of a history
edge precedes the landing itself: the landing value is below the target, so
the cursor cannot coincide with it. -/
theorem aboveTarget_before_landing_of_cursor
    {target parentTime landingTime : Nat}
    (hcursor : ∃ witness, witness ≤ parentTime + 1 ∧ target ≤ a witness)
    (hafter : parentTime < landingTime)
    (hlanding : a landingTime < target) :
    ∃ witness, witness < landingTime ∧ target ≤ a witness := by
  rcases hcursor with ⟨witness, hle, habove⟩
  refine ⟨witness, ?_, habove⟩
  by_cases heq : witness = landingTime
  · rw [heq] at habove
    omega
  · omega

namespace PermanentTailDischargeReturnCertificate

variable {target start : Nat} {parent : PhaseSearchNode}

/-- Any orbit value at or below the missing target occurs before the
historical strict-above tail begins. -/
theorem lowWitness_lt_tailStart
    (source : PermanentTailDischargeReturnCertificate target start parent)
    {witness : Nat} (hlow : a witness ≤ target) :
    witness < source.tailStart := by
  by_cases hbefore : witness < source.tailStart
  · exact hbefore
  · have habove := source.historical_tail.strictly_above witness
      (Nat.le_of_not_gt hbefore)
    omega

/-- Revisit elimination against the historical tail minimum.  This is the
form the discharge replay uses: the minimum is the successor of its own
predecessor value, so an early enough witness of that successor makes the
minimum a forbidden late revisit. -/
theorem historicalMinimum_revisit_absurd
    (source : PermanentTailDischargeReturnCertificate target start parent)
    {cutoff witness : Nat}
    (hlow : a cutoff ≤ target)
    (hwitness_time : witness ≤ cutoff)
    (hwitness_value : a witness ≤ cutoff)
    (hsuccessor : a witness = a source.historicalFirstTime + 1) : False := by
  have hcutoff := source.lowWitness_lt_tailStart hlow
  have hminimum := source.historical_minimum.minimum.start_le_time
  have hpredecessor := source.historical_minimum.predecessor_first.1
  have htarget := source.historical_minimum.target_lt_predecessor
  have hpositive := source.historical_tail.target_positive
  have hvalue : a source.historicalMinimumTime = a witness := by omega
  exact value_no_late_recurrence (v := a witness) (w := witness)
    (m := source.historicalMinimumTime) rfl (by omega) (by omega) hvalue

/-- The stored historical predecessor cursor never exceeds the discharge
downcross time. -/
theorem historicalFirstTime_le_downTime
    (source : PermanentTailDischargeReturnCertificate target start parent) :
    source.historicalFirstTime ≤ source.downTime :=
  source.downcross.horizon_le_time

/-- The discharge downcross is an above-target cursor at its own time, so
any parent cursor at or after it carries one. -/
theorem downcross_cursor
    (source : PermanentTailDischargeReturnCertificate target start parent)
    {parentTime : Nat} (horigin : source.downTime ≤ parentTime) :
    ∃ witness, witness ≤ parentTime + 1 ∧ target ≤ a witness :=
  ⟨source.downTime, by omega, source.downcross.start_at_or_above⟩

/-- The stored old crossing is an above-target cursor one step after its own
time, which is what the ineligible-old-crossing history edge supplies. -/
theorem oldCrossing_cursor
    (source : PermanentTailDischargeReturnCertificate target start parent)
    {parentTime : Nat} (horigin : source.oldCrossingTime ≤ parentTime) :
    ∃ witness, witness ≤ parentTime + 1 ∧ target ≤ a witness :=
  ⟨source.oldCrossingTime + 1, by omega, source.old_crossing.endpoint_ge⟩

set_option maxRecDepth 100000 in
/-- Coverage-free floor: a clock that strictly dominates the discharge
downcross puts the historical predecessor cursor inside the kernel prefix,
where every candidate successor is already witnessed by time 131.  The
clock is therefore at least thirty-two, with no `target = 19` escape. -/
theorem thirtytwo_le_crossingTime_of_downcrossBefore
    (source : PermanentTailDischargeReturnCertificate target start parent)
    {crossingTime : Nat}
    (hnineteen : 19 ≤ target)
    (hdown : source.downTime < crossingTime) :
    32 ≤ crossingTime := by
  by_cases hbig : 32 ≤ crossingTime
  · exact hbig
  · have hfirst := source.historicalFirstTime_le_downTime
    have hpredecessor := source.historical_minimum.predecessor_first.1
    have htarget := source.historical_minimum.target_lt_predecessor
    have hcursor : target < a source.historicalFirstTime := by omega
    rcases prefixCursor_successor_witness hnineteen hcursor (by omega) with
      ⟨witness, hwitnessTime, hwitnessValue, hsuccessor⟩
    have h131 : a 131 = 4 := by decide
    exact False.elim (source.historicalMinimum_revisit_absurd
      (cutoff := 131) (by omega) hwitnessTime hwitnessValue hsuccessor)

end PermanentTailDischargeReturnCertificate

/-- Landing fixed point together with the chronology cursor that the
history-edge interface erases.  Every field except the last two is already
carried by `PermanentTailUnifiedOutcome.landing_cycle`; `after_parent` is
carried by the anchored interface and dropped one step later, and
`downcross_before_parent` is the single genuinely new field, available at
the two discharge-cursor origins of a history edge. -/
structure RefinedLandingCycle
    (target start : Nat) (parent : PhaseSearchNode) (crossingTime : Nat)
    where
  source : PermanentTailDischargeReturnCertificate target start parent
  value : Nat
  parentTime : Nat
  landingTime : Nat
  value_below : value < target
  landing_first : FirstAt a value landingTime
  next_crossing : FirstWeakUpcrossingStep target landingTime crossingTime
  crossing_before_start : crossingTime + 1 ≤ start
  core : TailFixedPointCore target parent crossingTime
  after_parent : parentTime < landingTime
  downcross_before_parent : source.downTime < parentTime

namespace RefinedLandingCycle

variable {target start : Nat} {parent : PhaseSearchNode} {crossingTime : Nat}

/-- The landing value sits below the target. -/
theorem landing_below (r : RefinedLandingCycle target start parent
    crossingTime) : a r.landingTime < target := by
  rw [r.landing_first.1]
  exact r.value_below

/-- The discharge downcross precedes the landing, hence the crossing clock:
this is the restored prefix bound. -/
theorem downTime_lt_crossingTime
    (r : RefinedLandingCycle target start parent crossingTime) :
    r.source.downTime < crossingTime := by
  have hafter := r.after_parent
  have hcursor := r.downcross_before_parent
  have hstart := r.next_crossing.crossing.start_le
  omega

/-- Restored record exclusion: the downcross value dominates the crossing
value, so the landing clock is never an orbit record. -/
theorem crossingTime_not_record
    (r : RefinedLandingCycle target start parent crossingTime) :
    ∃ time, time < crossingTime ∧ a crossingTime < a time := by
  have habove := r.source.downcross.start_at_or_above
  exact r.core.crossingTime_not_record_of_prefixAbove
    (witnessTime := r.source.downTime) r.downTime_lt_crossingTime habove

/-- Restored prefix bound in the form the band eliminations consume. -/
theorem target_le_prefixValue
    (r : RefinedLandingCycle target start parent crossingTime) :
    ∃ time, time < crossingTime ∧ target ≤ a time :=
  ⟨r.source.downTime, r.downTime_lt_crossingTime,
    r.source.downcross.start_at_or_above⟩

/-- Payoff: the refined landing clock is at least thirty-two, with no
`target = 19` escape.  The shared kernel floor for the same core is only
`18 ≤ crossingTime ∨ target = 19`. -/
theorem thirtytwo_le_crossingTime
    (r : RefinedLandingCycle target start parent crossingTime) :
    32 ≤ crossingTime := by
  have hmissing := r.source.historical_tail.target_missing
  have hnineteen := r.core.nineteen_le_target hmissing
  exact r.source.thirtytwo_le_crossingTime_of_downcrossBefore hnineteen
    r.downTime_lt_crossingTime

/-- The refined landing target inherits the same floor as the core. -/
theorem nineteen_le_target
    (r : RefinedLandingCycle target start parent crossingTime) :
    19 ≤ target :=
  r.core.nineteen_le_target r.source.historical_tail.target_missing

end RefinedLandingCycle

/-- Additive strengthening of the unified outcome.  If the landing branch is
refined — that is, if the history edge behind it keeps its discharge cursor
— then both fixed-point branches carry the clock floor thirty-two, with no
deep-straggler escape on either side. -/
theorem PermanentTailUnifiedOutcome.semantic_or_thirtytwo_of_refinedLanding
    {target start : Nat}
    (h : PermanentTailUnifiedOutcome target start)
    (hrefine : ∀ (parent : PhaseSearchNode)
      (minimumTime predecessorFirstTime value landingTime crossingTime : Nat),
      PermanentTailCombinedCertificate target start parent minimumTime
        predecessorFirstTime →
      value < target → FirstAt a value landingTime →
      FirstWeakUpcrossingStep target landingTime crossingTime →
      crossingTime + 1 ≤ start →
      TailFixedPointCore target parent crossingTime →
      Nonempty (RefinedLandingCycle target start parent crossingTime)) :
    (∃ stepParent child : PhaseSearchNode,
      PhaseSemanticInvariant target child ∧
        PhaseSearchProgress target child stepParent) ∨
    (∃ (parent : PhaseSearchNode) (crossingTime : Nat),
      ∃ _core : TailFixedPointCore target parent crossingTime,
        32 ≤ crossingTime ∧ 19 ≤ target) := by
  cases h with
  | semantic_progress stepParent child semantic progress =>
      exact Or.inl ⟨stepParent, child, semantic, progress⟩
  | discharge_replay replayParent replaySource replay core =>
      have hmissing := replay.target_missing
      have hfloor := replay.onehundredtwelve_le_crossingTime
      exact Or.inr ⟨replayParent, replay.crossingTime, core, by omega,
        core.nineteen_le_target hmissing⟩
  | landing_cycle parent minimumTime predecessorFirstTime combined value
      landingTime crossingTime value_below landing_first next_crossing
      crossing_before_start core =>
      rcases hrefine parent minimumTime predecessorFirstTime value
        landingTime crossingTime combined value_below landing_first
        next_crossing crossing_before_start core with ⟨r⟩
      exact Or.inr ⟨parent, crossingTime, core, r.thirtytwo_le_crossingTime,
        r.nineteen_le_target⟩

/-- Unconditional companion of the previous theorem.  With no extra
hypothesis the unified outcome already splits into a semantic child, a
fixed-point core with clock floor thirty-two, or a residue consisting of the
two pinned deep stragglers and the clocks that carry an above-target prefix
event.  The refined landing interface removes the third alternative on the
landing side, exactly as the downcross removes it on the replay side. -/
theorem PermanentTailUnifiedOutcome.semantic_or_thirtytwo_or_residue
    {target start : Nat}
    (h : PermanentTailUnifiedOutcome target start) :
    (∃ stepParent child : PhaseSearchNode,
      PhaseSemanticInvariant target child ∧
        PhaseSearchProgress target child stepParent) ∨
    (∃ (parent : PhaseSearchNode) (crossingTime : Nat),
      ∃ _core : TailFixedPointCore target parent crossingTime,
        32 ≤ crossingTime ∧ 19 ≤ target) ∨
    (∃ (parent : PhaseSearchNode) (crossingTime : Nat),
      ∃ _core : TailFixedPointCore target parent crossingTime,
        ((crossingTime = 6 ∧ target = 19) ∨
          (crossingTime = 18 ∧ target = 61) ∨
          (∃ time, time < crossingTime ∧ target ≤ a time)) ∧
        19 ≤ target) := by
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
      rcases core.thirtytwo_or_straggler_or_prefixAbove hmissing with
        hfloor | hsix | heighteen | habove
      · exact Or.inr (Or.inl ⟨parent, crossingTime, core, hfloor, hnineteen⟩)
      · exact Or.inr (Or.inr ⟨parent, crossingTime, core, Or.inl hsix,
          hnineteen⟩)
      · exact Or.inr (Or.inr ⟨parent, crossingTime, core,
          Or.inr (Or.inl heighteen), hnineteen⟩)
      · exact Or.inr (Or.inr ⟨parent, crossingTime, core,
          Or.inr (Or.inr habove), hnineteen⟩)

/-- Summit form of the same strengthening. -/
theorem LeastMissingTarget.semantic_or_thirtytwo_of_refinedLanding
    {target : Nat} (h : LeastMissingTarget target)
    (hrefine : ∀ (start : Nat) (parent : PhaseSearchNode)
      (minimumTime predecessorFirstTime value landingTime crossingTime : Nat),
      PermanentTailCombinedCertificate target start parent minimumTime
        predecessorFirstTime →
      value < target → FirstAt a value landingTime →
      FirstWeakUpcrossingStep target landingTime crossingTime →
      crossingTime + 1 ≤ start →
      TailFixedPointCore target parent crossingTime →
      Nonempty (RefinedLandingCycle target start parent crossingTime)) :
    (∃ stepParent child : PhaseSearchNode,
      PhaseSemanticInvariant target child ∧
        PhaseSearchProgress target child stepParent) ∨
    (∃ (parent : PhaseSearchNode) (crossingTime : Nat),
      ∃ _core : TailFixedPointCore target parent crossingTime,
        32 ≤ crossingTime ∧ 19 ≤ target) := by
  rcases h.exists_missingPermanentAboveTail with ⟨start, htail⟩
  rcases htail.exists_combinedCertificate with
    ⟨crossingNode, minimumTime, predecessorFirstTime, hcombined⟩
  exact hcombined.unifiedOutcome.semantic_or_thirtytwo_of_refinedLanding
    (hrefine start)

end

end Recaman
