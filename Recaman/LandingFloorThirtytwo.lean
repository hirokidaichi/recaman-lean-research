import Recaman.RefinedLandingOutcome

namespace Recaman

noncomputable section

/-! # Unconditional clock floor thirty-two for the landing fixed point

The terminal history edge now carries `TerminalHistoryCursor`, a source-free
record of the orbit content that every generation site of such an edge
already had: an above-target predecessor cursor strictly before the parent
time, pinned as the numeric predecessor of a tail minimum whose tail begins
after every low orbit value.  The anchored interface transports the cursor
from the parent time to the landing time, and the landing fixed point
inherits it.

That is exactly the datum the discharge replay obtains from its downcross.
With it, revisit elimination fires on the landing side too: a cursor below
time thirty-one has its successor value witnessed inside the kernel prefix,
so the pinned tail minimum would be a forbidden late revisit.  The landing
clock is therefore at least thirty-two, unconditionally and with no
`target = 19` escape, and both fixed-point branches of the unified outcome
now carry that floor.
-/

namespace TerminalHistoryCursor

/-- Record exclusion and the prefix bound, straight from the cursor. -/
theorem aboveTarget_before {target bound : Nat}
    (h : TerminalHistoryCursor target bound) :
    ∃ time, time < bound ∧ target < a time := by
  rcases h with ⟨cursorTime, minimumTime, tailStart, hlt, habove, _, _, _⟩
  exact ⟨cursorTime, hlt, habove⟩

/-- A cursor inside the kernel prefix is impossible once the target floor
nineteen is available: its pinned tail minimum would revisit a value whose
occurrence and size both predate the tail. -/
theorem thirtytwo_le_bound {target bound : Nat}
    (h : TerminalHistoryCursor target bound)
    (hnineteen : 19 ≤ target) : 32 ≤ bound := by
  by_cases hbig : 32 ≤ bound
  · exact hbig
  · rcases h with ⟨cursorTime, minimumTime, tailStart, hlt, habove,
      hsuccessor, htail, hlow⟩
    rcases prefixCursor_successor_witness hnineteen habove (by omega) with
      ⟨witness, hwitnessTime, hwitnessValue, hwitnessSuccessor⟩
    have hkernel : a 131 = 4 := by
      set_option maxRecDepth 100000 in decide
    have hcutoff := hlow 131 (by omega)
    have hvalue : a minimumTime = a witness := by omega
    exact False.elim (value_no_late_recurrence (v := a witness)
      (w := witness) (m := minimumTime) rfl (by omega) (by omega) hvalue)

end TerminalHistoryCursor

/-- Landing payoff: the landing fixed-point clock is at least thirty-two.
The shared kernel floor for the same core is only
`18 ≤ crossingTime ∨ target = 19`. -/
theorem landing_thirtytwo_le_crossingTime
    {target landingTime crossingTime : Nat} {parent : PhaseSearchNode}
    (core : TailFixedPointCore target parent crossingTime)
    (missing : ¬ ∃ time, a time = target)
    (next_crossing : FirstWeakUpcrossingStep target landingTime crossingTime)
    (landing_cursor : TerminalHistoryCursor target landingTime) :
    32 ≤ crossingTime := by
  have hnineteen := core.nineteen_le_target missing
  have hfloor := landing_cursor.thirtytwo_le_bound hnineteen
  have hstart := next_crossing.crossing.start_le
  omega

/-- Record exclusion for the landing fixed point, now unconditional. -/
theorem landing_crossingTime_not_record
    {target landingTime crossingTime : Nat} {parent : PhaseSearchNode}
    (core : TailFixedPointCore target parent crossingTime)
    (next_crossing : FirstWeakUpcrossingStep target landingTime crossingTime)
    (landing_cursor : TerminalHistoryCursor target landingTime) :
    ∃ time, time < crossingTime ∧ a crossingTime < a time := by
  rcases landing_cursor.aboveTarget_before with ⟨time, hlt, habove⟩
  have hstart := next_crossing.crossing.start_le
  exact core.crossingTime_not_record_of_prefixAbove (witnessTime := time)
    (by omega) (by omega)

/-- Unified outcome with both fixed-point branches floored at thirty-two:
the replay by its own kernel sweep, the landing by the transported
cursor. -/
theorem PermanentTailUnifiedOutcome.semantic_or_thirtytwo
    {target start : Nat} (h : PermanentTailUnifiedOutcome target start) :
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
      crossing_before_start core landing_cursor =>
      have hmissing := combined.tail.target_missing
      exact Or.inr ⟨parent, crossingTime, core,
        landing_thirtytwo_le_crossingTime core hmissing next_crossing
          landing_cursor,
        core.nineteen_le_target hmissing⟩

/-- Summit: a least missing target hands the outer recursion a semantic
phase child, or a fixed-point core whose crossing clock is at least
thirty-two and whose target is at least nineteen. -/
theorem LeastMissingTarget.semantic_or_thirtytwo
    {target : Nat} (h : LeastMissingTarget target) :
    (∃ stepParent child : PhaseSearchNode,
      PhaseSemanticInvariant target child ∧
        PhaseSearchProgress target child stepParent) ∨
    (∃ (parent : PhaseSearchNode) (crossingTime : Nat),
      ∃ _core : TailFixedPointCore target parent crossingTime,
        32 ≤ crossingTime ∧ 19 ≤ target) := by
  rcases h.exists_missingPermanentAboveTail with ⟨start, htail⟩
  rcases htail.exists_combinedCertificate with
    ⟨crossingNode, minimumTime, predecessorFirstTime, hcombined⟩
  exact hcombined.unifiedOutcome.semantic_or_thirtytwo

end

end Recaman
