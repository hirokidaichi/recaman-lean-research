import Recaman.TargetCandidateTransitions

namespace Recaman

set_option maxRecDepth 100000

/-! # A concrete limit of the ungated comb-order conjecture

The target-relative probe only records maximal combs entered from an H→L
candidate transition for one fixed missing target.  If those gates are
dropped, even actual Recamán history-terminated combs exhibit a right-left-right
pattern.  The three singleton episodes below kernel-check that distinction.
-/

private theorem historyTerminatedComb_187 :
    HistoryTerminatedComb 187 0 265 := by
  refine
    { episode :=
        { entry_first := ?_
          run := ?_ }
      final_forced := by decide
      blocker_eq := by decide
      blocker_seen := by decide }
  · simpa using firstAt_succ_of_canSubtract
      (n := 186) (by decide : CanSubtract 187 (stateAt 186))
  · intro i hi
    omega

private theorem historyTerminatedComb_222 :
    HistoryTerminatedComb 222 0 46 := by
  refine
    { episode :=
        { entry_first := ?_
          run := ?_ }
      final_forced := by decide
      blocker_eq := by decide
      blocker_seen := by decide }
  · simpa using firstAt_succ_of_canSubtract
      (n := 221) (by decide : CanSubtract 222 (stateAt 221))
  · intro i hi
    omega

private theorem historyTerminatedComb_285 :
    HistoryTerminatedComb 285 0 228 := by
  refine
    { episode :=
        { entry_first := ?_
          run := ?_ }
      final_forced := by decide
      blocker_eq := by decide
      blocker_seen := by decide }
  · simpa using firstAt_succ_of_canSubtract
      (n := 284) (by decide : CanSubtract 285 (stateAt 284))
  · intro i hi
    omega

/-- The ungated global right-record claim is false on the exact orbit:
the blocker sequence `265 → 46 → 228` goes locally upward at the last
edge, while the older singleton fresh interval has entry `266 > 228`. -/
theorem ungated_upward_reset_not_global_right_record :
    HistoryTerminatedComb 187 0 265 ∧
      HistoryTerminatedComb 222 0 46 ∧
      HistoryTerminatedComb 285 0 228 ∧
      187 < 222 ∧ 222 < 285 ∧
      46 < 228 ∧ 228 < a 187 := by
  exact ⟨historyTerminatedComb_187, historyTerminatedComb_222,
    historyTerminatedComb_285, by decide, by decide, by decide, by decide⟩

/-- The old episode is excluded by the fixed-target `m=19` probe because its
entry exposes a high, rather than low, next subtraction candidate. -/
theorem counterexample_old_entry_not_targetLow :
    ¬ nextSubtractionCandidate 187 < 19 := by
  decide

end Recaman
