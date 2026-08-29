import Recaman.PermanentAboveCorridorNineteenRevisit

namespace Recaman

noncomputable section

/-! # Elimination of the nineteen replay

A seen value can never recur at a clock larger than itself: a subtraction
landing must be fresh, and an addition lands at or above its own clock.
Twenty-one is seen at time nine, so it can never recur after time
twenty-one — but the nineteen counterexample forces exactly such a
recurrence after time 131.  The nineteen replay is therefore impossible,
with no computation beyond the verified prefix.

This removes the exceptional target nineteen from every kernel floor: the
replay crossing clock is at least eighteen unconditionally, at least
thirty-two unless the target is sixty-one, and the replay target is at
least twenty.
-/

/-- A value already seen cannot recur at a strictly larger clock: the
subtraction branch demands freshness and the addition branch overshoots. -/
theorem a_succ_ne_of_seen {v n : Nat}
    (hseen : v ∈ valuesThrough n) (hlt : v < n + 1) :
    a (n + 1) ≠ v := by
  intro heq
  by_cases hcan : CanSubtract (n + 1) (stateAt n)
  · have hval := a_succ_of_canSubtract hcan
    apply hcan.2
    have hdefect : (stateAt n).value - (n + 1) = v := by
      have hvalue : (stateAt n).value = a n := rfl
      omega
    rw [hdefect]
    exact hseen
  · have hval := a_succ_of_not_canSubtract hcan
    omega

/-- Twenty-one never recurs after time twenty-one. -/
theorem twentyone_no_late_revisit :
    ∀ t, 21 < t → a t ≠ 21 := by
  intro t ht
  have hnine : a 9 = 21 := by decide
  rcases Nat.exists_eq_add_of_lt ht with ⟨n, rfl⟩
  have hmem : (21 : Nat) ∈ valuesThrough 9 :=
    mem_valuesThrough_iff.mpr ⟨9, Nat.le_refl 9, hnine⟩
  have hseen : (21 : Nat) ∈ valuesThrough (21 + n) :=
    valuesThrough_mono (by omega) hmem
  have harith : 21 + n + 1 = (21 + n) + 1 := rfl
  rw [harith]
  exact a_succ_ne_of_seen hseen (by omega)

namespace TerminalExactDischargeReplayCertificate

variable {target start : Nat} {parent : PhaseSearchNode}
variable {source : PermanentTailDischargeReturnCertificate target start parent}

/-- The nineteen replay is impossible: it forces a late twenty-one revisit
which the orbit dynamics forbid. -/
theorem target_ne_nineteen
    (r : TerminalExactDischargeReplayCertificate source) :
    target ≠ 19 := by
  intro h19
  rcases r.nineteen_forces_twentyone_revisit h19 with ⟨t, ht, hvalue⟩
  exact twentyone_no_late_revisit t (by omega) hvalue

/-- Unconditional second floor: the replay crossing clock is at least
eighteen. -/
theorem eighteen_le_crossingTime
    (r : TerminalExactDischargeReplayCertificate source) :
    18 ≤ r.crossingTime := by
  rcases r.eighteen_le_crossingTime_or_target_eq_nineteen with hbig | h19
  · exact hbig
  · exact absurd h19 r.target_ne_nineteen

/-- Third floor with a single exception: clock at least thirty-two unless
the target is sixty-one. -/
theorem thirtytwo_le_crossingTime_or_sixtyone
    (r : TerminalExactDischargeReplayCertificate source) :
    32 ≤ r.crossingTime ∨ target = 61 := by
  rcases r.thirtytwo_le_crossingTime_or_exceptional with hbig | h19 | h61
  · exact Or.inl hbig
  · exact absurd h19 r.target_ne_nineteen
  · exact Or.inr h61

/-- The replay target is at least twenty. -/
theorem twenty_le_target
    (r : TerminalExactDischargeReplayCertificate source) :
    20 ≤ target := by
  have hnineteen := r.nineteen_le_target
  have hne := r.target_ne_nineteen
  omega

end TerminalExactDischargeReplayCertificate

end

end Recaman
