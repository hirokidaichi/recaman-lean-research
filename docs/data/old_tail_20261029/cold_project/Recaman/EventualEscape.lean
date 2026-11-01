import Recaman.History

namespace Recaman

/-!
An audit of the quantifiers in an eventual landing floor.

Every fixed value eventually disappears, whether or not it occurs at all.
Consequently an unspecified eventual floor is unconditional and cannot,
together with an unrelated finite prefix, certify a missing value.

These elementary results expose a missing quantitative input; they do not
decide surjectivity. Only the recurrence and persistent history are used.
-/

/-- A repeated value cannot be smaller than the clock of its later visit.
This is the two-occurrence form of the no-late-revisit mechanism. -/
theorem repeat_clock_le_value {v s t : Nat}
    (hst : s < t) (hs : a s = v) (ht : a t = v) : t ≤ v := by
  cases t with
  | zero => omega
  | succ n =>
      have hseen : v ∈ valuesThrough n :=
        mem_valuesThrough_iff.mpr ⟨s, by omega, hs⟩
      have hrec := recurrence n
      by_cases hcan : CanSubtract (n + 1) (stateAt n)
      · rw [if_pos hcan] at hrec
        have hdefect : (stateAt n).value - (n + 1) = v := by
          change a n - (n + 1) = v
          omega
        exact False.elim (hcan.2 (by
          rw [hdefect]
          exact hseen))
      · rw [if_neg hcan] at hrec
        omega

/-- Each value is eventually avoided. If it occurs, a cutoff may depend on
that occurrence; this theorem does not bound its first occurrence. -/
theorem eventually_ne_value (v : Nat) :
    ∃ N, ∀ n, N ≤ n → a n ≠ v := by
  classical
  by_cases hocc : ∃ s, a s = v
  · rcases hocc with ⟨s, hs⟩
    refine ⟨max s v + 1, ?_⟩
    intro n hn heq
    have hsn : s < n := by omega
    have hbound := repeat_clock_le_value hsn hs heq
    omega
  · exact ⟨0, fun n _ hn => hocc ⟨n, hn⟩⟩

/-- The canonical Recamán values tend to infinity in the elementary sense
of eventually exceeding every fixed bound. No missing-target hypothesis
and no coverage hypothesis is needed. The cutoff is not quantitative. -/
theorem eventually_above_every_bound (B : Nat) :
    ∃ N, ∀ n, N ≤ n → B < a n := by
  induction B with
  | zero =>
      rcases eventually_ne_value 0 with ⟨N, hN⟩
      refine ⟨N, ?_⟩
      intro n hn
      have hne := hN n hn
      omega
  | succ B ih =>
      rcases ih with ⟨N, hN⟩
      rcases eventually_ne_value (B + 1) with ⟨M, hM⟩
      refine ⟨max N M, ?_⟩
      intro n hn
      have hgt := hN n (by omega)
      have hne := hM n (by omega)
      omega

/-- Restricting an eventual floor to any selected clocks, including any
definition of arc bottoms, cannot make it a new obstruction. -/
theorem eventually_above_on_selected_times (selected : Nat → Prop) (B : Nat) :
    ∃ N, ∀ n, N ≤ n → selected n → B < a n := by
  rcases eventually_above_every_bound B with ⟨N, hN⟩
  exact ⟨N, fun n hn _ => hN n hn⟩

/-- The same cutoff must delimit both the checked prefix and the future
exclusion. This is a logical handoff contract, not a new invariant. -/
theorem missing_of_prefix_and_same_cutoff_floor {m H : Nat}
    (hprefix : m ∉ valuesThrough H)
    (hfuture : ∀ n, H < n → m < a n) :
    ∀ n, a n ≠ m := by
  intro n heq
  by_cases hn : n ≤ H
  · exact hprefix (mem_valuesThrough_iff.mpr ⟨n, hn, heq⟩)
  · have hgt := hfuture n (by omega)
    omega

set_option maxRecDepth 4096 in
/-- An actual canonical counterexample to combining a prefix hole with
an independently chosen eventual cutoff: 4 is absent through clock 4,
eventually lies below every value, and nevertheless occurs at clock 131. -/
theorem free_cutoff_does_not_certify_missing :
    4 ∉ valuesThrough 4 ∧
      (∃ N, ∀ n, N ≤ n → 4 < a n) ∧
      (∃ t, 4 < t ∧ a t = 4) := by
  refine ⟨by decide, eventually_above_every_bound 4, 131, by omega, ?_⟩
  decide

/-- A rising floor alone is compatible with surjectivity. This deliberately
weaker sequence model tests the inference, not the Recamán recurrence. -/
theorem rising_floor_compatible_with_surjectivity :
    ∃ b f : Nat → Nat,
      (∀ m, ∃ n, b n = m) ∧
      (∀ B, ∃ N, ∀ n, N ≤ n → B < f n) ∧
      (∀ n, 0 < n → f n < b n) := by
  refine ⟨(fun n => n), (fun n => n / 2), ?_, ?_, ?_⟩
  · exact fun m => ⟨m, rfl⟩
  · intro B
    refine ⟨2 * (B + 1), ?_⟩
    intro n hn
    change B < n / 2
    omega
  · intro n hn
    change n / 2 < n
    omega

end Recaman
