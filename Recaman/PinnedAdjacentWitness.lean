import Recaman.PinnedRemainingRows

namespace Recaman

noncomputable section

/-! # The adjacent early witnesses of the adding row

`PinnedRemainingRows.lastRow_blocked_witness` showed that the adding row of
the pinned backward dichotomy forces the value `target - 2 * clock + 1` into
the history at or before `clock - 1`, while the row itself stores
`a (clock - 2) = target - 2 * clock + 2`, one above it.  This module works out
what that pair of adjacent early values costs.

Three results.

* The pinned clock is at least six.  The window `2 * clock + 2 < target` and
  `target + 1 <= upperTri clock` alone only give five; the clock five is then
  removed by the actual orbit value `a 5 = 7`.
* The blocked witness cannot sit at `clock - 1` or at `clock - 2`, because the
  row pins both of those values and neither equals it.  So the witness lives
  at or before `clock - 3`, and the upper triangular bound applies there.
  This narrows the top of the clock window by `clock - 3`, from
  `target + 1 <= upperTri clock` to `target <= upperTri (clock - 3) + 2 *
  clock - 1`.
* The second backward step is a forced addition as well, and its own blocked
  cause is pinned to a third early value.

The narrowing is real but not lethal: substituting the lower end
`2 * clock + 3 <= target` into the new upper end only reproduces
`clock >= 6`.  What the row still needs is stated at the end — an argument
that limits how many large values may sit on small times, rather than one
more early witness, because each forced addition supplies another witness and
the chain does not close.
-/

namespace PinnedTailMinimumConfiguration

variable {target clock : Nat}

/-- The pinned clock is at least six.  The clock window rules out one through
four outright; the clock five would need a target of thirteen or fourteen
carried by `a 5`, which is seven. -/
theorem six_le_clock (h : PinnedTailMinimumConfiguration target clock) :
    6 ≤ clock := by
  have hpos := h.clock_pos
  have hbound := h.clock_bound
  have htri := h.upperTri_bound
  have hvalue := h.value_eq
  by_cases hone : clock = 1
  · subst hone
    have hone' : upperTri 1 = 1 := by decide
    omega
  · by_cases htwo : clock = 2
    · subst htwo
      have htwo' : upperTri 2 = 3 := by decide
      omega
    · by_cases hthree : clock = 3
      · subst hthree
        have hthree' : upperTri 3 = 6 := by decide
        omega
      · by_cases hfour : clock = 4
        · subst hfour
          have hfour' : upperTri 4 = 10 := by decide
          omega
        · by_cases hfive : clock = 5
          · subst hfive
            have hfive' : upperTri 5 = 15 := by decide
            have horbit : a 5 = 7 := by decide
            omega
          · omega

end PinnedTailMinimumConfiguration

namespace TerminalExactDischargeReplayCertificate

variable {target start : Nat} {parent : PhaseSearchNode}
variable {source : PermanentTailDischargeReturnCertificate target start parent}

/-- Numeric shape of the adding row, written additively. -/
theorem lastRow_values {base : Nat}
    (hp : PinnedTailMinimumConfiguration target (base + 2))
    (hprevious : a (base + 1) + base + 2 = target + 1)
    (hsecond : a base + 2 * base + 2 = target) :
    a (base + 1) + base + 1 = target ∧ a base + 2 * base + 2 = target ∧
      2 * base + 6 < target := by
  have hclock := hp.clock_bound
  exact ⟨by omega, hsecond, by omega⟩

/-- The blocked witness of the adding row occurs at or before `clock - 3`.
Neither of the two times the row pins can carry it: `clock - 1` holds a value
`base + 2` larger and `clock - 2` holds a value exactly one larger. -/
theorem lastRow_witness_early {base : Nat}
    (hp : PinnedTailMinimumConfiguration target (base + 2))
    (hprevious : a (base + 1) + base + 2 = target + 1)
    (hsecond : a base + 2 * base + 2 = target) :
    ∃ w, w + 1 ≤ base ∧ a w = target - 2 * base - 3 := by
  have hclock := hp.clock_bound
  have hmem := lastRow_blocked_witness hp hprevious
  rcases mem_valuesThrough_iff.mp hmem with ⟨w, hw, hvalue⟩
  refine ⟨w, ?_, hvalue⟩
  by_cases htop : w = base + 1
  · subst htop
    omega
  · by_cases hmid : w = base
    · subst hmid
      omega
    · omega

/-- Consequently the top of the clock window drops.  The witness sits at or
before `clock - 3`, so its value is bounded by the triangular number there,
which is smaller than the one at the clock by `3 * clock - 6`. -/
theorem lastRow_target_upper_bound {base : Nat}
    (hp : PinnedTailMinimumConfiguration target (base + 2))
    (hprevious : a (base + 1) + base + 2 = target + 1)
    (hsecond : a base + 2 * base + 2 = target) :
    target ≤ upperTri (base - 1) + 2 * base + 3 := by
  have hclock := hp.clock_bound
  rcases lastRow_witness_early hp hprevious hsecond with ⟨w, hw, hvalue⟩
  have hle : w ≤ base - 1 := by omega
  have hmono : upperTri w ≤ upperTri (base - 1) := upperTri_mono hle
  have hbound := a_le_upperTri w
  omega

/-- The narrowing made explicit.  Written at `base = c + 1`, the original
window allows `target ≤ upperTri c + 3 * c + 5` while the refined one allows
only `target ≤ upperTri c + 2 * c + 5`, a saving of `c` at the top. -/
theorem lastRow_window_narrowed {c : Nat}
    (hp : PinnedTailMinimumConfiguration target (c + 1 + 2))
    (hprevious : a (c + 1 + 1) + (c + 1) + 2 = target + 1)
    (hsecond : a (c + 1) + 2 * (c + 1) + 2 = target) :
    target ≤ upperTri c + 2 * c + 5 ∧
      target + 1 ≤ upperTri c + 3 * c + 6 := by
  have hrefined := lastRow_target_upper_bound hp hprevious hsecond
  have horiginal := hp.upperTri_bound
  have hexpand : upperTri (c + 1 + 2) = upperTri c + 3 * c + 6 := by
    simp only [upperTri]
    omega
  have hpred : c + 1 - 1 = c := by omega
  rw [hpred] at hrefined
  exact ⟨by omega, by omega⟩

/-- The earlier backward step is a forced addition too: a legal subtraction
there would have dropped the value by another `clock - 1`. -/
theorem lastRow_second_forced_addition {base : Nat}
    (hp : PinnedTailMinimumConfiguration target (base + 2))
    (hprevious : a (base + 1) + base + 2 = target + 1)
    (hsecond : a base + 2 * base + 2 = target) :
    ¬ CanSubtract (base + 1) (stateAt base) := by
  have hclock := hp.clock_bound
  intro hsub
  have hstep : a (base + 1) = a base - (base + 1) :=
    a_succ_of_canSubtract hsub
  have hpos : base + 1 < a base := hsub.1
  omega

/-- Its cause is pinned as well, so the row supplies a third early datum: the
value two clocks further down is either already stored at `clock - 2`, or the
stored value there is small enough to block subtraction outright. -/
theorem lastRow_second_witness {base : Nat}
    (hp : PinnedTailMinimumConfiguration target (base + 2))
    (hprevious : a (base + 1) + base + 2 = target + 1)
    (hsecond : a base + 2 * base + 2 = target) :
    a base ≤ base + 1 ∨ target - 3 * base - 3 ∈ valuesThrough base := by
  have hclock := hp.clock_bound
  have hnot := lastRow_second_forced_addition hp hprevious hsecond
  rcases not_canSubtract_cases hnot with hsmall | hseen
  · exact Or.inl hsmall
  · right
    have hrewrite : a base - (base + 1) = target - 3 * base - 3 := by omega
    rw [hrewrite] at hseen
    exact hseen

end TerminalExactDischargeReplayCertificate

end

end Recaman
