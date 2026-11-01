import Recaman.PinnedForwardOrbit

namespace Recaman

noncomputable section

/-! # Where the tail start can be placed, and why it has no upper bound

Three separate attacks have stalled on the same missing ingredient: an upper
bound for `tailStart`, or for the parent horizon that dominates it.  This
module settles the question.

The negative half is exact.  Every condition the certificate imposes on the
tail start is upward closed, so the field can be replaced by any larger value
and the certificate still holds.  `MissingStrictAboveTail.mono` and
`missingStrictAboveTail_no_upper_bound` say this outright: for any bound
whatsoever there is a valid tail start beyond it.  The same holds on the
horizon side.  Zero remaining budget survives moving the horizon forward, the
absence of a future downcross survives it as well, and the one condition that
is not obviously monotone — the orbit sitting above the target at the horizon
— turns out to follow from the other two.  So no theorem of the form
`tailStart ≤ g target` can be derived from the certificate as it stands.  The
wall is a property of the specification, not a gap in effort.

The positive half is the mechanism that a minimality field would activate.
Once every value below a level is stored, that level can never be revisited
from above: a later visit would repeat a value at a time exceeding the value,
which the freshness of subtraction and the overshoot of addition jointly
forbid.  `covered_forces_above` is that statement, and
`missingStrictAboveTail_of_covered` turns it into a tail start.  Coverage
therefore caps where the tail has to begin, and the certificate already
carries coverage — at the horizon through zero budget, and just before the
tail through the counting separation.  Adding a single field demanding that
`tailStart` be least among valid tail starts would pin it to within one of the
coverage time, which is what `tailStart_le_of_minimal` records.

What remains after that fix is one genuinely new combinatorial question: an
upper bound for the coverage time itself, the last moment at which a value
below the target receives its first occurrence.  That, and not the tail start,
is the quantity the counting route ultimately needs.
-/

/-- Zero remaining budget below a level means the level is fully covered. -/
theorem missingBelowCount_zero_covered {bound : Nat} :
    ∀ level, missingBelowCount level bound = 0 →
      ∀ v, v < level → v ∈ valuesThrough bound := by
  intro level
  induction level with
  | zero =>
      intro _ v hv
      exact False.elim (by omega)
  | succ level ih =>
      intro hzero v hv
      rw [missingBelowCount_succ] at hzero
      have hmem : level ∈ valuesThrough bound := by
        by_cases hcase : level ∈ valuesThrough bound
        · exact hcase
        · rw [if_neg hcase] at hzero
          omega
      have hrest : missingBelowCount level bound = 0 := by
        rw [if_pos hmem] at hzero
        omega
      rcases Nat.lt_or_ge v level with hlt | hge
      · exact ih hrest v hlt
      · have hveq : v = level := by omega
        rw [hveq]
        exact hmem

/-- Full coverage below a level bars the orbit from ever returning below that
level, once the clock has passed both the coverage time and the level itself.
A return would repeat a stored value at a time exceeding the value, which
neither transition can do. -/
theorem covered_forces_above {level bound : Nat}
    (hcov : ∀ v, v < level → v ∈ valuesThrough bound) :
    ∀ time, bound < time → level ≤ time → level ≤ a time := by
  intro time hbound hlevel
  by_cases hge : level ≤ a time
  · exact hge
  · exfalso
    have hlt : a time < level := by omega
    have hmem : a time ∈ valuesThrough bound := hcov _ hlt
    have hseen : a time ∈ valuesThrough (time - 1) :=
      valuesThrough_mono (by omega) hmem
    have hne := a_succ_ne_of_seen hseen
      (show a time < time - 1 + 1 by omega)
    apply hne
    have hsucc : time - 1 + 1 = time := by omega
    rw [hsucc]

/-- Coverage below the target therefore supplies a tail start outright. -/
theorem missingStrictAboveTail_of_covered {target bound : Nat}
    (hpos : 0 < target)
    (hmissing : ¬ ∃ time, a time = target)
    (hcov : ∀ v, v < target → v ∈ valuesThrough bound) :
    MissingStrictAboveTail target (max bound target + 1) := by
  refine ⟨hpos, hmissing, ?_⟩
  intro time htime
  have hleft := Nat.le_max_left bound target
  have hright := Nat.le_max_right bound target
  have hge := covered_forces_above hcov time (by omega) (by omega)
  rcases Nat.lt_or_ge target (a time) with hlt | hle
  · exact hlt
  · exact False.elim (hmissing ⟨time, by omega⟩)

/-- Zero remaining budget below the target is itself a coverage hypothesis. -/
theorem missingStrictAboveTail_of_budgetZero {target bound : Nat}
    (hpos : 0 < target)
    (hmissing : ¬ ∃ time, a time = target)
    (hzero : missingBelowCount target bound = 0) :
    MissingStrictAboveTail target (max bound target + 1) :=
  missingStrictAboveTail_of_covered hpos hmissing
    (missingBelowCount_zero_covered target hzero)

/-- Every tail-start condition is upward closed. -/
theorem MissingStrictAboveTail.mono {target s s' : Nat}
    (h : MissingStrictAboveTail target s) (hle : s ≤ s') :
    MissingStrictAboveTail target s' :=
  ⟨h.target_positive, h.target_missing,
    fun time htime => h.strictly_above time (by omega)⟩

/-- Hence the tail start has no upper bound: for any proposed bound there
is a valid tail start beyond it. -/
theorem missingStrictAboveTail_no_upper_bound {target s : Nat}
    (h : MissingStrictAboveTail target s) (bound : Nat) :
    ∃ s', bound ≤ s' ∧ MissingStrictAboveTail target s' :=
  ⟨max s bound, Nat.le_max_right _ _, h.mono (Nat.le_max_left _ _)⟩

/-- Zero remaining budget survives moving the horizon forward. -/
theorem missingBelowCount_zero_mono {target n n' : Nat}
    (hzero : missingBelowCount target n = 0) (hle : n ≤ n') :
    missingBelowCount target n' = 0 := by
  have hanti := missingBelowCount_antitone (m := target) hle
  omega

/-- The absence of a future downcross survives moving the horizon forward. -/
theorem no_future_downcross_mono {target n n' : Nat}
    (h : ¬ ∃ time, FutureDowncrossStep target n time) (hle : n ≤ n') :
    ¬ ∃ time, FutureDowncrossStep target n' time := by
  rintro ⟨time, hd⟩
  exact h ⟨time,
    { horizon_le_time := Nat.le_trans hle hd.horizon_le_time
      start_at_or_above := hd.start_at_or_above
      endpoint_below := hd.endpoint_below }⟩

/-- The remaining horizon condition is not independent: zero budget already
forces the orbit above the target at every sufficiently late horizon.  So all
three horizon conditions are upward closed and the horizon has no upper bound
either. -/
theorem horizon_strictly_above_of_budgetZero {target n : Nat}
    (hmissing : ¬ ∃ time, a time = target)
    (hzero : missingBelowCount target n = 0)
    (horizon : Nat) (hafter : n < horizon) (hlevel : target ≤ horizon) :
    target < a horizon := by
  have hge := covered_forces_above
    (missingBelowCount_zero_covered target hzero) horizon hafter hlevel
  rcases Nat.lt_or_ge target (a horizon) with hlt | hle
  · exact hlt
  · exact False.elim (hmissing ⟨horizon, by omega⟩)

/-- What the chronology cursor supplies is a lower bound on the tail start,
not an upper one: it says the tail start dominates every time at which the
orbit sits at or below the target. -/
theorem terminalHistoryCursor_lower_bound {target bound : Nat}
    (h : TerminalHistoryCursor target bound) :
    ∃ tailStart,
      (∀ witness, a witness ≤ target → witness < tailStart) ∧
        (∀ time, tailStart ≤ time → target < a time) := by
  rcases h with ⟨_, _, tailStart, _, _, _, _, hlow⟩
  refine ⟨tailStart, hlow, ?_⟩
  intro time htime
  rcases Nat.lt_or_ge target (a time) with hlt | hle
  · exact hlt
  · exact False.elim (by have := hlow time hle; omega)

/-- The minimal fix, stated as a theorem: a certificate whose tail start is
least among valid tail starts is capped by any coverage time. -/
theorem tailStart_le_of_minimal {target tailStart bound : Nat}
    (hpos : 0 < target)
    (hmissing : ¬ ∃ time, a time = target)
    (hcov : ∀ v, v < target → v ∈ valuesThrough bound)
    (hminimal : ∀ s, MissingStrictAboveTail target s → tailStart ≤ s) :
    tailStart ≤ max bound target + 1 :=
  hminimal _ (missingStrictAboveTail_of_covered hpos hmissing hcov)

namespace TerminalExactDischargeReplayCertificate

variable {target start : Nat} {parent : PhaseSearchNode}
variable {source : PermanentTailDischargeReturnCertificate target start parent}

/-- The certificate already carries coverage below the target at the parent
horizon, so the tail could have been started right after it. -/
theorem tailStart_available_at_horizon
    (_r : TerminalExactDischargeReplayCertificate source) :
    MissingStrictAboveTail target (max parent.horizon target + 1) :=
  missingStrictAboveTail_of_budgetZero
    source.historical_tail.target_positive
    source.historical_tail.target_missing
    source.combined.crossing.budget_zero

/-- It also carries coverage just before its own tail start, so the tail could
have been started there as well.  Both facts are caps on where a *minimal*
tail start could sit; neither caps the field the certificate actually
carries. -/
theorem tailStart_available_at_own_coverage
    (r : TerminalExactDischargeReplayCertificate source) :
    MissingStrictAboveTail target (max (source.tailStart - 1) target + 1) :=
  missingStrictAboveTail_of_covered
    source.historical_tail.target_positive
    source.historical_tail.target_missing
    r.belowTarget_covered_preTail

/-- Under a minimality field the tail start would be pinned to the coverage
time exactly: the counting separation already gives the lower half. -/
theorem tailStart_pinned_of_minimal
    (r : TerminalExactDischargeReplayCertificate source)
    (hminimal : ∀ s, MissingStrictAboveTail target s → source.tailStart ≤ s)
    (bound : Nat)
    (hcov : ∀ v, v < target → v ∈ valuesThrough bound)
    (hlate : target ≤ bound) :
    target < source.tailStart ∧ source.tailStart ≤ bound + 1 := by
  have hlow := r.target_lt_tailStart
  have hup := tailStart_le_of_minimal
    source.historical_tail.target_positive
    source.historical_tail.target_missing hcov hminimal
  have hmax : max bound target = bound := Nat.max_eq_left hlate
  rw [hmax] at hup
  exact ⟨hlow, hup⟩

/-- The certificate's own tail start can always be replaced by a larger one,
which is the exact obstruction: no upper bound is derivable. -/
theorem tailStart_replaceable
    (_r : TerminalExactDischargeReplayCertificate source) (bound : Nat) :
    ∃ s, bound ≤ s ∧ MissingStrictAboveTail target s :=
  missingStrictAboveTail_no_upper_bound source.historical_tail bound

end TerminalExactDischargeReplayCertificate

end

end Recaman
