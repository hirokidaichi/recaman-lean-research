import Recaman.CoverageTimeBound

namespace Recaman

noncomputable section

/-! # Return frequency, and why it is not a stepping stone

The counting route was reduced to a single unknown, an upper bound for the
coverage time, and the natural way to get one is a return-frequency lemma: an
uncovered level below the target should force the orbit back down within a
controlled number of steps.  This module works out what that lemma is worth,
and the answer is sharper than expected.

The failure mode of return frequency is completely characterised.  If the
orbit has settled above the target from some time onwards, then any level
below the target still uncovered at that moment is uncovered forever — after
the settling point the orbit is too high to supply it, and before it the
history already records everything it will ever hold.  So a run of
non-returns is possible only when a second value below the target is missing
from the whole orbit.  Under the least-missing-target hypothesis that the
certificates carry, no such second value exists, and coverage is therefore
complete before the tail begins.

That is exactly the trouble.  The same argument run backwards turns a
tail-start bound into a coverage bound, so the two quantities bound each
other.  Return frequency is not an ingredient of the tail-start bound; it is
the tail-start bound wearing different clothes.  Any proof of one is a proof
of the other, and the counting route cannot manufacture either from the
material it already has.

What the module does supply on the quantitative side is the honest half of the
estimate.  Consecutive steps move the orbit by the clock, so a descent from
above the target has a forced length: the drop cannot exceed the triangular
gap between the two times.  This is a lower bound on the return time, which is
the direction the existing tools were always going to give.  The defect
identities for a run of forced additions are recorded as well, since they show
what blocking costs: a run deposits a strictly increasing family of values
that must already be in the history.
-/

/-- A level below the target that is uncovered when the orbit settles above
the target is uncovered forever. -/
theorem uncovered_at_tail_never_occurs {target bound v : Nat}
    (hspec : MissingStrictAboveTail target bound)
    (hv : v < target)
    (hnot : ∀ t, t < bound → a t ≠ v) :
    ∀ t, a t ≠ v := by
  intro t heq
  by_cases hlt : t < bound
  · exact hnot t hlt heq
  · have habove := hspec.strictly_above t (by omega)
    omega

/-- A value the orbit never reaches blocks coverage at every time. -/
theorem never_occurs_blocks_coverage {target v : Nat}
    (hv : v < target) (hnever : ∀ t, a t ≠ v) :
    ∀ n, ¬ CoversBelow target n := by
  intro n hcov
  rcases mem_valuesThrough_iff.mp (hcov v hv) with ⟨t, _, hval⟩
  exact hnever t hval

/-- Complete characterisation of the failure of return frequency: once the
orbit has settled above the target, either coverage is already complete or a
second value below the target is missing from the whole orbit. -/
theorem returnFrequency_dichotomy {target bound : Nat}
    (hspec : MissingStrictAboveTail target bound) (hpos : 0 < bound) :
    CoversBelow target (bound - 1) ∨ ∃ v, v < target ∧ ∀ t, a t ≠ v := by
  by_cases hex : ∃ v, v < target ∧ v ∉ valuesThrough (bound - 1)
  · right
    rcases hex with ⟨v, hv, hvnot⟩
    refine ⟨v, hv, ?_⟩
    refine uncovered_at_tail_never_occurs hspec hv ?_
    intro t ht hval
    exact hvnot (mem_valuesThrough_iff.mpr ⟨t, by omega, hval⟩)
  · left
    intro v hv
    by_cases hm : v ∈ valuesThrough (bound - 1)
    · exact hm
    · exact absurd ⟨v, hv, hm⟩ hex

/-- Finitely many occurring levels can be collected at one time. -/
theorem exists_coversBelow_of_all_occur {target : Nat}
    (hocc : ∀ v, v < target → ∃ t, a t = v) : ∃ n, CoversBelow target n := by
  induction target with
  | zero => exact ⟨0, fun v hv => absurd hv (by omega)⟩
  | succ k ih =>
      rcases ih (fun v hv => hocc v (by omega)) with ⟨n, hn⟩
      rcases hocc k (by omega) with ⟨t, ht⟩
      refine ⟨max n t, fun v hv => ?_⟩
      rcases Nat.lt_or_ge v k with hlt | hge
      · exact valuesThrough_mono (Nat.le_max_left _ _) (hn v hlt)
      · have hvk : v = k := by omega
        rw [hvk]
        exact mem_valuesThrough_iff.mpr ⟨t, Nat.le_max_right _ _, ht⟩

/-- Under the least-missing-target hypothesis the second disjunct is empty, so
coverage is complete before the orbit settles.  This is the qualitative half
of return frequency, and it is free. -/
theorem coversBelow_before_tail_of_all_occur {target bound : Nat}
    (hspec : MissingStrictAboveTail target bound) (hpos : 0 < bound)
    (hocc : ∀ v, v < target → ∃ t, a t = v) :
    CoversBelow target (bound - 1) := by
  rcases returnFrequency_dichotomy hspec hpos with hcov | ⟨v, hv, hnever⟩
  · exact hcov
  · rcases hocc v hv with ⟨t, ht⟩
    exact absurd ht (hnever t)

/-- A tail-start bound yields a coverage bound.  Together with
`least_tailStart_le_of_coverage_bound` this makes the two quantities
interderivable: return frequency is the tail-start bound restated, not an
ingredient of it. -/
theorem coverage_le_of_tailStart_bound {target bound coverage : Nat}
    (hspec : MissingStrictAboveTail target bound) (hpos : 0 < bound)
    (hocc : ∀ v, v < target → ∃ t, a t = v)
    (hcovmin : ∀ n, CoversBelow target n → coverage ≤ n) :
    coverage ≤ bound - 1 :=
  hcovmin _ (coversBelow_before_tail_of_all_occur hspec hpos hocc)

/-- The decisive identification.  Return frequency at a horizon past the
target says the orbit never comes back below the target from that horizon on,
which is the tail-start statement at that horizon; under the least-missing
hypothesis it is equivalent to coverage at the horizon.  So the two open
quantities are one open quantity. -/
theorem returnFrequency_iff_coverage {target g : Nat}
    (hpos : 0 < target)
    (hmissing : ¬ ∃ time, a time = target)
    (hocc : ∀ v, v < target → ∃ t, a t = v)
    (hlate : target ≤ g) :
    CoversBelow target g ↔ MissingStrictAboveTail target (g + 1) := by
  have hmax : max g target = g := Nat.max_eq_left hlate
  constructor
  · intro hcov
    have hres := missingStrictAboveTail_of_covered hpos hmissing hcov
    rw [hmax] at hres
    exact hres
  · intro hspec
    have hcov := coversBelow_before_tail_of_all_occur hspec (by omega) hocc
    have hsucc : g + 1 - 1 = g := by omega
    rw [hsucc] at hcov
    exact hcov

/-- Steps move the orbit by the clock, so the value cannot fall faster than
the triangular gap between two times. -/
theorem drop_le_upperTri_gap {s : Nat} :
    ∀ t, s ≤ t → a s ≤ a t + (upperTri t - upperTri s) := by
  intro t
  induction t with
  | zero =>
      intro hle
      have hzero : s = 0 := by omega
      subst hzero
      omega
  | succ t ih =>
      intro hle
      rcases Nat.eq_or_lt_of_le hle with heq | hlt
      · rw [heq]
        omega
      · have hs : s ≤ t := by omega
        have hih := ih hs
        have hmono : upperTri s ≤ upperTri t := upperTri_mono hs
        have hstep : upperTri (t + 1) = upperTri t + (t + 1) := by
          simp [upperTri]
          omega
        by_cases hcan : CanSubtract (t + 1) (stateAt t)
        · have hval := a_succ_of_canSubtract hcan
          have hpos : t + 1 < (stateAt t).value := hcan.1
          have hval' : (stateAt t).value = a t := rfl
          omega
        · have hval := a_succ_of_not_canSubtract hcan
          omega

/-- Forced return time: descending from at or above the target to strictly
below it takes long enough that the triangular gap covers the drop. -/
theorem return_time_lower_bound {target s t : Nat}
    (hst : s ≤ t) (habove : target ≤ a s) (hbelow : a t < target) :
    target - a t ≤ upperTri t - upperTri s := by
  have hdrop := drop_le_upperTri_gap t hst
  omega

/-- Defect identities for a run of forced additions.  Each blocked step
deposits a value that must already be stored, and past the first two the
deposited values strictly increase, so a long run costs a long strictly
increasing family of stored values. -/
theorem forced_addition_run_defects {t : Nat}
    (h1 : ¬ CanSubtract (t + 1) (stateAt t))
    (h2 : ¬ CanSubtract (t + 2) (stateAt (t + 1)))
    (hbig : t + 2 < a t) (ht : 0 < t) :
    a (t + 1) - (t + 2) = a t - 1 ∧
      a (t + 1) = a t + (t + 1) ∧
      a (t + 2) = a t + 2 * t + 3 ∧
      a t - (t + 1) < a t - 1 := by
  have hv1 := a_succ_of_not_canSubtract h1
  have hv2 : a (t + 2) = a (t + 1) + (t + 2) := by
    have hstep := a_succ_of_not_canSubtract (n := t + 1) h2
    simpa using hstep
  exact ⟨by omega, by omega, by omega, by omega⟩

namespace TerminalExactDischargeReplayCertificate

variable {target start : Nat} {parent : PhaseSearchNode}
variable {source : PermanentTailDischargeReturnCertificate target start parent}

/-- A surviving replay has every level below the target occurring somewhere:
the target is the least missing value. -/
theorem all_below_target_occur
    (_r : TerminalExactDischargeReplayCertificate source) :
    ∀ v, v < target → ∃ t, a t = v := by
  intro v hv
  rcases mem_valuesThrough_iff.mp
    (source.combined.tail.below_covered v hv) with ⟨t, _, hval⟩
  exact ⟨t, hval⟩

/-- Applied to a surviving replay: proving return frequency at any horizon
past the target is the same task as bounding its coverage time, which is the
same task as bounding its least tail start. -/
theorem returnFrequency_is_coverage
    (r : TerminalExactDischargeReplayCertificate source)
    (g : Nat) (hlate : target ≤ g) :
    CoversBelow target g ↔ MissingStrictAboveTail target (g + 1) :=
  returnFrequency_iff_coverage
    source.historical_tail.target_positive
    source.historical_tail.target_missing
    r.all_below_target_occur hlate

/-- The failure mode is empty for a surviving replay: no second missing value
below the target exists, so return frequency holds qualitatively and only its
quantitative form is open. -/
theorem returnFrequency_failure_mode_empty
    (r : TerminalExactDischargeReplayCertificate source) :
    ¬ ∃ v, v < target ∧ ∀ t, a t ≠ v := by
  rintro ⟨v, hv, hnever⟩
  rcases r.all_below_target_occur v hv with ⟨t, ht⟩
  exact hnever t ht

end TerminalExactDischargeReplayCertificate

end

end Recaman
