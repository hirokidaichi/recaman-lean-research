import Recaman.TailStartTwoSided
import Recaman.PermanentAboveCorridorReplayFloorFour

namespace Recaman

noncomputable section

/-! # The coverage time, the last free parameter of the counting route

The two-sided bound reduced the tail start to a single unknown: the time by
which every value below the target has occurred.  This module makes that
unknown a first-class object and settles everything about it except the one
thing that is genuinely open.

`CoversBelow target n` says the history at time `n` holds every value below
the target.  Like the tail-start predicate it is upward closed, so only its
least witness carries information; that least witness is the coverage time.
Three facts pin it down.  It is at least `target - 1`, by the pigeonhole.  It
is a first occurrence of a value below the target, since minimality means the
last missing level is supplied at exactly that step.  And it determines the
least tail start outright: `least = coverage + 1` whenever the coverage time
has reached the target.

So the counting route is now a single inequality away from being quantitative.
What is missing is an upper bound `coverage ≤ g target` for some explicit `g`.
Nothing in the present toolkit produces one, and the reason is structural
rather than tactical.  Every tool here bounds the count of covered levels from
above, which bounds the coverage time from *below*.  An upper bound needs the
opposite kind of statement: that an uncovered level below the target forces
the orbit to return to the low region within a controlled number of steps.
The orbit bound `a n ≤ upperTri n` does not supply that, since it also only
limits how high the orbit is, never how soon it comes back down.  The missing
ingredient is a return-frequency lemma, and it is stated here as the explicit
hypothesis of `least_tailStart_le_of_coverage_bound`.
-/

/-- The history at time `n` holds every value below `target`. -/
def CoversBelow (target n : Nat) : Prop :=
  ∀ v, v < target → v ∈ valuesThrough n

/-- Coverage is upward closed. -/
theorem CoversBelow.mono {target n n' : Nat}
    (h : CoversBelow target n) (hle : n ≤ n') : CoversBelow target n' :=
  fun v hv => valuesThrough_mono hle (h v hv)

/-- Hence coverage times have no upper bound, and only the least one carries
information. -/
theorem coversBelow_no_upper_bound {target n : Nat}
    (h : CoversBelow target n) (bound : Nat) :
    ∃ n', bound ≤ n' ∧ CoversBelow target n' :=
  ⟨max n bound, Nat.le_max_right _ _, h.mono (Nat.le_max_left _ _)⟩

/-- The least coverage time exists. -/
theorem exists_least_coversBelow {target : Nat}
    (hex : ∃ n, CoversBelow target n) :
    ∃ least, CoversBelow target least ∧
      ∀ n, CoversBelow target n → least ≤ n := by
  rcases hex with ⟨n, hn⟩
  exact exists_least_of_bounded n n (Nat.le_refl n) hn

/-- Pigeonhole lower bound: covering `target` levels needs `target` slots. -/
theorem coversBelow_pigeonhole {target n : Nat}
    (h : CoversBelow target n) : target ≤ n + 1 := by
  have hfull : coveredBelowCount target n = target :=
    coveredBelowCount_eq_of_covered target h
  have hbound := coveredBelowCount_le_time target n
  omega

/-- The coverage time is a first occurrence of a value below the target: at a
least coverage time the last missing level is supplied by that very step. -/
theorem least_coversBelow_firstAt {target least : Nat}
    (hcov : CoversBelow target least)
    (hmin : ∀ n, CoversBelow target n → least ≤ n)
    (hpos : 0 < least) :
    a least < target ∧ FirstAt a (a least) least := by
  have hnot : ¬ CoversBelow target (least - 1) := by
    intro hc
    have hle := hmin _ hc
    omega
  by_cases hex : ∃ v, v < target ∧ v ∉ valuesThrough (least - 1)
  · rcases hex with ⟨v, hv, hvnot⟩
    have hsucc : least - 1 + 1 = least := by omega
    have hmem := hcov v hv
    rw [← hsucc, valuesThrough_succ] at hmem
    rcases List.mem_cons.mp hmem with heq | hin
    · rw [hsucc] at heq
      subst heq
      refine ⟨hv, rfl, ?_⟩
      intro u hu hua
      exact hvnot (mem_valuesThrough_iff.mpr ⟨u, by omega, hua⟩)
    · exact absurd hin hvnot
  · exfalso
    apply hnot
    intro v hv
    by_cases hm : v ∈ valuesThrough (least - 1)
    · exact hm
    · exact absurd ⟨v, hv, hm⟩ hex

/-- The coverage time sits strictly below every valid tail start. -/
theorem least_coversBelow_lt_tailStart {target coverage s : Nat}
    (hcov : CoversBelow target coverage)
    (hcovmin : ∀ n, CoversBelow target n → coverage ≤ n)
    (hspec : MissingStrictAboveTail target s) :
    coverage < s := by
  have hpos := missingStrictAboveTail_pos hspec
  have hbefore : CoversBelow target (s - 1) :=
    covered_before_tailStart hspec hcov
  have hle := hcovmin _ hbefore
  omega

/-- Determination: once the coverage time has reached the target, the least
tail start is exactly one past it.  The tail start is no longer an independent
quantity. -/
theorem least_tailStart_eq_coverage_succ {target coverage least : Nat}
    (hcov : CoversBelow target coverage)
    (hcovmin : ∀ n, CoversBelow target n → coverage ≤ n)
    (hspec : MissingStrictAboveTail target least)
    (hmin : ∀ s, MissingStrictAboveTail target s → least ≤ s)
    (hlate : target ≤ coverage) :
    least = coverage + 1 := by
  have hlow := least_coversBelow_lt_tailStart hcov hcovmin hspec
  have hup := tailStart_le_of_minimal hspec.target_positive
    hspec.target_missing hcov hmin
  have hmax : max coverage target = coverage := Nat.max_eq_left hlate
  rw [hmax] at hup
  omega

/-- A step that revisits a stored value adds no covered level at all. -/
theorem coveredBelowCount_step_of_seen {n : Nat}
    (hseen : a (n + 1) ∈ valuesThrough n) :
    ∀ k, coveredBelowCount k (n + 1) = coveredBelowCount k n := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
      have hiff : (k ∈ valuesThrough (n + 1)) ↔ (k ∈ valuesThrough n) := by
        rw [valuesThrough_succ]
        constructor
        · intro hm
          rcases List.mem_cons.mp hm with heq | hin
          · rw [heq]
            exact hseen
          · exact hin
        · intro hm
          exact List.mem_cons.mpr (Or.inr hm)
      by_cases hmem : k ∈ valuesThrough n
      · simp only [coveredBelowCount_succ, if_pos hmem,
          if_pos (hiff.mpr hmem)]
        omega
      · have hnot : k ∉ valuesThrough (n + 1) := fun h => hmem (hiff.mp h)
        simp only [coveredBelowCount_succ, if_neg hmem, if_neg hnot]
        omega

/-- Chaining the one-step bound over a stretch of times. -/
theorem coveredBelowCount_le_add {k s : Nat} :
    ∀ n, s ≤ n → coveredBelowCount k n ≤ coveredBelowCount k s + (n - s) := by
  intro n
  induction n with
  | zero =>
      intro h
      have hzero : s = 0 := by omega
      subst hzero
      omega
  | succ n ih =>
      intro h
      rcases Nat.eq_or_lt_of_le h with heq | hlt
      · rw [heq]
        omega
      · have hs : s ≤ n := by omega
        have hstep := coveredBelowCount_step_le n k
        have hih := ih hs
        omega

/-- The orbit repeats a value at time twenty-four, so one slot is already
lost by then. -/
theorem revisit_at_twentyfour : a 24 ∈ valuesThrough 23 := by
  set_option maxRecDepth 100000 in decide

/-- Sharpened pigeonhole: past the first orbit repeat the coverage time can no
longer be one short of the target.  So the coverage time reaches the target,
and the determination below becomes unconditional. -/
theorem target_le_coversBelow {target n : Nat}
    (hcov : CoversBelow target n) (hbig : 25 ≤ target) : target ≤ n := by
  by_cases hsmall : n ≤ 23
  · have hp := coversBelow_pigeonhole hcov
    omega
  · have hstep : coveredBelowCount target 24 = coveredBelowCount target 23 :=
      coveredBelowCount_step_of_seen revisit_at_twentyfour target
    have h23 := coveredBelowCount_le_time target 23
    have hchain := coveredBelowCount_le_add (k := target) (s := 24) n
      (by omega)
    have hfull : coveredBelowCount target n = target :=
      coveredBelowCount_eq_of_covered target hcov
    omega

/-- Unconditional determination of the least tail start from the coverage
time. -/
theorem least_tailStart_eq_coverage_succ_of_large {target coverage least : Nat}
    (hcov : CoversBelow target coverage)
    (hcovmin : ∀ n, CoversBelow target n → coverage ≤ n)
    (hspec : MissingStrictAboveTail target least)
    (hmin : ∀ s, MissingStrictAboveTail target s → least ≤ s)
    (hbig : 25 ≤ target) :
    least = coverage + 1 :=
  least_tailStart_eq_coverage_succ hcov hcovmin hspec hmin
    (target_le_coversBelow hcov hbig)

/-- The reduction, with the missing ingredient isolated as a hypothesis: any
explicit coverage bound transfers directly to the least tail start. -/
theorem least_tailStart_le_of_coverage_bound {target g least : Nat}
    (hcov : CoversBelow target g)
    (hspec : MissingStrictAboveTail target least)
    (hmin : ∀ s, MissingStrictAboveTail target s → least ≤ s)
    (hlate : target ≤ g) :
    least ≤ g + 1 := by
  have hup := tailStart_le_of_minimal hspec.target_positive
    hspec.target_missing hcov hmin
  have hmax : max g target = g := Nat.max_eq_left hlate
  rw [hmax] at hup
  omega

namespace TerminalExactDischargeReplayCertificate

variable {target start : Nat} {parent : PhaseSearchNode}
variable {source : PermanentTailDischargeReturnCertificate target start parent}

/-- A surviving replay carries coverage, so its coverage time exists and is
characterised. -/
theorem exists_coverageTime
    (r : TerminalExactDischargeReplayCertificate source) :
    ∃ coverage, CoversBelow target coverage ∧
      (∀ n, CoversBelow target n → coverage ≤ n) ∧
      target ≤ coverage + 1 ∧
      coverage < source.tailStart := by
  have hex : ∃ n, CoversBelow target n :=
    ⟨source.tailStart - 1, r.belowTarget_covered_preTail⟩
  rcases exists_least_coversBelow hex with ⟨coverage, hcov, hmin⟩
  exact ⟨coverage, hcov, hmin, coversBelow_pigeonhole hcov,
    least_coversBelow_lt_tailStart hcov hmin source.historical_tail⟩

/-- Combined with the two-sided bound: the least tail start of a surviving
replay is exactly one past its coverage time, as soon as the coverage time
reaches the target. -/
theorem least_tailStart_determined
    (r : TerminalExactDischargeReplayCertificate source) :
    ∃ coverage least, CoversBelow target coverage ∧
      (∀ n, CoversBelow target n → coverage ≤ n) ∧
      MissingStrictAboveTail target least ∧
      (∀ s, MissingStrictAboveTail target s → least ≤ s) ∧
      target ≤ least ∧
      coverage < least ∧
      (target ≤ coverage → least = coverage + 1) := by
  rcases r.exists_coverageTime with ⟨coverage, hcov, hcovmin, _, _⟩
  have hexTail : ∃ s, MissingStrictAboveTail target s :=
    ⟨source.tailStart, source.historical_tail⟩
  rcases exists_least_missingStrictAboveTail hexTail with
    ⟨least, hspec, hmin⟩
  exact ⟨coverage, least, hcov, hcovmin, hspec, hmin,
    target_le_tailStart hspec hcov,
    least_coversBelow_lt_tailStart hcov hcovmin hspec,
    fun hlate => least_tailStart_eq_coverage_succ hcov hcovmin hspec hmin
      hlate⟩

/-- Unconditional for a surviving replay: the target floor clears
twenty-five, so the least tail start is exactly one past the coverage time.
The counting route now has a single unknown, and it is the coverage time. -/
theorem least_tailStart_eq_coverage_succ_final
    (r : TerminalExactDischargeReplayCertificate source) :
    ∃ coverage least, CoversBelow target coverage ∧
      (∀ n, CoversBelow target n → coverage ≤ n) ∧
      MissingStrictAboveTail target least ∧
      (∀ s, MissingStrictAboveTail target s → least ≤ s) ∧
      target ≤ coverage ∧
      least = coverage + 1 := by
  have hbig : 25 ≤ target := by
    have := r.onehundredfourteen_le_target
    omega
  rcases r.exists_coverageTime with ⟨coverage, hcov, hcovmin, _, _⟩
  have hexTail : ∃ s, MissingStrictAboveTail target s :=
    ⟨source.tailStart, source.historical_tail⟩
  rcases exists_least_missingStrictAboveTail hexTail with
    ⟨least, hspec, hmin⟩
  exact ⟨coverage, least, hcov, hcovmin, hspec, hmin,
    target_le_coversBelow hcov hbig,
    least_tailStart_eq_coverage_succ_of_large hcov hcovmin hspec hmin hbig⟩

end TerminalExactDischargeReplayCertificate

end

end Recaman
