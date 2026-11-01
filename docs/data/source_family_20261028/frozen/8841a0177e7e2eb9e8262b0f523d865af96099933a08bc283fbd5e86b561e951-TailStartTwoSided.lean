import Recaman.TailStartHorizonBound

namespace Recaman

noncomputable section

/-! # A two-sided bound for the canonical tail start

The tail-start wall was shown to be a property of the specification: every
condition on the tail start is upward closed, so the field carried by a
certificate has no upper bound.  The repair is to work with the *least* valid
tail start instead of an arbitrary one.  Nothing in the existing certificates
has to change for that: least elements of a nonempty set of naturals exist,
and the coverage the certificates already carry caps where the least one can
sit.

The result is the sandwich `target ≤ least ≤ bound + 1`, where `bound` is any
time by which every value below the target has occurred.  The lower half is
the counting separation, the upper half is the coverage mechanism.  The least
tail start also has a clean local signature: the orbit sits strictly below the
target one step before it, which is exactly what minimality means.

Two things follow.  The minimum machinery transfers verbatim to the least tail
start, so a certificate can be rebuilt there.  And the only quantity still
unbounded is the coverage time itself — the last moment at which a value below
the target receives its first occurrence.  The sandwich makes that explicit:
the tail start is no longer the unknown, the coverage time is.
-/

/-- Least elements exist for any predicate on the naturals with a witness.
Proved by induction on a bound, so no decidability is required beyond the
classical case split. -/
theorem exists_least_of_bounded {p : Nat → Prop} :
    ∀ bound n, n ≤ bound → p n →
      ∃ least, p least ∧ ∀ m, p m → least ≤ m := by
  classical
  intro bound
  induction bound with
  | zero =>
      intro n hn hp
      have hzero : n = 0 := by omega
      subst hzero
      exact ⟨0, hp, fun m _ => Nat.zero_le m⟩
  | succ bound ih =>
      intro n hn hp
      by_cases hsmall : ∃ k, k ≤ bound ∧ p k
      · rcases hsmall with ⟨k, hk, hpk⟩
        exact ih k hk hpk
      · have hne : n = bound + 1 := by
          by_cases hle : n ≤ bound
          · exact absurd ⟨n, hle, hp⟩ hsmall
          · omega
        subst hne
        refine ⟨bound + 1, hp, fun m hm => ?_⟩
        by_cases hle : m ≤ bound
        · exact absurd ⟨m, hle, hm⟩ hsmall
        · omega

/-- Least elements exist for the tail-start predicate. -/
theorem exists_least_missingStrictAboveTail {target : Nat}
    (hex : ∃ s, MissingStrictAboveTail target s) :
    ∃ least, MissingStrictAboveTail target least ∧
      ∀ s, MissingStrictAboveTail target s → least ≤ s := by
  rcases hex with ⟨s, hs⟩
  exact exists_least_of_bounded s s (Nat.le_refl s) hs

/-- A valid tail start is positive: the orbit starts at zero, below every
positive target. -/
theorem missingStrictAboveTail_pos {target s : Nat}
    (h : MissingStrictAboveTail target s) : 0 < s := by
  by_cases hpos : 0 < s
  · exact hpos
  · have hzero : s = 0 := by omega
    have habove := h.strictly_above 0 (by omega)
    have hbase : a 0 = 0 := rfl
    have htarget := h.target_positive
    omega

/-- Local signature of the least tail start: the orbit is strictly below the
target one step earlier. -/
theorem least_predecessor_below_target {target least : Nat}
    (hspec : MissingStrictAboveTail target least)
    (hmin : ∀ s, MissingStrictAboveTail target s → least ≤ s) :
    a (least - 1) < target := by
  have hpos := missingStrictAboveTail_pos hspec
  by_cases hge : target ≤ a (least - 1)
  · exfalso
    have hsmaller : MissingStrictAboveTail target (least - 1) := by
      refine ⟨hspec.target_positive, hspec.target_missing, ?_⟩
      intro time htime
      rcases Nat.eq_or_lt_of_le htime with heq | hlt
      · have hne : a time ≠ target :=
          fun hbad => hspec.target_missing ⟨time, hbad⟩
        rw [heq] at hge
        omega
      · exact hspec.strictly_above time (by omega)
    have hle := hmin _ hsmaller
    omega
  · omega

/-- Every value below the target occurs strictly before any valid tail
start. -/
theorem covered_before_tailStart {target s bound : Nat}
    (hspec : MissingStrictAboveTail target s)
    (hcov : ∀ v, v < target → v ∈ valuesThrough bound) :
    ∀ v, v < target → v ∈ valuesThrough (s - 1) := by
  intro v hv
  rcases mem_valuesThrough_iff.mp (hcov v hv) with ⟨t, _, hval⟩
  have hlt : t < s := by
    by_cases hlt : t < s
    · exact hlt
    · have habove := hspec.strictly_above t (by omega)
      omega
  exact mem_valuesThrough_iff.mpr ⟨t, by omega, hval⟩

/-- Counting lower bound: a valid tail start clears the target. -/
theorem target_le_tailStart {target s bound : Nat}
    (hspec : MissingStrictAboveTail target s)
    (hcov : ∀ v, v < target → v ∈ valuesThrough bound) :
    target ≤ s := by
  have hpos := missingStrictAboveTail_pos hspec
  have hfull : coveredBelowCount target (s - 1) = target :=
    coveredBelowCount_eq_of_covered target
      (covered_before_tailStart hspec hcov)
  have hbound := coveredBelowCount_le_time target (s - 1)
  omega

/-- The sandwich.  The least tail start is caught between the target and any
coverage time. -/
theorem least_tailStart_twoSided {target bound : Nat}
    (hpos : 0 < target)
    (hmissing : ¬ ∃ time, a time = target)
    (hcov : ∀ v, v < target → v ∈ valuesThrough bound)
    (hex : ∃ s, MissingStrictAboveTail target s) :
    ∃ least, MissingStrictAboveTail target least ∧
      (∀ s, MissingStrictAboveTail target s → least ≤ s) ∧
      a (least - 1) < target ∧
      target ≤ least ∧
      least ≤ max bound target + 1 := by
  rcases exists_least_missingStrictAboveTail hex with ⟨least, hspec, hmin⟩
  exact ⟨least, hspec, hmin,
    least_predecessor_below_target hspec hmin,
    target_le_tailStart hspec hcov,
    tailStart_le_of_minimal hpos hmissing hcov hmin⟩

/-- With the coverage time already past the target the sandwich reads
`target ≤ least ≤ bound + 1`. -/
theorem least_tailStart_twoSided_of_late {target bound : Nat}
    (hpos : 0 < target)
    (hmissing : ¬ ∃ time, a time = target)
    (hcov : ∀ v, v < target → v ∈ valuesThrough bound)
    (hlate : target ≤ bound)
    (hex : ∃ s, MissingStrictAboveTail target s) :
    ∃ least, MissingStrictAboveTail target least ∧
      (∀ s, MissingStrictAboveTail target s → least ≤ s) ∧
      target ≤ least ∧ least ≤ bound + 1 := by
  rcases least_tailStart_twoSided hpos hmissing hcov hex with
    ⟨least, hspec, hmin, _, hlow, hup⟩
  have hmax : max bound target = bound := Nat.max_eq_left hlate
  rw [hmax] at hup
  exact ⟨least, hspec, hmin, hlow, hup⟩

/-- The whole tail-minimum machinery transfers to the least tail start, so a
certificate can be rebuilt there. -/
theorem least_tailStart_minimumCertificate {target least : Nat}
    (hspec : MissingStrictAboveTail target least) :
    ∃ time firstTime,
      PermanentTailMinimumCertificate target least time firstTime :=
  hspec.exists_minimumCertificate

namespace TerminalExactDischargeReplayCertificate

variable {target start : Nat} {parent : PhaseSearchNode}
variable {source : PermanentTailDischargeReturnCertificate target start parent}

/-- Applied to a surviving replay.  The certificate's own coverage, taken just
before its tail start, sandwiches the least tail start between the target and
the certificate's tail start, and the minimum machinery is available there. -/
theorem least_tailStart_sandwich
    (r : TerminalExactDischargeReplayCertificate source) :
    ∃ least, MissingStrictAboveTail target least ∧
      (∀ s, MissingStrictAboveTail target s → least ≤ s) ∧
      a (least - 1) < target ∧
      target ≤ least ∧
      least ≤ source.tailStart ∧
      ∃ time firstTime,
        PermanentTailMinimumCertificate target least time firstTime := by
  have hex : ∃ s, MissingStrictAboveTail target s :=
    ⟨source.tailStart, source.historical_tail⟩
  rcases least_tailStart_twoSided
    source.historical_tail.target_positive
    source.historical_tail.target_missing
    r.belowTarget_covered_preTail hex with
    ⟨least, hspec, hmin, hlocal, hlow, _⟩
  exact ⟨least, hspec, hmin, hlocal, hlow,
    hmin _ source.historical_tail,
    least_tailStart_minimumCertificate hspec⟩

/-- The rebuilt minimum at the least tail start dominates nothing new: its
value sits at or below the certificate's own tail minimum, since it minimises
over a larger stretch.  This is the link that would carry a rebuilt
certificate's two-sided bound back to the existing one. -/
theorem least_tailStart_minimum_le
    (_r : TerminalExactDischargeReplayCertificate source)
    {least time firstTime : Nat}
    (hmin : ∀ s, MissingStrictAboveTail target s → least ≤ s)
    (hcert : PermanentTailMinimumCertificate target least time firstTime) :
    a time ≤ a source.historicalMinimumTime := by
  have hle := hmin _ source.historical_tail
  have hstart := source.historical_minimum.minimum.start_le_time
  exact hcert.minimum.minimal source.historicalMinimumTime (by omega)

/-- Using the zero-budget coverage stored at the parent horizon instead, the
least tail start is capped by the horizon.  This is the form the counting
route needs: the tail start is no longer the free parameter, the coverage time
is. -/
theorem least_tailStart_capped_by_horizon
    (_r : TerminalExactDischargeReplayCertificate source) :
    ∃ least, MissingStrictAboveTail target least ∧
      (∀ s, MissingStrictAboveTail target s → least ≤ s) ∧
      target ≤ least ∧
      least ≤ max parent.horizon target + 1 := by
  have hex : ∃ s, MissingStrictAboveTail target s :=
    ⟨source.tailStart, source.historical_tail⟩
  rcases least_tailStart_twoSided
    source.historical_tail.target_positive
    source.historical_tail.target_missing
    (missingBelowCount_zero_covered target
      source.combined.crossing.budget_zero) hex with
    ⟨least, hspec, hmin, _, hlow, hup⟩
  exact ⟨least, hspec, hmin, hlow, hup⟩

end TerminalExactDischargeReplayCertificate

end

end Recaman
