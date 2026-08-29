import Recaman.PinnedAdjacentWitness

namespace Recaman

noncomputable section

/-! # How many early times can carry a large value

`coveredBelowCount_two_above` charged two idle times back to the pigeonhole
by naming them.  The same accounting works for any number of times at once
once the idle times are counted by a function rather than listed, and the
resulting statement is the density bound both open fronts asked for.

`highCount V n` counts the times up to `n` whose orbit value reaches `V`.
The basic identity is that covered levels and high times compete for the same
time budget:

* a time whose value reaches `V` covers no level below `V`;
* a time whose value stays below `V` covers at most one new level.

Hence `coveredBelowCount V n + highCount V n <= n + 1`.  When every level
below `V` is already covered at time `n` the covered term is exactly `V`, and
the bound becomes a genuine density statement: at most `n + 1 - V` of the
times up to `n` can carry a value of `V` or more.

Applied to a replay this reads: the pre-tail region has room for only
`tailStart - target` times at or above the target.  Naming three such times
therefore reproves `target + 3 <= tailStart` without listing them by hand,
and naming `k` of them gives `target + k <= tailStart` for free.

The last section reports what this does to the surviving pinned rows.  It
recovers the subtracting row's bound from a general principle, and it makes
precise why the adding row is out of reach: that row has exactly one time at
or above the target, so the density bound yields `target + 1 <= tailStart`
and nothing more.
-/

/-! ## Counting the high times -/

/-- Number of times up to `n` whose orbit value reaches `level`. -/
def highCount (level : Nat) : Nat → Nat
  | 0 => if level ≤ a 0 then 1 else 0
  | n + 1 => highCount level n + (if level ≤ a (n + 1) then 1 else 0)

@[simp] theorem highCount_succ (level n : Nat) :
    highCount level (n + 1) =
      highCount level n + (if level ≤ a (n + 1) then 1 else 0) := rfl

/-- The count only grows. -/
theorem highCount_mono {level m : Nat} :
    ∀ n, m ≤ n → highCount level m ≤ highCount level n := by
  intro n
  induction n with
  | zero =>
      intro hm
      have hzero : m = 0 := by omega
      subst hzero
      exact Nat.le_refl _
  | succ n ih =>
      intro hm
      rcases Nat.eq_or_lt_of_le hm with heq | hlt
      · subst heq
        exact Nat.le_refl _
      · have hle : m ≤ n := by omega
        have hih := ih hle
        simp only [highCount_succ]
        split <;> omega

/-- A high time strictly increases the count at its own index. -/
theorem highCount_step_high {level n : Nat} (h : level ≤ a (n + 1)) :
    highCount level n + 1 ≤ highCount level (n + 1) := by
  simp only [highCount_succ, if_pos h]
  omega

/-- One named high time gives a count of at least one. -/
theorem one_le_highCount {level t n : Nat} (ht : t ≤ n)
    (hv : level ≤ a t) : 1 ≤ highCount level n := by
  have hbase : 1 ≤ highCount level t := by
    cases t with
    | zero =>
        show 1 ≤ highCount level 0
        simp only [highCount, if_pos hv]
        omega
    | succ p =>
        have hstep := highCount_step_high (level := level) (n := p) hv
        omega
  have hmono := highCount_mono (level := level) (m := t) n ht
  omega

/-- Two named high times give a count of at least two. -/
theorem two_le_highCount {level t1 t2 n : Nat}
    (h12 : t1 < t2) (h2n : t2 ≤ n)
    (hv1 : level ≤ a t1) (hv2 : level ≤ a t2) :
    2 ≤ highCount level n := by
  obtain ⟨p2, rfl⟩ : ∃ p, t2 = p + 1 := ⟨t2 - 1, by omega⟩
  have hone : 1 ≤ highCount level p2 :=
    one_le_highCount (t := t1) (by omega) hv1
  have htwo : highCount level p2 + 1 ≤ highCount level (p2 + 1) :=
    highCount_step_high hv2
  have hlast : highCount level (p2 + 1) ≤ highCount level n :=
    highCount_mono n h2n
  omega

/-- Three named high times give a count of at least three. -/
theorem three_le_highCount {level t1 t2 t3 n : Nat}
    (h12 : t1 < t2) (h23 : t2 < t3) (h3n : t3 ≤ n)
    (hv1 : level ≤ a t1) (hv2 : level ≤ a t2) (hv3 : level ≤ a t3) :
    3 ≤ highCount level n := by
  obtain ⟨p2, rfl⟩ : ∃ p, t2 = p + 1 := ⟨t2 - 1, by omega⟩
  obtain ⟨p3, rfl⟩ : ∃ p, t3 = p + 1 := ⟨t3 - 1, by omega⟩
  have hone : 1 ≤ highCount level p2 :=
    one_le_highCount (t := t1) (by omega) hv1
  have htwo : highCount level p2 + 1 ≤ highCount level (p2 + 1) :=
    highCount_step_high hv2
  have hmid : highCount level (p2 + 1) ≤ highCount level p3 :=
    highCount_mono p3 (by omega)
  have hthree : highCount level p3 + 1 ≤ highCount level (p3 + 1) :=
    highCount_step_high hv3
  have hlast : highCount level (p3 + 1) ≤ highCount level n :=
    highCount_mono n h3n
  omega

/-! ## The competition identity -/

/-- Covered levels and high times share one time budget.  This is the
counting core: a high time covers nothing, an ordinary time covers at most
one new level, and the initial history holds a single value. -/
theorem coveredBelowCount_add_highCount_le (level : Nat) :
    ∀ n, coveredBelowCount level n + highCount level n ≤ n + 1 := by
  intro n
  induction n with
  | zero =>
      have hinit := coveredBelowCount_initial level
      by_cases hzero : level ≤ a 0
      · have hlevel : level = 0 := by
          have hbase : a 0 = 0 := rfl
          omega
        subst hlevel
        have hcov : coveredBelowCount 0 0 = 0 := rfl
        show coveredBelowCount 0 0 + highCount 0 0 ≤ 0 + 1
        simp only [highCount, if_pos hzero]
        omega
      · show coveredBelowCount level 0 + highCount level 0 ≤ 0 + 1
        simp only [highCount, if_neg hzero]
        omega
  | succ n ih =>
      by_cases hhigh : level ≤ a (n + 1)
      · have hcov : coveredBelowCount level (n + 1) ≤
            coveredBelowCount level n :=
          coveredBelowCount_step_of_above n level hhigh
        simp only [highCount_succ, if_pos hhigh]
        omega
      · have hcov := coveredBelowCount_step_le n level
        simp only [highCount_succ, if_neg hhigh]
        omega

/-- Density bound.  Once every level below `level` is covered at time `n`,
only `n + 1 - level` of the times up to `n` can reach `level`. -/
theorem highCount_le_of_covered {level n : Nat}
    (hcov : ∀ v, v < level → v ∈ valuesThrough n) :
    highCount level n + level ≤ n + 1 := by
  have hexact : coveredBelowCount level n = level :=
    coveredBelowCount_eq_of_covered level hcov
  have hsum := coveredBelowCount_add_highCount_le level n
  omega

/-- Naming three high times inside a fully covered prefix pushes the prefix
length three past the level. -/
theorem three_high_forces_length {level t1 t2 t3 n : Nat}
    (hcov : ∀ v, v < level → v ∈ valuesThrough n)
    (h12 : t1 < t2) (h23 : t2 < t3) (h3n : t3 ≤ n)
    (hv1 : level ≤ a t1) (hv2 : level ≤ a t2) (hv3 : level ≤ a t3) :
    level + 3 ≤ n + 1 := by
  have hthree := three_le_highCount h12 h23 h3n hv1 hv2 hv3
  have hdensity := highCount_le_of_covered hcov
  omega

/-- The hand-listed two-idle-time pigeonhole of `PinnedMiddleRow` is the
special case `highCount >= 2` of the competition identity. -/
theorem coveredBelowCount_two_above_by_density {level t1 t2 n : Nat}
    (h12 : t1 < t2) (h2n : t2 ≤ n)
    (hv1 : level ≤ a t1) (hv2 : level ≤ a t2) :
    coveredBelowCount level n + 1 ≤ n := by
  have htwo := two_le_highCount h12 h2n hv1 hv2
  have hsum := coveredBelowCount_add_highCount_le level n
  omega

/-! ## What this says about the surviving pinned rows -/

namespace TerminalExactDischargeReplayCertificate

variable {target start : Nat} {parent : PhaseSearchNode}
variable {source : PermanentTailDischargeReturnCertificate target start parent}

/-- Pre-tail density for a replay: the whole pre-tail region has room for
only `tailStart - target` times at or above the missing target. -/
theorem preTail_highCount_bound
    (r : TerminalExactDischargeReplayCertificate source) :
    highCount target (source.tailStart - 1) + target ≤ source.tailStart := by
  have hpos := r.tailStart_pos
  have hbound := highCount_le_of_covered
    (level := target) (n := source.tailStart - 1)
    r.belowTarget_covered_preTail
  omega

/-- The subtracting row of the pinned backward dichotomy has three pre-tail
times at or above the target, so the density bound alone reproves its
separation.  No hand-listed idle times are needed. -/
theorem firstRow_separation_by_density
    (r : TerminalExactDischargeReplayCertificate source)
    (_hminimum : a source.historicalMinimumTime = target + 2)
    {base : Nat} (hclock : source.historicalFirstTime = base + 2)
    (hp : PinnedTailMinimumConfiguration target (base + 2))
    (hprevious : a (base + 1) = target + base + 3)
    (hsecond : a base = target + 2 * base + 4) :
    target + 3 ≤ source.tailStart := by
  have hbefore := source.historical_minimum.firstTime_before_tail
  have hvalue : a (base + 2) = target + 1 := hp.value_eq
  have hlength := three_high_forces_length
    (level := target) (t1 := base) (t2 := base + 1) (t3 := base + 2)
    (n := source.tailStart - 1)
    r.belowTarget_covered_preTail (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)
  omega

/-- The adding row has exactly one such time, its own clock, so the density
bound yields only the separation already known.  This is the precise reason
the tool does not reach that row: both of its backward values lie strictly
below the target and therefore compete for covered levels rather than for
the time budget. -/
theorem lastRow_density_gives_only_one
    (r : TerminalExactDischargeReplayCertificate source)
    {base : Nat} (hclock : source.historicalFirstTime = base + 2)
    (hp : PinnedTailMinimumConfiguration target (base + 2))
    (hprevious : a (base + 1) + base + 2 = target + 1)
    (hsecond : a base + 2 * base + 2 = target) :
    a (base + 1) < target ∧ a base < target ∧
      1 ≤ highCount target (source.tailStart - 1) ∧
      target + 1 ≤ source.tailStart := by
  have hbefore := source.historical_minimum.firstTime_before_tail
  have hclockBound := hp.clock_bound
  have hvalue : a (base + 2) = target + 1 := hp.value_eq
  have hone : 1 ≤ highCount target (source.tailStart - 1) :=
    one_le_highCount (t := base + 2) (by omega) (by omega)
  have hdensity := r.preTail_highCount_bound
  exact ⟨by omega, by omega, hone, by omega⟩

end TerminalExactDischargeReplayCertificate

end

end Recaman
