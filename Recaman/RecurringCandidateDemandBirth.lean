import Recaman.EventualHighCorridorBirth
import Recaman.RecurringCandidateBurst

namespace Recaman

/-! # Birth classification for a recurring-candidate successor demand

At a positive use clock `m` of a corridor candidate `c`, the first forced
addition exposes the successor demand `c + m` at the next candidate clock.
When that demand is already in history, the second addition is forced.  This
module specializes the corridor birth machinery to that second addition and
keeps the demand's exact `FirstAt` witness.

The specialization gains one strict clock fact which the generic birth
classification does not record: the birth predecessor `t` satisfies `t < m`.
Indeed, the demand is not the value emitted by the first addition at time
`m + 1`.  In the addition-birth branch, a predecessor strictly inside the
corridor also gives the genuine clock contraction

```text
2 * (t + 1) + target < c + m.
```

With only the hull condition `upperTri cutoff < c + m`, the boundary
`t = cutoff` cannot be excluded: the corridor hypothesis controls the
candidate at `cutoff + 1`, not the candidate at `cutoff`.  The first theorem
therefore exposes that boundary honestly.  The late-demand corollary raises
the cleared hull by one clock, excludes the boundary, and returns the
contraction unconditionally in the addition branch.

No upper bound on an addition-run length is used.  In particular, the seeded
use-gap counterexample does not challenge these statements: its blockers are
placed in an arbitrary untimed seed, whereas `FirstAt a` below refers to the
canonical orbit's actual first occurrence.
-/

/-- **Recurring-demand birth classification.**  A positive recurring
candidate use whose successor demand forces the second addition has an exact
canonical birth strictly before the use clock.  A subtraction birth reuses
the predecessor clock's candidate.  An addition birth either occurs at the
corridor boundary, or its predecessor candidate is itself inside the
corridor and yields a double-clock contraction. -/
theorem corridor_recurringCandidate_demand_birth_classified
    {target cutoff c m : Nat}
    (hhigh : ∀ k, cutoff ≤ k → target < nextSubtractionCandidate (k + 1))
    (hm : cutoff ≤ m)
    (hc : nextSubtractionCandidate m = c)
    (hlate : c ≤ m)
    (hcpos : 0 < c)
    (hseen : c + m ∈ valuesThrough (m + 1))
    (hbig : upperTri cutoff < c + m) :
    ∃ t, cutoff ≤ t ∧ t < m ∧
      FirstAt a (c + m) (t + 1) ∧
      t + 2 + target < c + m ∧
      ((CanSubtract (t + 1) (stateAt t) ∧
          nextSubtractionCandidate t = c + m) ∨
        (¬ CanSubtract (t + 1) (stateAt t) ∧
          c + m = a t + (t + 1) ∧
          (t = cutoff ∨ 2 * (t + 1) + target < c + m))) := by
  have hforced₁ :=
    corridor_recurringCandidate_forcedAddition hhigh hm hc hlate
  have ham : a m = c + m + 1 := by
    simp only [nextSubtractionCandidate] at hc
    omega
  have ham₁ : a (m + 1) = c + 2 * m + 2 := by
    have hstep := a_succ_of_not_canSubtract hforced₁
    omega
  have hforced₂ := recurringCandidate_second_forcedAddition ham₁ hseen
  have hcand₁ : nextSubtractionCandidate (m + 1) = c + m := by
    simp only [nextSubtractionCandidate]
    omega
  have hn : cutoff + 1 ≤ m + 1 := by omega
  rcases corridor_forcedAddition_birth hhigh hn hforced₂
      (by simpa [hcand₁] using hbig) with
    ⟨b, hbcut, hbm, hfirst, hcone, _hhull⟩
  obtain ⟨t, rfl⟩ : ∃ t, b = t + 1 := ⟨b - 1, by omega⟩
  have hfirstDemand : FirstAt a (c + m) (t + 1) := by
    rwa [hcand₁] at hfirst
  have htm : t < m := by
    have htle : t ≤ m := by omega
    have hne : t ≠ m := by
      intro heq
      subst t
      have hvalue := hfirstDemand.1
      omega
    omega
  have htcut : cutoff ≤ t := by omega
  have hcone' : t + 2 + target < c + m := by
    rw [hcand₁] at hcone
    exact hcone
  rcases firstAt_succ_birth_dichotomy hfirst with hsub | hadd
  · refine ⟨t, htcut, htm, ?_, hcone', Or.inl ?_⟩
    · exact hfirstDemand
    · exact ⟨hsub.1, by omega⟩
  · refine ⟨t, htcut, htm, ?_, hcone', Or.inr ⟨hadd.1, ?_, ?_⟩⟩
    · exact hfirstDemand
    · omega
    · by_cases hboundary : t = cutoff
      · exact Or.inl hboundary
      · apply Or.inr
        have hpredHigh := hhigh (t - 1) (by omega)
        have hidx : t - 1 + 1 = t := by omega
        rw [hidx] at hpredHigh
        simp only [nextSubtractionCandidate] at hpredHigh
        omega

/-- **Late recurring-demand birth.**  Once the demand clears the hull one
clock beyond the corridor cutoff, its birth predecessor is strictly inside
the corridor.  Consequently every addition birth satisfies the exact
double-clock contraction, with no boundary alternative. -/
theorem corridor_recurringCandidate_late_demand_birth
    {target cutoff c m : Nat}
    (hhigh : ∀ k, cutoff ≤ k → target < nextSubtractionCandidate (k + 1))
    (hm : cutoff ≤ m)
    (hc : nextSubtractionCandidate m = c)
    (hlate : c ≤ m)
    (hcpos : 0 < c)
    (hseen : c + m ∈ valuesThrough (m + 1))
    (hbig : upperTri (cutoff + 1) < c + m) :
    ∃ t, cutoff < t ∧ t < m ∧
      FirstAt a (c + m) (t + 1) ∧
      t + 2 + target < c + m ∧
      ((CanSubtract (t + 1) (stateAt t) ∧
          nextSubtractionCandidate t = c + m) ∨
        (¬ CanSubtract (t + 1) (stateAt t) ∧
          c + m = a t + (t + 1) ∧
          2 * (t + 1) + target < c + m)) := by
  have hmono : upperTri cutoff ≤ upperTri (cutoff + 1) :=
    upperTri_mono (Nat.le_succ cutoff)
  have hbigCut : upperTri cutoff < c + m := by omega
  rcases corridor_recurringCandidate_demand_birth_classified
      hhigh hm hc hlate hcpos hseen hbigCut with
    ⟨t, htcut, htm, hfirst, hcone, hbirth⟩
  have htcutStrict : cutoff < t := by
    by_cases hstrict : cutoff < t
    · exact hstrict
    · exfalso
      have htle : t + 1 ≤ cutoff + 1 := by omega
      have hvalueBound := a_le_upperTri (t + 1)
      have hhullMono := upperTri_mono htle
      have hvalue := hfirst.1
      omega
  refine ⟨t, htcutStrict, htm, hfirst, hcone, ?_⟩
  rcases hbirth with hsub | hadd
  · exact Or.inl hsub
  · rcases hadd with ⟨hnot, heq, hboundary | hcontract⟩
    · exact False.elim (by omega)
    · exact Or.inr ⟨hnot, heq, hcontract⟩

end Recaman
