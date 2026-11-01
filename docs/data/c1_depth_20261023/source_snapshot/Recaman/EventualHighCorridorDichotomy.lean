import Recaman.TargetTailResidualKernel
import Recaman.EventualHighCorridorRecurrence

namespace Recaman

/-! # Divergence-or-recurrence dichotomy in a high-candidate corridor

Inside an eventual high-candidate corridor the subtraction-candidate walk
shows exactly two long-run behaviours.  Either the walk diverges — past
some clock every candidate exceeds any prescribed bound — or some single
value `c` strictly above the missing target recurs as the exact candidate
at arbitrarily late clocks *and* eventually floors the walk from below.

The recurrence branch is produced by extracting the least recurring value.
Minimality turns every smaller band value into a value of bounded
occurrence, and a uniform bound over the finite band `(target, c)`
upgrades the corridor's high-candidate law to the eventual floor
`c ≤ nextSubtractionCandidate`.

Feeding the floor back into the rigid use-clock analysis of
`EventualHighCorridorRecurrence` yields the capstone corollary: in the
non-divergent branch the corridor hosts an unbounded chronological stream
of complete rigid use-clock events for the recurring value. -/

/-- **Least recurring candidate value.**  If some value occurs as the
subtraction candidate at arbitrarily late clocks, then a least such value
exists.  Strong recursion descends through any smaller recurring witness. -/
theorem exists_least_recurring_candidate
    (c₀ : Nat) :
    (∀ M, ∃ m, M ≤ m ∧ nextSubtractionCandidate m = c₀) →
    ∃ c, (∀ M, ∃ m, M ≤ m ∧ nextSubtractionCandidate m = c) ∧
      ∀ v, (∀ M, ∃ m, M ≤ m ∧ nextSubtractionCandidate m = v) → c ≤ v := by
  classical
  induction c₀ using Nat.strongRecOn with
  | ind c₀ ih =>
      intro hrec
      by_cases hsmaller : ∃ v, v < c₀ ∧
          ∀ M, ∃ m, M ≤ m ∧ nextSubtractionCandidate m = v
      · rcases hsmaller with ⟨v, hv, hvrec⟩
        exact ih v hv hvrec
      · refine ⟨c₀, hrec, ?_⟩
        intro v hvrec
        by_cases hv : v < c₀
        · exact False.elim (hsmaller ⟨v, hv, hvrec⟩)
        · omega

/-- **Uniform bound for a non-recurring band.**  If no value in the open
band `(target, c)` recurs at arbitrarily late clocks, then past one
uniform clock the candidate walk avoids the whole band.  Induction on `c`
combines the finitely many per-value avoidance bounds. -/
theorem exists_uniform_bound_of_no_recurrence
    (target c : Nat)
    (hno : ∀ v, target < v → v < c →
      ¬ (∀ M, ∃ m, M ≤ m ∧ nextSubtractionCandidate m = v)) :
    ∃ M₀, ∀ m, M₀ ≤ m → ∀ v, target < v → v < c →
      nextSubtractionCandidate m ≠ v := by
  classical
  revert hno
  induction c with
  | zero =>
      intro _
      refine ⟨0, ?_⟩
      intro m _ v _ hv
      exact absurd hv (Nat.not_lt_zero v)
  | succ c ih =>
      intro hno
      have hno' : ∀ v, target < v → v < c →
          ¬ (∀ M, ∃ m, M ≤ m ∧ nextSubtractionCandidate m = v) := by
        intro v hv1 hv2
        exact hno v hv1 (by omega)
      rcases ih hno' with ⟨M₀, hM₀⟩
      by_cases hct : target < c
      · have hnoc := hno c hct (by omega)
        by_cases hstop : ∃ N, ∀ m, N ≤ m →
            nextSubtractionCandidate m ≠ c
        · rcases hstop with ⟨N, hN⟩
          refine ⟨M₀ + N, ?_⟩
          intro m hm v hv1 hv2
          by_cases hvc : v = c
          · subst hvc
            exact hN m (by omega)
          · exact hM₀ m (by omega) v hv1 (by omega)
        · refine False.elim (hnoc ?_)
          intro M
          by_cases hexists : ∃ m, M ≤ m ∧
              nextSubtractionCandidate m = c
          · exact hexists
          · refine False.elim (hstop ⟨M, ?_⟩)
            intro m hm heq
            exact hexists ⟨m, hm, heq⟩
      · refine ⟨M₀, ?_⟩
        intro m hm v hv1 hv2
        by_cases hvc : v < c
        · exact hM₀ m hm v hv1 hvc
        · omega

/-- **A-branch dichotomy.**  In an eventual high-candidate corridor the
candidate walk either diverges, or some value `c` strictly above the
missing target recurs as the exact candidate at arbitrarily late clocks
and eventually floors the walk: `c ≤ nextSubtractionCandidate k` for all
late `k`. -/
theorem EventualHighCandidateTail.candidate_diverges_or_recurrence
    {target tailStart : Nat}
    (hcorridor : EventualHighCandidateTail target tailStart) :
    (∀ K, ∃ N, ∀ m, N ≤ m → K < nextSubtractionCandidate m) ∨
      ∃ c M₁, target < c ∧
        (∀ k, M₁ ≤ k → c ≤ nextSubtractionCandidate k) ∧
        ∀ M, ∃ m, M ≤ m ∧ nextSubtractionCandidate m = c := by
  classical
  by_cases hdiv : ∀ K, ∃ N, ∀ m, N ≤ m → K < nextSubtractionCandidate m
  · exact Or.inl hdiv
  · apply Or.inr
    have hK : ∃ K, ∀ M, ∃ m, M ≤ m ∧
        nextSubtractionCandidate m ≤ K := by
      by_cases hexists : ∃ K, ∀ M, ∃ m, M ≤ m ∧
          nextSubtractionCandidate m ≤ K
      · exact hexists
      · refine False.elim (hdiv ?_)
        intro K
        by_cases hN : ∃ N, ∀ m, N ≤ m →
            K < nextSubtractionCandidate m
        · exact hN
        · refine False.elim (hexists ⟨K, ?_⟩)
          intro M
          by_cases hm : ∃ m, M ≤ m ∧
              nextSubtractionCandidate m ≤ K
          · exact hm
          · refine False.elim (hN ⟨M, ?_⟩)
            intro m hMm
            by_cases hle : K < nextSubtractionCandidate m
            · exact hle
            · exact False.elim (hm ⟨m, hMm, by omega⟩)
    rcases hK with ⟨K, hbounded⟩
    rcases corridor_candidate_bounded_recurrence hbounded with
      ⟨c₀, _hcK, hrec₀⟩
    rcases exists_least_recurring_candidate c₀ hrec₀ with
      ⟨c, hcrec, hcmin⟩
    rcases hcorridor with ⟨cutoff, _htailCut, hhigh⟩
    have htargetc : target < c := by
      rcases hcrec (cutoff + 1) with ⟨m, hm, hmc⟩
      have hm1 : m - 1 + 1 = m := by omega
      have hcut : cutoff ≤ m - 1 := by omega
      have hhighm := hhigh (m - 1) hcut
      rw [hm1] at hhighm
      omega
    have hno : ∀ v, target < v → v < c →
        ¬ (∀ M, ∃ m, M ≤ m ∧ nextSubtractionCandidate m = v) := by
      intro v _ hvc hvrec
      have hcv := hcmin v hvrec
      omega
    rcases exists_uniform_bound_of_no_recurrence target c hno with
      ⟨M₀, hM₀⟩
    refine ⟨c, M₀ + cutoff + 1, htargetc, ?_, hcrec⟩
    intro k hk
    have hk1 : k - 1 + 1 = k := by omega
    have hcut : cutoff ≤ k - 1 := by omega
    have hhighk := hhigh (k - 1) hcut
    rw [hk1] at hhighk
    by_cases hlt : nextSubtractionCandidate k < c
    · exact False.elim
        (hM₀ k (by omega) (nextSubtractionCandidate k) hhighk hlt rfl)
    · omega

/-- **Capstone: divergence or a rigid event stream.**  In an eventual
high-candidate corridor, either the candidate walk diverges, or some
value `c` strictly above the missing target has arbitrarily late use
clocks each performing the complete rigid pattern: exact candidate `c`,
legal fresh subtraction entry onto the diagonal value `c + m + 1`, forced
addition out to `c + 2m + 2`, and the successor value `c + m` already
recorded in history. -/
theorem EventualHighCandidateTail.diverges_or_rigidEventStream
    {target tailStart : Nat}
    (hcorridor : EventualHighCandidateTail target tailStart) :
    (∀ K, ∃ N, ∀ m, N ≤ m → K < nextSubtractionCandidate m) ∨
      ∃ c, target < c ∧
        ∀ M, ∃ m, M ≤ m ∧
          nextSubtractionCandidate m = c ∧
          CanSubtract m (stateAt (m - 1)) ∧
          FirstAt a (a m) m ∧
          a m = c + m + 1 ∧
          ¬ CanSubtract (m + 1) (stateAt m) ∧
          a (m + 1) = c + 2 * m + 2 ∧
          c + m ∈ valuesThrough (m + 1) := by
  classical
  rcases hcorridor.candidate_diverges_or_recurrence with
    hdiv | ⟨c, M₁, htargetc, hfloor, hrec⟩
  · exact Or.inl hdiv
  · apply Or.inr
    rcases hcorridor with ⟨cutoff, _htailCut, hhigh⟩
    refine ⟨c, htargetc, ?_⟩
    intro M
    rcases hrec (M + cutoff + c + M₁ + 3) with ⟨m, hm, hmc⟩
    have hevent := corridor_recurringCandidate_event hhigh hfloor
      (by omega) (by omega) hmc (by omega) (by omega)
    exact ⟨m, by omega, hmc, hevent.1, hevent.2.1, hevent.2.2.1,
      hevent.2.2.2.1, hevent.2.2.2.2.1, hevent.2.2.2.2.2⟩

end Recaman
