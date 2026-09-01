import Recaman.TargetTailResidualKernel
import Recaman.OrbitBounds

namespace Recaman

/-! # Structure of the eventual high-candidate corridor

The A-branch of the residual kernel is `EventualHighCandidateTail`: past a
cutoff, every subtraction candidate sits strictly above the missing target.
This module sharpens that branch in three steps.

First, any legal subtraction taken inside the corridor lands strictly above
`target + clock` and on a globally fresh value.  Second, and unconditionally,
the canonical orbit can never take forced additions forever: a perpetual
forced-addition ray grows so fast that its own candidate `a (n-1) - 1`
escapes both the finite pre-ray history and the sparse ray values, so a
legal subtraction eventually becomes available.  Combining the two, the
corridor forces infinitely many fresh landings high above their clocks.
Finally, every forced addition strictly inside the corridor exposes a
historical candidate.  The 2026-09-01 audit showed this membership
conclusion alone is free — it holds with no corridor hypothesis, because a
failed clock half truncates the candidate to `0 = a 0` — so the genuinely
corridor-bound half, the clock condition, is recorded separately in
`UnconditionalStepRecurrence` as `corridor_forcedAddition_clock_and_seen`.
-/

/-- **Corridor landing law.**  A legal subtraction taken at a corridor index
lands strictly above `target` plus the next clock, and the landing is a
first occurrence. -/
theorem corridor_subtraction_lands_above_clock
    {target cutoff n : Nat}
    (hhigh : ∀ m, cutoff ≤ m → target < nextSubtractionCandidate (m + 1))
    (hn : cutoff ≤ n)
    (hcan : CanSubtract (n + 1) (stateAt n)) :
    target + (n + 2) < a (n + 1) ∧ FirstAt a (a (n + 1)) (n + 1) := by
  have hhighN := hhigh n hn
  simp only [nextSubtractionCandidate] at hhighN
  exact ⟨by omega, firstAt_succ_of_canSubtract hcan⟩

/-- On a forced-addition ray beginning at `M`, every step past `M` adds its
own clock to the value. -/
theorem ray_step_value {M : Nat}
    (hray : ∀ n, M ≤ n → ¬ CanSubtract (n + 1) (stateAt n)) :
    ∀ n, M ≤ n → a (n + 1) = a n + (n + 1) := fun n hn =>
  a_succ_of_not_canSubtract (hray n hn)

/-- On a forced-addition ray the value grows by at least one per step. -/
theorem ray_growth_linear {M : Nat}
    (hray : ∀ n, M ≤ n → ¬ CanSubtract (n + 1) (stateAt n)) :
    ∀ s d, M ≤ s → a s + d ≤ a (s + d) := by
  have hstep := ray_step_value hray
  intro s d hs
  induction d with
  | zero =>
      show a s + 0 ≤ a s
      omega
  | succ d ih =>
      have hstepd := hstep (s + d) (by omega)
      show a s + (d + 1) ≤ a (s + d + 1)
      omega

/-- From any positive ray index onward, the value grows by at least two per
step: each addition contributes a clock of size at least two. -/
theorem ray_growth_double {M : Nat}
    (hray : ∀ n, M ≤ n → ¬ CanSubtract (n + 1) (stateAt n)) :
    ∀ s d, M ≤ s → 1 ≤ s → a s + 2 * d ≤ a (s + d) := by
  have hstep := ray_step_value hray
  intro s d hs hs1
  induction d with
  | zero =>
      show a s + 2 * 0 ≤ a s
      omega
  | succ d ih =>
      have hstepd := hstep (s + d) (by omega)
      show a s + 2 * (d + 1) ≤ a (s + d + 1)
      omega

/-- **No perpetual forced-addition ray.**  If every clock past `M` forced an
addition, the ray value would eventually clear the whole pre-ray value hull
`upperTri M` by a wide margin, while consecutive ray values are at least two
apart.  The candidate exposed there, one below the previous ray value, would
then be fresh, and its clock condition holds by growth; the resulting legal
subtraction contradicts the ray. -/
theorem no_perpetual_forcedAddition_ray (M : Nat)
    (hray : ∀ n, M ≤ n → ¬ CanSubtract (n + 1) (stateAt n)) :
    False := by
  have hstep := ray_step_value hray
  have hgrow := ray_growth_linear hray
  have hgap := ray_growth_double hray
  obtain ⟨p, hp⟩ : ∃ p, p = M + (upperTri M + M + 2) := ⟨_, rfl⟩
  have hpM : M ≤ p := by omega
  have hplow : upperTri M + M + 2 ≤ a p := by
    have h := hgrow M (upperTri M + M + 2) (Nat.le_refl M)
    rw [← hp] at h
    omega
  have hstepp := hstep p hpM
  have hclock : p + 1 + 1 < a (p + 1) := by omega
  have hcandidate : a (p + 1) - (p + 1 + 1) = a p - 1 := by omega
  have hfresh : a p - 1 ∉ valuesThrough (p + 1) := by
    intro hmem
    rcases mem_valuesThrough_iff.mp hmem with ⟨t, ht, hval⟩
    by_cases htM : t ≤ M
    · have hbound := a_le_upperTri t
      have hmono := upperTri_mono htM
      omega
    · by_cases htp : t < p
      · have hgapt := hgap t (p - t) (by omega) (by omega)
        have hidx : t + (p - t) = p := by omega
        rw [hidx] at hgapt
        omega
      · by_cases htpp : t = p
        · subst t
          omega
        · have htn : t = p + 1 := by omega
          subst t
          omega
  have hcan : CanSubtract (p + 1 + 1) (stateAt (p + 1)) := by
    constructor
    · change p + 1 + 1 < a (p + 1)
      exact hclock
    · change a (p + 1) - (p + 1 + 1) ∉ valuesThrough (p + 1)
      rw [hcandidate]
      exact hfresh
  exact hray (p + 1) (by omega) hcan

/-- **Unconditional subtraction recurrence.**  Beyond any bound the canonical
orbit takes another legal subtraction: forced additions never persist
forever. -/
theorem exists_canSubtract_of_ray (M : Nat) :
    ∃ n, M ≤ n ∧ CanSubtract (n + 1) (stateAt n) := by
  classical
  by_cases hresult : ∃ n, M ≤ n ∧ CanSubtract (n + 1) (stateAt n)
  · exact hresult
  · have hray : ∀ n, M ≤ n → ¬ CanSubtract (n + 1) (stateAt n) := by
      intro n hn hcan
      exact hresult ⟨n, hn, hcan⟩
    exact False.elim (no_perpetual_forcedAddition_ray M hray)

/-- **Corridor landing stream.**  An eventual high-candidate corridor forces
arbitrarily late legal subtractions, and each of them lands on a fresh value
strictly above `target` plus its clock. -/
theorem EventualHighCandidateTail.infinitely_many_high_fresh_landings
    {target tailStart : Nat}
    (hcorridor : EventualHighCandidateTail target tailStart) :
    ∀ M, ∃ n, M ≤ n ∧
      target + (n + 2) < a (n + 1) ∧
      FirstAt a (a (n + 1)) (n + 1) := by
  intro M
  rcases hcorridor with ⟨cutoff, _htail, hhigh⟩
  rcases exists_canSubtract_of_ray (max M cutoff) with ⟨n, hn, hcan⟩
  have hcut : cutoff ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
  have hlands := corridor_subtraction_lands_above_clock hhigh hcut hcan
  exact ⟨n, Nat.le_trans (Nat.le_max_left _ _) hn, hlands.1, hlands.2⟩

/-- A forced addition strictly inside the corridor exposes a historical
candidate.  Audit note: this membership conclusion is free of the corridor
hypothesis (see `forcedAddition_candidate_historical`); the corridor-bound
clock half lives in `corridor_forcedAddition_clock_and_seen`. -/
theorem corridor_forcedAddition_candidate_seen
    {target cutoff n : Nat}
    (hhigh : ∀ m, cutoff ≤ m → target < nextSubtractionCandidate (m + 1))
    (hn : cutoff + 1 ≤ n)
    (hnot : ¬ CanSubtract (n + 1) (stateAt n)) :
    nextSubtractionCandidate n ∈ valuesThrough n := by
  have hhighPrev := hhigh (n - 1) (by omega)
  have hclock : n - 1 + 1 = n := by omega
  rw [hclock] at hhighPrev
  simp only [nextSubtractionCandidate] at hhighPrev ⊢
  rcases not_canSubtract_cases hnot with hsmall | hseen
  · exact False.elim (by omega)
  · exact hseen

end Recaman
