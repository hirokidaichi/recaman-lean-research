import Recaman.PermanentHighToothcombBound
import Recaman.PermanentHighToothcombDescent
import Recaman.PermanentHighCollision
import Recaman.PermanentHighRigidity
import Recaman.TailDowncrossingDichotomy

namespace Recaman

/-! # Permanent High Historical Blocker Exhaustion and Downcrossing Inevitability

This module formalizes the exhaustion of historical blockers and the inevitability
of downcrossings from the Recamán permanent high regime:

1. **Blocker Injectivity**:
   Each distinct toothcomb step `m` that fails to subtract requires a distinct
   historical blocker:
   `a(j1) = a n + n - m1 ∧ a(j2) = a n + n - m2 ∧ m1 ≠ m2 → j1 ≠ j2`.
   The historical blockers consumed by a toothcomb must all be distinct indices!

2. **Severe Blocker Height Escalation**:
   In the high regime `2n ≤ a n`, any toothcomb step `m` within the horizon
   `5m + n + 6 ≤ a n` has candidate `a n + n - m`.
   Any historical blocker `a j = a n + n - m` must satisfy the sharp linear inequality:
   `14 * n + 6 ≤ 5 * a j`  (i.e. `a j ≥ 2.8 n + 1.2`).
   Since `j < n`, this implies `14 * j + 20 ≤ 5 * a j` (i.e. `a j ≥ 2.8 j + 4`).

3. **Exhaustion of Historical Blockers**:
   If past values before `n` are bounded by `5 * a j < 14n + 6`, then:
   NO historical blocker can exist for ANY toothcomb step `m` in the high regime!
   `∀ j < n, a j ≠ a n + n - m`.

4. **Horizon Escape and Downcrossing Inevitability**:
   When historical blockers are exhausted, the toothcomb descent cannot be
   interrupted by past history. Once `m` exceeds `(a n - n - 6) / 5`,
   the orbit strictly downcrosses: `val < 2 * time`.
-/

/-! ### Part 1: Blocker Injectivity -/

/-- Distinct toothcomb steps within the valid range require distinct historical indices for their blockers. -/
theorem toothcomb_blocker_injective
    {n : Nat} {j1 j2 m1 m2 : Nat}
    (hm1 : m1 ≤ a n + n) (hm2 : m2 ≤ a n + n)
    (h1 : a j1 = a n + n - m1)
    (h2 : a j2 = a n + n - m2)
    (hne : m1 ≠ m2) :
    j1 ≠ j2 := by
  intro heq
  rw [heq] at h1
  have : a n + n - m1 = a n + n - m2 := by rw [← h1, h2]
  omega

/-- Two toothcomb blockers at the same historical index must have identical step indices. -/
theorem toothcomb_blocker_index_unique
    {n : Nat} {j m1 m2 : Nat}
    (h1 : a j = a n + n - m1)
    (h2 : a j = a n + n - m2) :
    a n + n - m1 = a n + n - m2 := by
  rw [← h1, h2]

/-! ### Part 2: Blocker Height Escalation -/

/-- Blocker height escalation: in the high regime, any toothcomb blocker within the
high regime horizon must have height `5 * a j ≥ 14 * n + 6` (i.e. `a j ≥ 2.8 n`). -/
theorem toothcomb_blocker_height_escalation
    {n m j : Nat}
    (hn_high : 2 * n ≤ a n)
    (hbound : 5 * m + n + 6 ≤ a n)
    (hblock : a j = a n + n - m) :
    14 * n + 6 ≤ 5 * a j := by
  omega

/-- Relative blocker height: since `j < n`, the blocker satisfies
`5 * a j ≥ 14 * j + 20` (i.e. `a j > 2.8 j`), which strictly exceeds twice its clock. -/
theorem toothcomb_blocker_relative_height
    {n j : Nat} (hj : j < n)
    (hscale : 14 * n + 6 ≤ 5 * a j) :
    14 * j + 20 ≤ 5 * a j ∧ 2 * j < a j := by
  have : 14 * j + 20 ≤ 14 * n + 6 := by omega
  have h1 : 14 * j + 20 ≤ 5 * a j := by omega
  have h2 : 2 * j < a j := by omega
  exact ⟨h1, h2⟩

/-! ### Part 3: Blocker Exhaustion under Ceiling -/

/-- If all past values are below `(14n + 6) / 5`, no historical blocker can exist
for ANY toothcomb step within the high regime horizon. -/
theorem toothcomb_no_historical_blocker_under_ceiling
    {n m : Nat}
    (hn_high : 2 * n ≤ a n)
    (hbound : 5 * m + n + 6 ≤ a n)
    (hceiling : ∀ j, j < n → 5 * a j < 14 * n + 6) :
    ∀ j, j < n → a j ≠ a n + n - m := by
  intro j hj heq
  have hscale := toothcomb_blocker_height_escalation hn_high hbound heq
  have hlt := hceiling j hj
  omega

/-- Candidate isolation: under the historical ceiling, the candidate `a n + n - m`
is completely isolated from all past history prior to `n`. -/
theorem toothcomb_candidate_avoids_all_past_history
    {n m : Nat} (hn : 1 ≤ n)
    (hn_high : 2 * n ≤ a n)
    (hbound : 5 * m + n + 6 ≤ a n)
    (hceiling : ∀ j, j < n → 5 * a j < 14 * n + 6) :
    a n + n - m ∉ valuesThrough (n - 1) := by
  intro hmem
  rcases mem_valuesThrough_iff.mp hmem with ⟨j, hj, hval⟩
  have hj_lt : j < n := by omega
  have hne := toothcomb_no_historical_blocker_under_ceiling hn_high hbound hceiling j hj_lt
  exact hne hval

/-! ### Part 4: Grand Historical Exhaustion Synthesis -/

/-- Grand Historical Exhaustion Synthesis:
1. Historical blockers for different toothcomb steps are mutually distinct (`j1 ≠ j2`).
2. Every blocker inside the high regime horizon satisfies `5 * a j ≥ 14n + 6 > 14j + 14`.
3. Under the ceiling `∀ j < n, 5 * a j < 14n + 6`, no historical blocker exists.
4. Any toothcomb extending beyond the horizon `a n < 5m + n + 6` strictly downcrosses. -/
theorem grand_permanent_high_history_exhaustion_synthesis
    {n m : Nat} {val : Nat}
    (hn_high : 2 * n ≤ a n)
    (hval : val = a n + n - m) :
    (∀ j1 j2 m1 m2, m1 ≤ a n + n → m2 ≤ a n + n →
       a j1 = a n + n - m1 → a j2 = a n + n - m2 → m1 ≠ m2 → j1 ≠ j2) ∧
    (∀ j, 5 * m + n + 6 ≤ a n → a j = a n + n - m → 14 * n + 6 ≤ 5 * a j) ∧
    ((∀ j, j < n → 5 * a j < 14 * n + 6) → 5 * m + n + 6 ≤ a n →
       ∀ j, j < n → a j ≠ a n + n - m) ∧
    (a n < 5 * m + n + 6 → val < 2 * (n + 3 + 2 * m)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j1 j2 m1 m2 hm1 hm2 h1 h2 hne
    exact toothcomb_blocker_injective hm1 hm2 h1 h2 hne
  · intro j hbound hblock
    exact toothcomb_blocker_height_escalation hn_high hbound hblock
  · intro hceiling hbound j hj
    exact toothcomb_no_historical_blocker_under_ceiling hn_high hbound hceiling j hj
  · intro hbound
    exact toothcomb_exceeds_high_bound_forces_downcrossing hval hbound

end Recaman
