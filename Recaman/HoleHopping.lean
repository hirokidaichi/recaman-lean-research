import Recaman.DescendingChain

namespace Recaman

/-! # Hole hopping

The small-scale dynamics of the canonical orbit is a game played on the set of
*unvisited* values, the *holes*.  After a chain step reaches height `h` at
clock `n` (that is, `a n = n + h`), the small candidates presented by the
chain are `h - 1`, `h - 4`, `h - 7`, ...: a single residue class modulo three.
As long as the band values stay fresh, the chain is blocked by the visited
small candidates and lands the *first unvisited* one.

After landing a small value `v` at a clock `j ≥ v`, the orbit sweeps the
consecutive unvisited values `v - 1`, `v - 2`, ... downward (the classical
comb), one every two clocks, as long as they are unvisited: the clock after
the landing is a forced addition to `v + j + 1`, and the next transition
subtracts back to `v - 1` when that value is fresh.

Hence a hole `u` can only be landed by a chain whose residue class contains
`u` and which sees no hole of that class between `u` and its start.  The
residue bookkeeping is recorded in the last theorem.

Everything here is a direct consequence of the step recurrence and of the
descending-chain lemmas.  No target, cutoff, or reachability hypothesis is
used.
-/

/-- The chain from height `h` lands the first fresh member of its residue class:
if the class members `h - 1 - 3 i` for `i < k` are visited at the clocks where they are
presented, the band values stay fresh, and `h - 1 - 3 k` is unvisited when presented, then
the orbit lands `h - 1 - 3 k` at clock `n + 2 k + 1`. -/
theorem chain_lands_first_fresh {n h k : Nat} (hval : a n = n + h) (hk : 3 * k + 2 ≤ h)
    (hblocked : ∀ i, i < k → h - 1 - 3 * i ∈ valuesThrough (n + 2 * i))
    (hfresh : ∀ i, i < k → n + h - 1 - i ∉ valuesThrough (n + 2 * i + 1))
    (htarget : h - 1 - 3 * k ∉ valuesThrough (n + 2 * k)) :
    a (n + 2 * k + 1) = h - 1 - 3 * k := by
  have hdesc : a (n + 2 * k) = n + h - k :=
    chain_descends (n := n) (h := h) k hk hblocked hfresh hval
  have hval' : a (n + 2 * k) = n + 2 * k + (h - 3 * k) := by
    rw [hdesc]
    omega
  have hh' : 2 ≤ h - 3 * k := by omega
  have hfresh' : h - 3 * k - 1 ∉ valuesThrough (n + 2 * k) := by
    have heq : h - 3 * k - 1 = h - 1 - 3 * k := by omega
    rw [heq]
    exact htarget
  have hland := chain_late_landing hval' hh' hfresh'
  omega

/-- After landing a small value `v ≤ j` at clock `j`, the next clock adds and the orbit
sits at height `v`: `a (j + 1) = v + j + 1`. -/
theorem comb_after_landing {j v : Nat} (hland : a j = v) (hle : v ≤ j) :
    a (j + 1) = v + j + 1 := by
  have hrec := recurrence j
  have hnot : ¬ CanSubtract (j + 1) (stateAt j) := by
    intro hcan
    have hlt : j + 1 < a j := hcan.1
    omega
  rw [if_neg hnot] at hrec
  omega

/-- Comb sweep: after landing `v ≤ j` at clock `j`, if the consecutive values `v - 1 - i`
(for `i < r`) are unvisited when presented, they are landed one every two clocks:
`a (j + 2 * (i + 1)) = v - 1 - i` for every `i < r`. Requires `r ≤ v - 1` so that the
values stay positive. -/
theorem comb_sweep {j v : Nat} (hland : a j = v) (hle : v ≤ j) :
    ∀ r, r + 1 ≤ v →
      (∀ i, i < r → v - 1 - i ∉ valuesThrough (j + 2 * i + 1)) →
      ∀ i, i < r → a (j + 2 * (i + 1)) = v - 1 - i := by
  intro r hr hfresh
  have haux : ∀ i, i ≤ r → a (j + 2 * i) = v - i := by
    intro i
    induction i with
    | zero =>
        intro _
        have h₀ : j + 2 * 0 = j := by omega
        rw [h₀]
        omega
    | succ i ih =>
        intro hi
        have hprev : a (j + 2 * i) = v - i := ih (by omega)
        have hle' : v - i ≤ j + 2 * i := by omega
        have hup : a (j + 2 * i + 1) = v - i + (j + 2 * i) + 1 :=
          comb_after_landing hprev hle'
        have hrec := recurrence (j + 2 * i + 1)
        have hcan : CanSubtract (j + 2 * i + 1 + 1) (stateAt (j + 2 * i + 1)) := by
          refine ⟨?_, ?_⟩
          · show j + 2 * i + 1 + 1 < a (j + 2 * i + 1)
            omega
          · have hcand :
                (stateAt (j + 2 * i + 1)).value - (j + 2 * i + 1 + 1) = v - 1 - i := by
              show a (j + 2 * i + 1) - (j + 2 * i + 1 + 1) = v - 1 - i
              omega
            rw [hcand]
            exact hfresh i (by omega)
        rw [if_pos hcan] at hrec
        have hidx : j + 2 * (i + 1) = j + 2 * i + 1 + 1 := by omega
        rw [hidx]
        omega
  intro i hi
  have hstep := haux (i + 1) (by omega)
  omega

/-- Residue bookkeeping for hole hopping: every small candidate presented by the chain
from height `h` is congruent to `h - 1` modulo three, so a hole `u` with
`u % 3 ≠ (h - 1) % 3` is never presented by that chain. -/
theorem chain_never_presents_other_class {h u i : Nat} (hi : 3 * i + 1 ≤ h)
    (hu : u % 3 ≠ (h - 1) % 3) : h - 1 - 3 * i ≠ u := by
  omega

end Recaman
