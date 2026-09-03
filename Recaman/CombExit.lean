import Recaman.LevelTwoThree
import Recaman.LockResidue

namespace Recaman

/-! # The comb blocks the exits of the level-2/3 phase

A comb with `T` teeth lands `v + s` at clock `i + 1 - 2 s` for `s < T` (tooth `0` is the
comb end `(i + 1, v)`), and every tooth is followed by the forced addition
`a (i + 2 - 2 s) = i + v + 2 - s`.  These addition values form a run of consecutive
integers just above `i + v + 2 - T`.

When the test value `2 i + v + 4` of the comb end is fresh, the orbit returns to level two
(`popup_return_level_two`) and the level-2/3 phase (`level23_phase`) starts at `m = i + 5`
with offset `s = v - 6`.  Its exit candidates are `(i + 5 + 2 k) + (v - 6 - 5 k) - 1 =
i + v - 2 - 3 k`, and `i + v - 2 - 3 k = i + v + 2 - (3 k + 4)` is the addition value of
tooth `3 k + 4`.  Hence the comb itself blocks the exits of the pairs `k` with
`3 k + 5 ≤ T`, and the phase persists for at least `⌊(T - 2) / 3⌋` pairs whenever the
level-three values it presents are fresh.  This is the fresh-side counterpart of
`popup_lock_persists`: the length of the comb, like the length of the pre-landing run, is
paid back as ping-pong pairs after the comb end.  (The blocker-provenance census,
`H-20260903-01`, sees this as the `gap = 7` signature of the `entry23` blockers.)

Everything here is a direct consequence of the step recurrence and of the comb, pop-up
and level-2/3 lemmas.  No target, cutoff, or reachability hypothesis is used.
-/

/-- The forced addition after every tooth of a comb: with teeth `a (i + 1 - 2 s) = v + s`
for `s < T` and `v + 3 T ≤ i + 1`, the clock after tooth `s` carries `i + v + 2 - s`. -/
theorem comb_addition_values {i v T : Nat}
    (hcomb : ∀ s, s < T → a (i + 1 - 2 * s) = v + s) (hle : v + 3 * T ≤ i + 1) :
    ∀ s, s < T → a (i + 1 - 2 * s + 1) = i + v + 2 - s := by
  intro s hs
  have hadd := comb_after_landing (hcomb s hs) (by omega)
  omega

/-- The exit candidates of the level-2/3 phase after the comb end are the comb's own
addition values: for `3 k + 5 ≤ T` the candidate `(i + 5 + 2 k) + (v - 6 - 5 k) - 1`
was visited at clock `i + 1 - 2 (3 k + 4) + 1`, hence is visited when presented. -/
theorem level23_candidate_blocked_by_comb {i v T : Nat}
    (hcomb : ∀ s, s < T → a (i + 1 - 2 * s) = v + s) (hle : v + 3 * T ≤ i + 1) :
    ∀ k, 3 * k + 5 ≤ T → 5 * k + 6 ≤ v →
      (i + 5 + 2 * k) + (v - 6 - 5 * k) - 1 ∈ valuesThrough (i + 5 + 2 * k) := by
  intro k hk hv
  have hval := comb_addition_values hcomb hle (3 * k + 4) (by omega)
  have hcand : (i + 5 + 2 * k) + (v - 6 - 5 * k) - 1 = a (i + 1 - 2 * (3 * k + 4) + 1) := by
    omega
  rw [hcand]
  exact valuesThrough_mono_of_le (current_mem_valuesThrough _) (by omega)

/-- The level-2/3 phase after a comb end with a fresh test value persists for `K` pairs
as soon as `3 K + 2 ≤ T` (that is, for at least `⌊(T - 2) / 3⌋` pairs), provided the
level-three values it presents are fresh: `a (i + 5 + 2 k) = 2 (i + 5 + 2 k) + (v - 6 - 5 k)`
for all `k ≤ K`. -/
theorem level23_phase_of_comb {i v T K : Nat}
    (hcomb : ∀ s, s < T → a (i + 1 - 2 * s) = v + s) (hle : v + 3 * T ≤ i + 1)
    (hprev : a i = v + i + 1) (hblocked : v - 1 ∈ valuesThrough (i + 2))
    (htest : 2 * i + v + 4 ∉ valuesThrough (i + 4))
    (hK : 3 * K + 2 ≤ T) (hs : 5 * K + 9 ≤ v)
    (hfresh : ∀ k, k < K →
      2 * (i + 5 + 2 * k) + (v - 6 - 5 * k) - 1 ∉ valuesThrough (i + 5 + 2 * k + 1)) :
    ∀ k, k ≤ K → a (i + 5 + 2 * k) = 2 * (i + 5 + 2 * k) + (v - 6 - 5 * k) := by
  have hland : a (i + 1) = v := by
    have h0 := hcomb 0 (by omega)
    rw [show i + 1 - 2 * 0 = i + 1 by omega] at h0
    omega
  have hret := popup_return_level_two hprev hland (by omega) hblocked htest
  have hval : a (i + 5) = 2 * (i + 5) + (v - 6) := by omega
  exact level23_phase hval K (by omega)
    (fun k hk => level23_candidate_blocked_by_comb hcomb hle k (by omega) (by omega)) hfresh

end Recaman
