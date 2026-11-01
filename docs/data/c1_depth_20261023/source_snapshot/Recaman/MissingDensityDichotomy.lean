import Recaman.EventualHighCorridorSecondMissing

namespace Recaman

/-! # The missing-density dichotomy

Either the canonical orbit returns to within two of its clock infinitely
often, or the integers it never visits have lower density at least one
quarter.  No target, cutoff, or reachability hypothesis enters.

The proof has three elementary steps under the negation of the first
alternative, which supplies a clock `N` with `k + 3 ≤ a k` for all `k ≥ N`.

* Isolation.  Past `N`, an interior clock (`a n ≤ 2n + 1`) is followed by an
  exterior clock: a subtraction would land at most `n`, below the law, so the
  step adds and `a (n+1) ≥ 2n + 4`.
* Counting.  Through time `m` the history holds exactly `m + 1` values.  In the
  second half `(m/2, m]` no two consecutive clocks are interior, and an
  exterior clock there has value above `m + 2`, so at most about `m/4` of the
  second-half clocks can contribute a value to the window `[0, m + 2]`.
  Hence the window contains at least about `m/4` unvisited values.
* Freezing.  A value `u ≤ m + 2` unvisited by time `m` is never visited: every
  later clock `t ≥ m + 1 ≥ N` has `a t ≥ t + 3 > m + 2`.

The corollaries say that an eventual high-candidate corridor over any
positive target forces this density-one-quarter alternative, and that the
recurrence alternative refutes every such corridor.
-/

/-- Number of stored values through time `n` that are at most `bound`,
counted with multiplicity. -/
def lowCount (n bound : Nat) : Nat :=
  ((valuesThrough n).filter (fun v => decide (v ≤ bound))).length

theorem lowCount_succ (n bound : Nat) :
    lowCount (n + 1) bound =
      lowCount n bound + (if a (n + 1) ≤ bound then 1 else 0) := by
  unfold lowCount
  rw [valuesThrough_succ]
  by_cases h : a (n + 1) ≤ bound
  · rw [List.filter_cons_of_pos (by simp [h]), List.length_cons, if_pos h]
  · rw [List.filter_cons_of_neg (by simp [h]), if_neg h, Nat.add_zero]

theorem lowCount_le (n bound : Nat) : lowCount n bound ≤ n + 1 := by
  unfold lowCount
  have h := List.length_filter_le (fun v => decide (v ≤ bound)) (valuesThrough n)
  rw [valuesThrough_length] at h
  exact h

theorem lowCount_le_add (n bound : Nat) :
    ∀ d, lowCount (n + d) bound ≤ lowCount n bound + d := by
  intro d
  induction d with
  | zero => simp
  | succ d ih =>
      rw [show n + (d + 1) = n + d + 1 by omega, lowCount_succ]
      split <;> omega

/-- **Isolation.**  Under the law `k + 3 ≤ a k` past `N`, an interior clock
is followed by an exterior clock. -/
theorem exterior_succ_of_interior {N n : Nat}
    (hlaw : ∀ k, N ≤ k → k + 3 ≤ a k) (hn : N ≤ n)
    (hint : a n ≤ 2 * n + 1) :
    2 * n + 4 ≤ a (n + 1) := by
  have hlawN := hlaw n hn
  have hlawSucc := hlaw (n + 1) (by omega)
  have hrec := recurrence n
  by_cases hcan : CanSubtract (n + 1) (stateAt n)
  · rw [if_pos hcan] at hrec
    omega
  · rw [if_neg hcan] at hrec
    omega

/-- Two consecutive clocks in the second half contribute at most one value
to the window. -/
theorem lowCount_two_step {N n bound : Nat}
    (hlaw : ∀ k, N ≤ k → k + 3 ≤ a k) (hn : N ≤ n + 1)
    (hbound : bound ≤ 2 * (n + 1) + 1) :
    lowCount (n + 1 + 1) bound ≤ lowCount n bound + 1 := by
  rw [lowCount_succ, lowCount_succ]
  by_cases h1 : a (n + 1) ≤ bound
  · have hint : a (n + 1) ≤ 2 * (n + 1) + 1 := by omega
    have hext := exterior_succ_of_interior hlaw hn hint
    have h2 : ¬ a (n + 1 + 1) ≤ bound := by omega
    rw [if_pos h1, if_neg h2]
    omega
  · rw [if_neg h1]
    split <;> omega

theorem lowCount_block {N s bound : Nat}
    (hlaw : ∀ k, N ≤ k → k + 3 ≤ a k) (hs : N ≤ s)
    (hbound : bound ≤ 2 * s + 1) :
    ∀ j, lowCount (s + 2 * j) bound ≤ lowCount s bound + j := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
      have hstep := lowCount_two_step hlaw (n := s + 2 * j)
        (bound := bound) (by omega) (by omega)
      rw [show s + 2 * (j + 1) = s + 2 * j + 1 + 1 by omega]
      omega

/-- **Window bound.**  Under the law `k + 3 ≤ a k` past `N`, every window
`[0, m + 2]` with `m ≥ 2N + 2` contains about `m / 4` values that the orbit never
visits, listed without repetition. -/
theorem missing_window_of_law {N : Nat}
    (hlaw : ∀ k, N ≤ k → k + 3 ≤ a k) (m : Nat) (hm : 2 * N + 2 ≤ m) :
    ∃ missing : List Nat, missing.Nodup ∧
      (∀ u ∈ missing, u ≤ m + 2 ∧ ∀ t, a t ≠ u) ∧
      m ≤ 4 * missing.length := by
  classical
  obtain ⟨s, hs_def⟩ : ∃ s, s = m / 2 + 1 := ⟨_, rfl⟩
  obtain ⟨j, hj_def⟩ : ∃ j, j = (m - s) / 2 := ⟨_, rfl⟩
  have hs : N ≤ s := by omega
  have hbound : m + 2 ≤ 2 * s + 1 := by omega
  have hblock := lowCount_block hlaw hs hbound j
  have htail := lowCount_le_add (s + 2 * j) (m + 2) (m - (s + 2 * j))
  rw [show s + 2 * j + (m - (s + 2 * j)) = m by omega] at htail
  have hstart := lowCount_le s (m + 2)
  refine ⟨(List.range (m + 3)).filter
      (fun u => decide (u ∉ valuesThrough m)), ?_, ?_, ?_⟩
  · exact List.Nodup.sublist List.filter_sublist List.nodup_range
  · intro u hu
    rw [List.mem_filter, List.mem_range] at hu
    have hfresh : u ∉ valuesThrough m := by simpa using hu.2
    refine ⟨by omega, ?_⟩
    intro t ht
    by_cases htm : t ≤ m
    · exact hfresh (mem_valuesThrough_iff.mpr ⟨t, htm, ht⟩)
    · have := hlaw t (by omega)
      omega
  · have hsubset : List.range (m + 3) ⊆
        (List.range (m + 3)).filter (fun u => decide (u ∉ valuesThrough m)) ++
          (valuesThrough m).filter (fun v => decide (v ≤ m + 2)) := by
      intro u hu
      rw [List.mem_append]
      by_cases hmem : u ∈ valuesThrough m
      · right
        rw [List.mem_filter]
        rw [List.mem_range] at hu
        exact ⟨hmem, by simp; omega⟩
      · left
        rw [List.mem_filter]
        exact ⟨hu, by simpa using hmem⟩
    have hlength := List.nodup_range.length_le_of_subset hsubset
    rw [List.length_range, List.length_append] at hlength
    change m + 3 ≤ _ + lowCount m (m + 2) at hlength
    omega

/-- **Dichotomy.**  Either `a n ≤ n + 2` for infinitely many `n`, or every
sufficiently wide window `[0, m + 2]` contains about `m / 4` values that the
orbit never visits: the never-visited set has lower density at least `1/4`. -/
theorem missing_density_dichotomy :
    (∀ start, ∃ n, start ≤ n ∧ a n ≤ n + 2) ∨
    (∃ N, ∀ m, N ≤ m → ∃ missing : List Nat, missing.Nodup ∧
      (∀ u ∈ missing, u ≤ m + 2 ∧ ∀ t, a t ≠ u) ∧
      m ≤ 4 * missing.length) := by
  classical
  by_cases hrec : ∀ start, ∃ n, start ≤ n ∧ a n ≤ n + 2
  · exact Or.inl hrec
  · right
    have hlaw : ∃ N, ∀ k, N ≤ k → k + 3 ≤ a k := by
      by_cases h : ∃ N, ∀ k, N ≤ k → k + 3 ≤ a k
      · exact h
      · exfalso
        apply hrec
        intro start
        by_cases h' : ∃ n, start ≤ n ∧ a n ≤ n + 2
        · exact h'
        · exfalso
          apply h
          refine ⟨start, ?_⟩
          intro k hk
          by_cases hk' : k + 3 ≤ a k
          · exact hk'
          · exact False.elim (h' ⟨k, hk, by omega⟩)
    rcases hlaw with ⟨N, hlaw⟩
    exact ⟨2 * N + 2, fun m hm => missing_window_of_law hlaw m hm⟩

/-- An eventual high-candidate corridor over a positive target forces the
density alternative: about `m / 4` never-visited values in every window. -/
theorem EventualHighCandidateTail.missing_density
    {target tailStart : Nat} (htarget : 1 ≤ target)
    (hcorridor : EventualHighCandidateTail target tailStart) :
    ∃ N, ∀ m, N ≤ m → ∃ missing : List Nat, missing.Nodup ∧
      (∀ u ∈ missing, u ≤ m + 2 ∧ ∀ t, a t ≠ u) ∧
      m ≤ 4 * missing.length := by
  rcases hcorridor with ⟨cutoff, _, hhigh⟩
  have hlaw : ∀ k, cutoff + 1 ≤ k → k + 3 ≤ a k := by
    intro k hk
    have := corridor_value_law hhigh (show cutoff < k by omega)
    omega
  exact ⟨2 * (cutoff + 1) + 2, fun m hm => missing_window_of_law hlaw m hm⟩

/-- The recurrence alternative refutes every eventual high-candidate
corridor over a positive target. -/
theorem not_eventualHigh_of_recurrent_low
    {target tailStart : Nat} (htarget : 1 ≤ target)
    (hrec : ∀ start, ∃ n, start ≤ n ∧ a n ≤ n + 2) :
    ¬ EventualHighCandidateTail target tailStart := by
  intro hcorridor
  rcases hcorridor with ⟨cutoff, _, hhigh⟩
  rcases hrec (cutoff + 1) with ⟨n, hn, hlow⟩
  have := corridor_value_law hhigh (show cutoff < n by omega)
  omega

/-- Sub-diagonal landings suffice for the recurrence alternative. -/
theorem recurrent_low_of_subDiagonal
    (hsub : ∀ start, ∃ n, start ≤ n ∧ a n < n) :
    ∀ start, ∃ n, start ≤ n ∧ a n ≤ n + 2 := by
  intro start
  rcases hsub start with ⟨n, hn, hlt⟩
  exact ⟨n, hn, by omega⟩

end Recaman
