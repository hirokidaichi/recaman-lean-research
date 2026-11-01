import Recaman.LagSevenPrefixRigidity

/-!
# TightHallAugmentation: Hall's condition forces membership in tight subsets

Consequences of Hall's condition for *tight* subsets.  Throughout, `U` is a nodup
list of supplied addition phases, `lag` assigns each phase its window length, and
Hall's condition on `U` is the hypothesis shape used in the T6 modules:

`hhall : ∀ A, List.Sublist A U → A.length ≤ (neighborhood e p A lag).length`.

A sublist `B` of `U` is *tight* when `(neighborhood e p B lag).length = B.length`.

1. `filter_mem_of_sublist_nodup`: filtering a nodup `U` by membership in a sublist `B`
   returns exactly `B`.
2. `filter_mem_or_eq_length`: for `x ∈ U \ B`, filtering `U` by `y ∈ B ∨ y = x` yields a
   sublist of `U` of length `B.length + 1` (the augmentation `B ∪ {x}` as a sublist of `U`).
3. `hall_forces_membership` (augmentation lemma): if `B` is tight and `x ∈ U` has every
   covered phase already inside `N(B)`, then `x ∈ B`.  Otherwise `B ∪ {x}` would be a
   sublist of `U` with `|B ∪ {x}| = |B| + 1 > |B| = |N(B)| ≥ |N(B ∪ {x})|`, violating Hall.
4. `tight_member_of_neighborhood_subset`: the same statement with the hypothesis written
   as a list inclusion `neighborhood e p [x] lag ⊆ neighborhood e p B lag`.
5. `w1_sibling_forced`: if a tight `B` contains a lag-7 member `u` whose past is
   `w1 = [S, A, A, A, A, S, S]`, and the phase `v = u - 3` is supplied with `lag v = 3`,
   then `v ∈ B`.  The window of `v` is `AAS` and covers exactly the phase of `u - 6`,
   which is an `S` inside the lag-7 window of `u`.
6. `aas_after_w1_forced`: if moreover `e u = A`, `e (u + 1) = A`, and `w = u + 2` is
   supplied with `lag w = 3`, then `w ∈ B`.  The window of `w` covers exactly the phase
   of `u - 1`, the youngest `S` of the window of `u`.

These lemmas explain the empirical facts recorded in
`docs/data/issue73_20260915/tight_structure.txt`: in every tight set found there, each
lag-7 `w1` member `u` comes with its lag-3 sibling `u - 3` (`sib u-3 in B` equals the
`w1` count for every period `p = 10..23`).  The mechanism is purely combinatorial:
a supplied phase whose neighborhood lies inside `N(B)` cannot be left out of a tight `B`.

Nothing here proves G1 or Gate T6: the results only constrain the shape of tight subsets
under an already-assumed Hall condition; they do not establish Hall's condition, nor any
deletability statement.
-/

namespace Recaman.TightHallAugmentation

open TwoSSTightDisjoint TwoSSAvoidTight LeadingRunSupply LowSSPeriodicSupply SharpPeriodicSupply
open UniversalQuantumWindowCapacity TightSubsetDecomposition LagSevenPrefixRigidity

/-- Filtering a nodup list `U` by membership in a sublist `B` returns exactly `B`. -/
theorem filter_mem_of_sublist_nodup {B U : List Nat} (hB : List.Sublist B U) (hU : U.Nodup) :
    U.filter (fun y => decide (y ∈ B)) = B := by
  induction hB with
  | slnil => rfl
  | @cons l₁ l₂ a h ih =>
    rw [List.nodup_cons] at hU
    have haB : a ∉ l₁ := fun haB => hU.1 (h.subset haB)
    rw [List.filter_cons_of_neg (by simp [haB])]
    exact ih hU.2
  | @cons_cons l₁ l₂ a h ih =>
    rw [List.nodup_cons] at hU
    rw [List.filter_cons_of_pos (by simp)]
    have hcongr : l₂.filter (fun y => decide (y ∈ a :: l₁)) = l₂.filter (fun y => decide (y ∈ l₁)) := by
      apply List.filter_congr
      intro y hy
      have hya : y ≠ a := fun hya => hU.1 (hya ▸ hy)
      simp [hya]
    rw [hcongr, ih hU.2]

/-- Augmenting a sublist `B` of a nodup `U` by one element `x ∈ U \ B`, realised as the
filter of `U` by `y ∈ B ∨ y = x`, has length exactly `B.length + 1`. -/
theorem filter_mem_or_eq_length {B U : List Nat} (hB : List.Sublist B U) (hU : U.Nodup)
    (x : Nat) (hxU : x ∈ U) (hxB : x ∉ B) :
    (U.filter (fun y => decide (y ∈ B ∨ y = x))).length = B.length + 1 := by
  induction hB with
  | slnil => simp at hxU
  | @cons l₁ l₂ a h ih =>
    rw [List.nodup_cons] at hU
    by_cases hxa : x = a
    · subst hxa
      rw [List.filter_cons_of_pos (by simp), List.length_cons]
      have hcongr : l₂.filter (fun y => decide (y ∈ l₁ ∨ y = x)) = l₂.filter (fun y => decide (y ∈ l₁)) := by
        apply List.filter_congr
        intro y hy
        have hyx : y ≠ x := fun hyx => hU.1 (hyx ▸ hy)
        simp [hyx]
      rw [hcongr, filter_mem_of_sublist_nodup h hU.2]
    · have hxl : x ∈ l₂ := by
        rw [List.mem_cons] at hxU
        rcases hxU with hxU | hxU
        · exact absurd hxU hxa
        · exact hxU
      have haB : a ∉ l₁ := fun haB => hU.1 (h.subset haB)
      have hax : a ≠ x := fun hax => hxa hax.symm
      rw [List.filter_cons_of_neg (by simp [haB, hax])]
      exact ih hU.2 hxl hxB
  | @cons_cons l₁ l₂ a h ih =>
    rw [List.nodup_cons] at hU
    have hxa : x ≠ a := fun hxa => hxB (hxa ▸ List.mem_cons_self)
    have hxl : x ∈ l₂ := by
      rw [List.mem_cons] at hxU
      rcases hxU with hxU | hxU
      · exact absurd hxU hxa
      · exact hxU
    have hxB' : x ∉ l₁ := fun hx => hxB (List.mem_cons_of_mem a hx)
    rw [List.filter_cons_of_pos (by simp), List.length_cons, List.length_cons]
    have hcongr : l₂.filter (fun y => decide (y ∈ a :: l₁ ∨ y = x)) =
        l₂.filter (fun y => decide (y ∈ l₁ ∨ y = x)) := by
      apply List.filter_congr
      intro y hy
      have hya : y ≠ a := fun hya => hU.1 (hya ▸ hy)
      simp [hya]
    rw [hcongr, ih hU.2 hxl hxB']

/-- **Augmentation lemma.** Under Hall's condition on `U`, a tight sublist `B` must contain
every supplied phase `x ∈ U` whose covered phases all lie inside `N(B)`. -/
theorem hall_forces_membership (e : Int → Bool) (p : Nat) (U B : List Nat) (lag : Nat → Nat)
    (hU : U.Nodup)
    (hhall : ∀ A : List Nat, List.Sublist A U → A.length ≤ (neighborhood e p A lag).length)
    (hB : List.Sublist B U)
    (htight : (neighborhood e p B lag).length = B.length)
    (x : Nat) (hxU : x ∈ U)
    (hcov : ∀ s, s ∈ neighborhood e p [x] lag → s ∈ neighborhood e p B lag) :
    x ∈ B := by
  by_cases hxB : x ∈ B
  · exact hxB
  · exfalso
    have hB'U : List.Sublist (U.filter (fun y => decide (y ∈ B ∨ y = x))) U := List.filter_sublist
    have hlen := filter_mem_or_eq_length hB hU x hxU hxB
    have hsub : neighborhood e p (U.filter (fun y => decide (y ∈ B ∨ y = x))) lag ⊆
        neighborhood e p B lag := by
      intro s hs
      rw [mem_neighborhood_iff_exists_singleton] at hs
      obtain ⟨u, hu, hsu⟩ := hs
      simp only [List.mem_filter, decide_eq_true_eq] at hu
      rcases hu.2 with huB | hux
      · exact singleton_neighborhood_subset e p B lag u huB hsu
      · subst hux
        exact hcov s hsu
    have hle := (neighborhood_nodup e p (U.filter (fun y => decide (y ∈ B ∨ y = x))) lag).length_le_of_subset hsub
    have hhall' := hhall _ hB'U
    omega

/-- Restatement of the augmentation lemma with the hypothesis as a list inclusion. -/
theorem tight_member_of_neighborhood_subset (e : Int → Bool) (p : Nat) (U B : List Nat) (lag : Nat → Nat)
    (hU : U.Nodup)
    (hhall : ∀ A : List Nat, List.Sublist A U → A.length ≤ (neighborhood e p A lag).length)
    (hB : List.Sublist B U)
    (htight : (neighborhood e p B lag).length = B.length)
    (x : Nat) (hxU : x ∈ U)
    (hsub : neighborhood e p [x] lag ⊆ neighborhood e p B lag) :
    x ∈ B :=
  hall_forces_membership e p U B lag hU hhall hB htight x hxU (fun _ hs => hsub hs)

/-- The seven bits of a `w1` past, read off from `past e u 7 = w1`. -/
theorem w1_bits (e : Int → Bool) (t : Int) (hw1 : past e t 7 = w1) :
    e (t - 1) = false ∧ e (t - 2) = true ∧ e (t - 3) = true ∧ e (t - 4) = true ∧
    e (t - 5) = true ∧ e (t - 6) = false ∧ e (t - 7) = false := by
  simpa [past, w1, List.range_succ] using hw1

/-- The lag-3 window at `u - 3` (an `AAS` window when `past e u 7 = w1`) covers only phases
already covered by the lag-7 window at `u`: its unique `S` is `u - 6`. -/
theorem w1_sibling_neighborhood_subset (e : Int → Bool) (p : Nat) (lag : Nat → Nat)
    (u v : Nat) (hvu : v + 3 = u) (hlu : lag u = 7) (hlv : lag v = 3)
    (hw1 : past e (u : Int) 7 = w1) :
    neighborhood e p [v] lag ⊆ neighborhood e p [u] lag := by
  obtain ⟨_, _, _, h4, h5, h6, _⟩ := w1_bits e (u : Int) hw1
  intro s hs
  rw [mem_neighborhood_iff] at hs ⊢
  refine ⟨hs.1, ?_⟩
  have hcov := hs.2
  rw [isCoveredBySubset_iff] at hcov ⊢
  obtain ⟨w, hw, i, hi, he, hmod⟩ := hcov
  rw [List.mem_singleton] at hw
  rw [hw] at hi he hmod
  rw [hlv] at hi
  have hi2 : i = 2 := by
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl
    · exfalso
      have heq : (v : Int) - 1 - ((0 : Nat) : Int) = (u : Int) - 4 := by omega
      rw [heq, h4] at he
      exact Bool.noConfusion he
    · exfalso
      have heq : (v : Int) - 1 - ((1 : Nat) : Int) = (u : Int) - 5 := by omega
      rw [heq, h5] at he
      exact Bool.noConfusion he
    · rfl
  subst hi2
  refine ⟨u, List.mem_singleton_self u, 5, by rw [hlu]; omega, ?_, ?_⟩
  · have heq : (u : Int) - 1 - ((5 : Nat) : Int) = (v : Int) - 1 - ((2 : Nat) : Int) := by omega
    rw [heq]
    exact he
  · have heq : (u : Int) - 1 - ((5 : Nat) : Int) = (v : Int) - 1 - ((2 : Nat) : Int) := by omega
    rw [heq]
    exact hmod

/-- **`w1` sibling forcing.** If a tight `B` contains a lag-7 member `u` with `past e u 7 = w1`,
and the phase `v = u - 3` is supplied with `lag v = 3`, then `v ∈ B`. -/
theorem w1_sibling_forced (e : Int → Bool) (p : Nat) (U B : List Nat) (lag : Nat → Nat)
    (hU : U.Nodup)
    (hhall : ∀ A : List Nat, List.Sublist A U → A.length ≤ (neighborhood e p A lag).length)
    (hB : List.Sublist B U)
    (htight : (neighborhood e p B lag).length = B.length)
    (u v : Nat) (huB : u ∈ B) (hvU : v ∈ U)
    (hvu : v + 3 = u) (hlu : lag u = 7) (hlv : lag v = 3)
    (hw1 : past e (u : Int) 7 = w1) :
    v ∈ B := by
  apply tight_member_of_neighborhood_subset e p U B lag hU hhall hB htight v hvU
  intro s hs
  exact singleton_neighborhood_subset e p B lag u huB
    (w1_sibling_neighborhood_subset e p lag u v hvu hlu hlv hw1 hs)

/-- The lag-3 window at `u + 2` (an `AAS` window when `e u = A`, `e (u + 1) = A`, and
`past e u 7 = w1`) covers only the phase of `u - 1`, the youngest `S` of the window at `u`. -/
theorem aas_after_w1_neighborhood_subset (e : Int → Bool) (p : Nat) (lag : Nat → Nat)
    (u w : Nat) (hwu : w = u + 2) (hlu : lag u = 7) (hlw : lag w = 3)
    (huA : e (u : Int) = true) (hu1 : e ((u : Int) + 1) = true)
    (hw1 : past e (u : Int) 7 = w1) :
    neighborhood e p [w] lag ⊆ neighborhood e p [u] lag := by
  obtain ⟨h1, _, _, _, _, _, _⟩ := w1_bits e (u : Int) hw1
  intro s hs
  rw [mem_neighborhood_iff] at hs ⊢
  refine ⟨hs.1, ?_⟩
  have hcov := hs.2
  rw [isCoveredBySubset_iff] at hcov ⊢
  obtain ⟨x, hx, i, hi, he, hmod⟩ := hcov
  rw [List.mem_singleton] at hx
  rw [hx] at hi he hmod
  rw [hlw] at hi
  have hi2 : i = 2 := by
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl
    · exfalso
      have heq : (w : Int) - 1 - ((0 : Nat) : Int) = (u : Int) + 1 := by omega
      rw [heq, hu1] at he
      exact Bool.noConfusion he
    · exfalso
      have heq : (w : Int) - 1 - ((1 : Nat) : Int) = (u : Int) := by omega
      rw [heq, huA] at he
      exact Bool.noConfusion he
    · rfl
  subst hi2
  refine ⟨u, List.mem_singleton_self u, 0, by rw [hlu]; omega, ?_, ?_⟩
  · have heq : (u : Int) - 1 - ((0 : Nat) : Int) = (w : Int) - 1 - ((2 : Nat) : Int) := by omega
    rw [heq]
    exact he
  · have heq : (u : Int) - 1 - ((0 : Nat) : Int) = (w : Int) - 1 - ((2 : Nat) : Int) := by omega
    rw [heq]
    exact hmod

/-- **`AAS`-after-`w1` forcing.** If a tight `B` contains a lag-7 member `u` with
`past e u 7 = w1`, `e u = A`, `e (u + 1) = A`, and the phase `w = u + 2` is supplied with
`lag w = 3`, then `w ∈ B`. -/
theorem aas_after_w1_forced (e : Int → Bool) (p : Nat) (U B : List Nat) (lag : Nat → Nat)
    (hU : U.Nodup)
    (hhall : ∀ A : List Nat, List.Sublist A U → A.length ≤ (neighborhood e p A lag).length)
    (hB : List.Sublist B U)
    (htight : (neighborhood e p B lag).length = B.length)
    (u w : Nat) (huB : u ∈ B) (hwU : w ∈ U)
    (hwu : w = u + 2) (hlu : lag u = 7) (hlw : lag w = 3)
    (huA : e (u : Int) = true) (hu1 : e ((u : Int) + 1) = true)
    (hw1 : past e (u : Int) 7 = w1) :
    w ∈ B := by
  apply tight_member_of_neighborhood_subset e p U B lag hU hhall hB htight w hwU
  intro s hs
  exact singleton_neighborhood_subset e p B lag u huB
    (aas_after_w1_neighborhood_subset e p lag u w hwu hlu hlw huA hu1 hw1 hs)

end Recaman.TightHallAugmentation
