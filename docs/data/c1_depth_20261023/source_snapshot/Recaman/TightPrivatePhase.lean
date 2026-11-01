import Recaman.TightHallAugmentation

/-!
# TightPrivatePhase: each member of a tight set has at most one private subtraction phase

Consequences of Hall's condition on the *subsets* of a tight set.  Throughout, `U` is a list of
supplied addition phases, `lag` assigns each phase its window length, Hall's condition on `U` is
the hypothesis shape used in the T6 modules,

`hhall : ∀ A, List.Sublist A U → A.length ≤ (neighborhood e p A lag).length`,

and a sublist `B` of `U` is *tight* when `(neighborhood e p B lag).length = B.length`.
This is lemma B of `docs/HYPOTHESIS_CARD_2026-09-15_TIGHT_OLDEST_S_CHARACTERIZATION.md` §4:
apply Hall to `B \ {v}`.

1. `erase_sublist_of_sublist`: `B.erase v` is again a sublist of `U`.
2. `neighborhood_erase_subset`: `N(B.erase v) ⊆ N(B)`.
3. `tight_erase_length` (the private-phase bound): for tight `B` and `v ∈ B`,
   `|N(B)| ≤ |N(B.erase v)| + 1`.  Indeed Hall on `B.erase v` gives
   `|B| - 1 = |B.erase v| ≤ |N(B.erase v)|` and tightness gives `|N(B)| = |B|`.
4. `privatePhases e p B lag v` is the list of phases in `N(B)` that are not in `N(B.erase v)`,
   i.e. the phases covered by `v` and by no other member of `B`;
   `private_phases_le_one` says it has length at most `1`, and `private_phase_unique` restates
   this as: any two private phases of `v` coincide.
5. `lag7_w1_two_phases_covered_by_others`: for `7 ≤ p`, a periodic `e`, and a lag-7 member `u`
   of a tight `B` whose past is `w1 = [S, A, A, A, A, S, S]` (subtractions at `u - 1`, `u - 6`,
   `u - 7`), at least two of the three phases `endpointPhase p u 1`, `endpointPhase p u 6`,
   `endpointPhase p u 7` lie in `N(B.erase u)`, i.e. are covered by other members of `B`.
   The three phases are pairwise distinct because their offsets differ by less than `p`
   (`endpointPhase_ne_of_lt`), all three lie in `N(B)` (`endpointPhase_mem_neighborhood`), and at
   most one of them is private by item 4.

These lemmas explain the `cov<2: 0` column of `docs/data/issue73_20260915/tight_structure.txt`:
there `cov` counts, for each lag-7 member `u` of a tight set `B`, how many of the three
subtraction phases of `u` are covered by the other members of `B`, and the census never sees
`cov < 2`.  Item 5 is that observation as a theorem.

Nothing here proves G1 or Gate T6: every statement assumes Hall's condition on `U` and only
constrains the shape of tight subsets under that assumption.  No deletability statement and no
Hall condition is established.
-/

namespace Recaman.TightPrivatePhase

open TwoSSTightDisjoint TwoSSAvoidTight TightSubsetDecomposition TightHallAugmentation
open LeadingRunSupply LagSevenPrefixRigidity LowSSPeriodicSupply SharpPeriodicSupply TwoSSLocalDonation

/-- Erasing an element from a sublist of `U` leaves a sublist of `U`. -/
theorem erase_sublist_of_sublist {B U : List Nat} (hB : List.Sublist B U) (v : Nat) :
    List.Sublist (B.erase v) U :=
  List.Sublist.trans List.erase_sublist hB

/-- The subtraction neighborhood of `B.erase v` is contained in that of `B`. -/
theorem neighborhood_erase_subset (e : Int → Bool) (p : Nat) (B : List Nat) (lag : Nat → Nat)
    (v : Nat) :
    neighborhood e p (B.erase v) lag ⊆ neighborhood e p B lag := by
  intro s hs
  rw [mem_neighborhood_iff_exists_singleton] at hs ⊢
  obtain ⟨u, hu, hsu⟩ := hs
  exact ⟨u, List.mem_of_mem_erase hu, hsu⟩

/-- **Private-phase bound.** Under Hall's condition on `U`, a tight sublist `B` of `U` and a
member `v ∈ B` satisfy `|N(B)| ≤ |N(B.erase v)| + 1`: Hall applied to `B.erase v` gives
`|B| - 1 ≤ |N(B.erase v)|`, and tightness gives `|N(B)| = |B|`. -/
theorem tight_erase_length (e : Int → Bool) (p : Nat) (U B : List Nat) (lag : Nat → Nat)
    (hhall : ∀ A : List Nat, List.Sublist A U → A.length ≤ (neighborhood e p A lag).length)
    (hB : List.Sublist B U)
    (htight : (neighborhood e p B lag).length = B.length)
    (v : Nat) (hvB : v ∈ B) :
    (neighborhood e p B lag).length ≤ (neighborhood e p (B.erase v) lag).length + 1 := by
  have h1 := hhall (B.erase v) (erase_sublist_of_sublist hB v)
  have h2 : (B.erase v).length = B.length - 1 := List.length_erase_of_mem hvB
  omega

/-- The subtraction phases covered by `B` but not by `B.erase v`: the phases that only the
member `v` covers inside `B`. -/
def privatePhases (e : Int → Bool) (p : Nat) (B : List Nat) (lag : Nat → Nat) (v : Nat) :
    List Nat :=
  (neighborhood e p B lag).filter (fun s => decide (s ∉ neighborhood e p (B.erase v) lag))

/-- Membership in `privatePhases`. -/
theorem mem_privatePhases_iff (e : Int → Bool) (p : Nat) (B : List Nat) (lag : Nat → Nat)
    (v s : Nat) :
    s ∈ privatePhases e p B lag v ↔
      s ∈ neighborhood e p B lag ∧ s ∉ neighborhood e p (B.erase v) lag := by
  unfold privatePhases
  rw [List.mem_filter]
  simp

/-- Splitting a list by membership in another list. -/
theorem length_filter_mem_add_filter_not_mem (l l' : List Nat) :
    (l.filter (fun s => decide (s ∈ l'))).length +
      (l.filter (fun s => decide (s ∉ l'))).length = l.length := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    by_cases hx : x ∈ l'
    · rw [List.filter_cons_of_pos (by simp [hx]), List.filter_cons_of_neg (by simp [hx])]
      simp only [List.length_cons]
      omega
    · rw [List.filter_cons_of_neg (by simp [hx]), List.filter_cons_of_pos (by simp [hx])]
      simp only [List.length_cons]
      omega

/-- If `l'` is nodup and `l' ⊆ l`, then `|l'|` plus the number of elements of `l` outside `l'`
is at most `|l|`. -/
theorem length_add_filter_not_mem_le (l l' : List Nat) (hl' : l'.Nodup) (hsub : l' ⊆ l) :
    l'.length + (l.filter (fun s => decide (s ∉ l'))).length ≤ l.length := by
  have hsplit := length_filter_mem_add_filter_not_mem l l'
  have hin : l' ⊆ l.filter (fun s => decide (s ∈ l')) := by
    intro x hx
    rw [List.mem_filter]
    exact ⟨hsub hx, by simp [hx]⟩
  have hle := hl'.length_le_of_subset hin
  omega

/-- **At most one private phase.** Under Hall's condition on `U`, every member `v` of a tight
sublist `B` of `U` has at most one subtraction phase that no other member of `B` covers. -/
theorem private_phases_le_one (e : Int → Bool) (p : Nat) (U B : List Nat) (lag : Nat → Nat)
    (hhall : ∀ A : List Nat, List.Sublist A U → A.length ≤ (neighborhood e p A lag).length)
    (hB : List.Sublist B U)
    (htight : (neighborhood e p B lag).length = B.length)
    (v : Nat) (hvB : v ∈ B) :
    (privatePhases e p B lag v).length ≤ 1 := by
  have h3 := tight_erase_length e p U B lag hhall hB htight v hvB
  have h4 := length_add_filter_not_mem_le (neighborhood e p B lag)
    (neighborhood e p (B.erase v) lag) (neighborhood_nodup e p (B.erase v) lag)
    (neighborhood_erase_subset e p B lag v)
  unfold privatePhases
  omega

/-- A list containing two distinct elements has length at least `2`. -/
theorem two_le_length_of_mem_ne {l : List Nat} {a b : Nat} (ha : a ∈ l) (hb : b ∈ l)
    (hab : a ≠ b) : 2 ≤ l.length := by
  have hnd : ([a, b] : List Nat).Nodup := by simp [hab]
  have hsub : ([a, b] : List Nat) ⊆ l := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hb
  exact hnd.length_le_of_subset hsub

/-- Restatement of `private_phases_le_one`: two private phases of the same member coincide. -/
theorem private_phase_unique (e : Int → Bool) (p : Nat) (U B : List Nat) (lag : Nat → Nat)
    (hhall : ∀ A : List Nat, List.Sublist A U → A.length ≤ (neighborhood e p A lag).length)
    (hB : List.Sublist B U)
    (htight : (neighborhood e p B lag).length = B.length)
    (v : Nat) (hvB : v ∈ B)
    (s t : Nat) (hs : s ∈ privatePhases e p B lag v) (ht : t ∈ privatePhases e p B lag v) :
    s = t := by
  by_cases hst : s = t
  · exact hst
  · exfalso
    have h2 := two_le_length_of_mem_ne hs ht hst
    have h1 := private_phases_le_one e p U B lag hhall hB htight v hvB
    omega

/-- For a periodic `e`, the phase of an `S` bit at offset `d` inside the window of a member `u`
of `B` lies in `N(B)`. -/
theorem endpointPhase_mem_neighborhood (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (B : List Nat) (lag : Nat → Nat) (u : Nat) (huB : u ∈ B)
    (d : Nat) (hd : 0 < d) (hdl : d ≤ lag u)
    (hS : e ((u : Int) - (d : Int)) = false) :
    endpointPhase p (u : Int) d ∈ neighborhood e p B lag := by
  rw [mem_neighborhood_iff]
  refine ⟨oldest_is_subtraction e p hp hper u d hS, ?_⟩
  rw [isCoveredBySubset_iff]
  obtain ⟨i, hi, he, hmod⟩ := oldest_covered_by_window e p hp u d hd hS
  exact ⟨u, huB, i, by omega, he, hmod⟩

/-- Two offsets `d < d'` inside a window with `d' - d < p` give distinct phases. -/
theorem endpointPhase_ne_of_lt (p : Nat) (hp : 0 < p) (t : Int) (d d' : Nat)
    (hdd' : d < d') (hlt : d' - d < p) :
    endpointPhase p t d ≠ endpointPhase p t d' := by
  intro heq
  unfold endpointPhase at heq
  have hmod := phase_eq_mod p hp _ _ heq
  rw [Int.emod_eq_emod_iff_emod_sub_eq_zero] at hmod
  have hdiff : (t - (d : Int)) - (t - (d' : Int)) = ((d' - d : Nat) : Int) := by omega
  rw [hdiff, Int.emod_eq_of_lt (by omega) (by omega)] at hmod
  omega

/-- **Lag-7 `w1` members are covered twice over.** For `7 ≤ p`, a periodic `e`, Hall's condition
on `U`, a tight sublist `B` of `U`, and a member `u ∈ B` with `lag u = 7` and
`past e u 7 = w1` (subtractions at `u - 1`, `u - 6`, `u - 7`), at least two of the three phases
`endpointPhase p u 1`, `endpointPhase p u 6`, `endpointPhase p u 7` are covered by the other
members of `B`, i.e. lie in `N(B.erase u)`. -/
theorem lag7_w1_two_phases_covered_by_others (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hp7 : 7 ≤ p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U B : List Nat) (lag : Nat → Nat)
    (hhall : ∀ A : List Nat, List.Sublist A U → A.length ≤ (neighborhood e p A lag).length)
    (hB : List.Sublist B U)
    (htight : (neighborhood e p B lag).length = B.length)
    (u : Nat) (huB : u ∈ B) (hlu : lag u = 7) (hw1 : past e (u : Int) 7 = w1) :
    (endpointPhase p (u : Int) 1 ∈ neighborhood e p (B.erase u) lag ∧
        endpointPhase p (u : Int) 6 ∈ neighborhood e p (B.erase u) lag) ∨
      (endpointPhase p (u : Int) 1 ∈ neighborhood e p (B.erase u) lag ∧
        endpointPhase p (u : Int) 7 ∈ neighborhood e p (B.erase u) lag) ∨
      (endpointPhase p (u : Int) 6 ∈ neighborhood e p (B.erase u) lag ∧
        endpointPhase p (u : Int) 7 ∈ neighborhood e p (B.erase u) lag) := by
  obtain ⟨h1, _, _, _, _, h6, h7⟩ := w1_bits e (u : Int) hw1
  have hS1 : e ((u : Int) - ((1 : Nat) : Int)) = false := by
    have : (u : Int) - ((1 : Nat) : Int) = (u : Int) - 1 := by omega
    rw [this]; exact h1
  have hS6 : e ((u : Int) - ((6 : Nat) : Int)) = false := by
    have : (u : Int) - ((6 : Nat) : Int) = (u : Int) - 6 := by omega
    rw [this]; exact h6
  have hS7 : e ((u : Int) - ((7 : Nat) : Int)) = false := by
    have : (u : Int) - ((7 : Nat) : Int) = (u : Int) - 7 := by omega
    rw [this]; exact h7
  have hm1 := endpointPhase_mem_neighborhood e p hp hper B lag u huB 1 (by omega) (by omega) hS1
  have hm6 := endpointPhase_mem_neighborhood e p hp hper B lag u huB 6 (by omega) (by omega) hS6
  have hm7 := endpointPhase_mem_neighborhood e p hp hper B lag u huB 7 (by omega) (by omega) hS7
  have hne16 := endpointPhase_ne_of_lt p hp (u : Int) 1 6 (by omega) (by omega)
  have hne17 := endpointPhase_ne_of_lt p hp (u : Int) 1 7 (by omega) (by omega)
  have hne67 := endpointPhase_ne_of_lt p hp (u : Int) 6 7 (by omega) (by omega)
  have hpriv := private_phases_le_one e p U B lag hhall hB htight u huB
  have hmem : ∀ s, s ∈ neighborhood e p B lag → s ∉ neighborhood e p (B.erase u) lag →
      s ∈ privatePhases e p B lag u :=
    fun s hs hns => (mem_privatePhases_iff e p B lag u s).mpr ⟨hs, hns⟩
  by_cases k1 : endpointPhase p (u : Int) 1 ∈ neighborhood e p (B.erase u) lag
  · by_cases k6 : endpointPhase p (u : Int) 6 ∈ neighborhood e p (B.erase u) lag
    · exact Or.inl ⟨k1, k6⟩
    · by_cases k7 : endpointPhase p (u : Int) 7 ∈ neighborhood e p (B.erase u) lag
      · exact Or.inr (Or.inl ⟨k1, k7⟩)
      · exfalso
        have h2 := two_le_length_of_mem_ne (hmem _ hm6 k6) (hmem _ hm7 k7) hne67
        omega
  · by_cases k6 : endpointPhase p (u : Int) 6 ∈ neighborhood e p (B.erase u) lag
    · by_cases k7 : endpointPhase p (u : Int) 7 ∈ neighborhood e p (B.erase u) lag
      · exact Or.inr (Or.inr ⟨k6, k7⟩)
      · exfalso
        have h2 := two_le_length_of_mem_ne (hmem _ hm1 k1) (hmem _ hm7 k7) hne17
        omega
    · exfalso
      have h2 := two_le_length_of_mem_ne (hmem _ hm1 k1) (hmem _ hm6 k6) hne16
      omega

end Recaman.TightPrivatePhase
