import Recaman.TightPrivatePhase

/-!
# HallMatching: Hall's marriage theorem for finite lists and the owner map of a tight subset

This module proves Hall's marriage theorem for finite lists (core Lean only) by the
Halmos–Vaughan induction, and derives its *onto* form for tight subsets.  The abstract layer
speaks about an arbitrary coverage relation `cov : Nat → Nat → Bool` between left vertices and
elements of a nodup `ground` list; the concrete wrapper instantiates it with the window coverage
of the T6 modules, where `cover` becomes `neighborhood` by definitional unfolding
(`neighborhood_eq_cover`).

## What is proved

1. `cover cov ground A` is the sublist of `ground` covered by some `u ∈ A`; it depends only on
   the members of `A` (`cover_congr`), is monotone in `A` (`cover_mono`), is nodup for nodup
   `ground` (`cover_nodup`), commutes with filtering the ground list (`cover_filter_ground`),
   and splits over `A ++ A0` into the part covered by `A0` and the part of `A` covered outside
   `N(A0)` (`cover_append_length`).
2. `hall_matching` (Hall's marriage theorem): if every sublist `A` of a nodup `B` satisfies
   `|A| ≤ |cover cov ground A|`, then there is `m : Nat → Nat` with `m b ∈ cover cov ground [b]`
   for every `b ∈ B` and `m` injective on `B`.  The proof is the Halmos–Vaughan induction on
   `|B|`, generalising `ground`: if some non-empty proper sublist `A0` is critical
   (`|cover A0| = |A0|`), match `A0` inside `cover A0` and the rest `B \ A0` inside
   `ground \ cover A0`; otherwise every non-empty proper sublist has slack, so the head `b` may
   take any `s ∈ cover [b]` and the tail is matched inside `ground \ {s}`.
3. `hall_matching_onto`: if moreover `B` is tight, `|cover cov ground B| = |B|`, the matching is
   onto `cover cov ground B`.
4. `tight_owner_map`: the concrete statement.  Under Hall's condition on `U`, a tight sublist
   `B ⊆ U` has an owner map `own : B → N(B)`: each member owns a subtraction phase of its own
   window, distinct members own distinct phases, and every phase of `N(B)` is owned.

## What is not proved

Nothing here concerns Gate T6, periodicity, or the sign word beyond the wrapper
`tight_owner_map`: Hall's condition is always a hypothesis, never a conclusion, and no
deletability statement is established.
-/

namespace Recaman.HallMatching

open TwoSSTightDisjoint TwoSSAvoidTight TightSubsetDecomposition TightHallAugmentation
open TightPrivatePhase UniversalQuantumWindowCapacity

/-- Neighbourhood of a list of left vertices `A`: the ground elements covered by some `u ∈ A`. -/
def cover (cov : Nat → Nat → Bool) (ground : List Nat) (A : List Nat) : List Nat :=
  ground.filter (fun s => A.any (fun u => cov u s))

/-- The concrete subtraction neighbourhood is an instance of `cover`, definitionally. -/
theorem neighborhood_eq_cover (e : Int → Bool) (p : Nat) (A : List Nat) (lag : Nat → Nat) :
    neighborhood e p A lag =
      cover (fun u s => isCoveredByWindow e p (u : Int) (lag u) s)
        (LagElevenPeriodic.subPhases e 0 p) A :=
  rfl

/-- Membership in `cover`. -/
theorem mem_cover_iff (cov : Nat → Nat → Bool) (ground A : List Nat) (s : Nat) :
    s ∈ cover cov ground A ↔ s ∈ ground ∧ ∃ u ∈ A, cov u s = true := by
  unfold cover
  rw [List.mem_filter, List.any_eq_true]

/-- `cover cov ground A` is a sublist of `ground`. -/
theorem cover_sublist (cov : Nat → Nat → Bool) (ground A : List Nat) :
    List.Sublist (cover cov ground A) ground :=
  List.filter_sublist

/-- `cover cov ground A` is nodup when `ground` is. -/
theorem cover_nodup (cov : Nat → Nat → Bool) {ground : List Nat} (hg : ground.Nodup)
    (A : List Nat) : (cover cov ground A).Nodup :=
  List.Nodup.sublist (cover_sublist cov ground A) hg

/-- `cover` depends only on the members of `A`. -/
theorem cover_congr (cov : Nat → Nat → Bool) (ground : List Nat) {A A' : List Nat}
    (hmem : ∀ x, x ∈ A ↔ x ∈ A') : cover cov ground A = cover cov ground A' := by
  unfold cover
  apply List.filter_congr
  intro s _
  rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
  constructor
  · rintro ⟨u, hu, h⟩
    exact ⟨u, (hmem u).mp hu, h⟩
  · rintro ⟨u, hu, h⟩
    exact ⟨u, (hmem u).mpr hu, h⟩

/-- `cover` is monotone in `A`. -/
theorem cover_mono (cov : Nat → Nat → Bool) (ground : List Nat) {A A' : List Nat}
    (hsub : ∀ x, x ∈ A → x ∈ A') : cover cov ground A ⊆ cover cov ground A' := by
  intro s hs
  rw [mem_cover_iff] at hs ⊢
  obtain ⟨hg, u, hu, h⟩ := hs
  exact ⟨hg, u, hsub u hu, h⟩

/-- Covering from a filtered ground list is filtering the cover. -/
theorem cover_filter_ground (cov : Nat → Nat → Bool) (ground A : List Nat) (q : Nat → Bool) :
    cover cov (ground.filter q) A = (cover cov ground A).filter q := by
  unfold cover
  rw [List.filter_filter, List.filter_filter]
  apply List.filter_congr
  intro s _
  exact Bool.and_comm _ _

/-- Covering from a filtered ground list gives a subset of the cover. -/
theorem cover_filter_subset (cov : Nat → Nat → Bool) (ground A : List Nat) (q : Nat → Bool) :
    cover cov (ground.filter q) A ⊆ cover cov ground A := by
  rw [cover_filter_ground]
  exact List.filter_sublist.subset

/-- Splitting a filter by a disjunction: the elements satisfying `p || q` are those satisfying
`p` together with those satisfying `q` but not `p`. -/
theorem length_filter_or (l : List Nat) (p q : Nat → Bool) :
    (l.filter (fun x => p x || q x)).length =
      (l.filter p).length + (l.filter (fun x => q x && !p x)).length := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    cases hp : p x <;> cases hq : q x <;> simp [hp, hq, ih] <;> omega

/-- For `s ∈ ground`, not being in `cover cov ground A0` is the negation of being covered by
`A0`. -/
theorem decide_not_mem_cover_eq (cov : Nat → Nat → Bool) (ground A0 : List Nat) (s : Nat)
    (hs : s ∈ ground) :
    decide (s ∉ cover cov ground A0) = !(A0.any (fun u => cov u s)) := by
  have hmem : s ∈ cover cov ground A0 ↔ A0.any (fun u => cov u s) = true := by
    unfold cover
    rw [List.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hs, h⟩⟩
  cases h : A0.any (fun u => cov u s)
  · have hnot : s ∉ cover cov ground A0 := fun hc => by
      rw [hmem, h] at hc
      exact Bool.noConfusion hc
    simp [hnot]
  · have hin : s ∈ cover cov ground A0 := hmem.mpr h
    simp [hin]

/-- **Cover of a union.** The cover of `A ++ A0` splits into the cover of `A0` and the cover of
`A` inside the ground list with `cover cov ground A0` removed. -/
theorem cover_append_length (cov : Nat → Nat → Bool) (ground A A0 : List Nat) :
    (cover cov ground (A ++ A0)).length =
      (cover cov ground A0).length +
        (cover cov (ground.filter (fun s => decide (s ∉ cover cov ground A0))) A).length := by
  rw [cover_filter_ground]
  have h1 : cover cov ground (A ++ A0) =
      ground.filter (fun s => A0.any (fun u => cov u s) || A.any (fun u => cov u s)) := by
    unfold cover
    apply List.filter_congr
    intro s _
    rw [List.any_append, Bool.or_comm]
  rw [h1, length_filter_or]
  have h2 : (cover cov ground A).filter (fun s => decide (s ∉ cover cov ground A0)) =
      ground.filter (fun s => A.any (fun u => cov u s) && !(A0.any (fun u => cov u s))) := by
    unfold cover
    rw [List.filter_filter]
    apply List.filter_congr
    intro s hs
    rw [Bool.and_comm]
    have := decide_not_mem_cover_eq cov ground A0 s hs
    unfold cover at this
    rw [this]
  rw [h2]
  rfl

/-- Hall's condition on sublists of a nodup `B` transfers to nodup lists whose members lie in
`B`: such a list is a permutation of a sublist of `B` with the same cover. -/
theorem hall_of_subset (cov : Nat → Nat → Bool) (ground B : List Nat) (hB : B.Nodup)
    (hhall : ∀ A : List Nat, List.Sublist A B → A.length ≤ (cover cov ground A).length)
    (A : List Nat) (hA : A.Nodup) (hsub : ∀ x, x ∈ A → x ∈ B) :
    A.length ≤ (cover cov ground A).length := by
  have hA'sub : List.Sublist (B.filter (fun x => decide (x ∈ A))) B := List.filter_sublist
  have hA'nodup : (B.filter (fun x => decide (x ∈ A))).Nodup := List.Nodup.sublist hA'sub hB
  have hmem : ∀ x, x ∈ B.filter (fun x => decide (x ∈ A)) ↔ x ∈ A := by
    intro x
    rw [List.mem_filter, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨hsub x h, h⟩⟩
  have hperm : List.Perm (B.filter (fun x => decide (x ∈ A))) A :=
    (List.perm_ext_iff_of_nodup hA'nodup hA).mpr hmem
  have hlen := hperm.length_eq
  have hcov := cover_congr cov ground hmem
  have h := hhall _ hA'sub
  rw [hlen, hcov] at h
  exact h

/-- A map injective on a nodup list yields a nodup image list. -/
theorem nodup_map_of_inj_on (f : Nat → Nat) (l : List Nat) (hl : l.Nodup)
    (hinj : ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) : (l.map f).Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons x xs ih =>
    rw [List.nodup_cons] at hl
    rw [List.map_cons, List.nodup_cons]
    constructor
    · intro hmem
      rw [List.mem_map] at hmem
      obtain ⟨y, hy, hfy⟩ := hmem
      have hyx := hinj y (List.mem_cons_of_mem x hy) x List.mem_cons_self hfy
      exact hl.1 (hyx ▸ hy)
    · exact ih hl.2
        (fun a ha b hb => hinj a (List.mem_cons_of_mem x ha) b (List.mem_cons_of_mem x hb))

/-- **Halmos–Vaughan induction.** Hall's marriage theorem for nodup lists `B` of length at most
`n`, with the ground list generalised. -/
theorem hall_matching_aux (cov : Nat → Nat → Bool) (n : Nat) :
    ∀ (ground : List Nat), ground.Nodup → ∀ (B : List Nat), B.Nodup → B.length ≤ n →
      (∀ A : List Nat, List.Sublist A B → A.length ≤ (cover cov ground A).length) →
      ∃ m : Nat → Nat, (∀ b ∈ B, m b ∈ cover cov ground [b]) ∧
        (∀ b ∈ B, ∀ b' ∈ B, m b = m b' → b = b') := by
  induction n with
  | zero =>
    intro ground _ B _ hlen _
    have hnil : B = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hnil
    exact ⟨id, fun b hb => absurd hb List.not_mem_nil, fun b hb => absurd hb List.not_mem_nil⟩
  | succ n ih =>
    intro ground hg B hB hlen hhall
    cases B with
    | nil =>
      exact ⟨id, fun b hb => absurd hb List.not_mem_nil, fun b hb => absurd hb List.not_mem_nil⟩
    | cons b B' =>
      by_cases hcrit : ∃ A0 : List Nat, List.Sublist A0 (b :: B') ∧ A0 ≠ [] ∧
          A0.length < (b :: B').length ∧ (cover cov ground A0).length = A0.length
      · -- Case 2: a critical non-empty proper sublist `A0` exists.
        obtain ⟨A0, hA0sub, hA0ne, hA0lt, hA0tight⟩ := hcrit
        have hA0nodup : A0.Nodup := List.Nodup.sublist hA0sub hB
        have hA0pos : 0 < A0.length := List.length_pos_iff.mpr hA0ne
        obtain ⟨m1, hm1mem, hm1inj⟩ := ih ground hg A0 hA0nodup (by omega)
          (fun A hA => hhall A (hA.trans hA0sub))
        -- The rest `B1 = B \ A0` and the reduced ground `ground1 = ground \ cover A0`.
        have hB1sub : List.Sublist ((b :: B').filter (fun x => decide (x ∉ A0))) (b :: B') :=
          List.filter_sublist
        have hB1nodup : ((b :: B').filter (fun x => decide (x ∉ A0))).Nodup :=
          List.Nodup.sublist hB1sub hB
        have hB1len : ((b :: B').filter (fun x => decide (x ∉ A0))).length + A0.length =
            (b :: B').length := by
          have hsplit := length_filter_mem_add_filter_not_mem (b :: B') A0
          rw [filter_mem_of_sublist_nodup hA0sub hB] at hsplit
          omega
        have hg1 : (ground.filter (fun s => decide (s ∉ cover cov ground A0))).Nodup :=
          List.Nodup.sublist List.filter_sublist hg
        -- Hall's condition for sublists of `B1` with respect to `ground1`.
        have hhall1 : ∀ A : List Nat, List.Sublist A ((b :: B').filter (fun x => decide (x ∉ A0))) →
            A.length ≤ (cover cov (ground.filter (fun s => decide (s ∉ cover cov ground A0))) A).length := by
          intro A hA
          have hAnodup : A.Nodup := List.Nodup.sublist hA hB1nodup
          have hAdisj : ∀ x, x ∈ A → x ∉ A0 := by
            intro x hx
            have hx' := hA.subset hx
            rw [List.mem_filter, decide_eq_true_eq] at hx'
            exact hx'.2
          have hAB : ∀ x, x ∈ A → x ∈ b :: B' := fun x hx => hB1sub.subset (hA.subset hx)
          have hunion_nodup : (A ++ A0).Nodup := by
            rw [List.nodup_append]
            refine ⟨hAnodup, hA0nodup, ?_⟩
            intro x hx y hy hxy
            exact hAdisj x hx (hxy ▸ hy)
          have hunion_sub : ∀ x, x ∈ A ++ A0 → x ∈ b :: B' := by
            intro x hx
            rw [List.mem_append] at hx
            rcases hx with hx | hx
            · exact hAB x hx
            · exact hA0sub.subset hx
          have hunion := hall_of_subset cov ground (b :: B') hB hhall (A ++ A0) hunion_nodup hunion_sub
          rw [List.length_append, cover_append_length] at hunion
          omega
        obtain ⟨m2, hm2mem, hm2inj⟩ := ih (ground.filter (fun s => decide (s ∉ cover cov ground A0)))
          hg1 ((b :: B').filter (fun x => decide (x ∉ A0))) hB1nodup (by omega) hhall1
        -- Values of `m2` avoid `cover A0`.
        have hm2out : ∀ x, x ∈ (b :: B').filter (fun x => decide (x ∉ A0)) →
            m2 x ∉ cover cov ground A0 := by
          intro x hx
          have h := (cover_sublist cov _ [x]).subset (hm2mem x hx)
          rw [List.mem_filter, decide_eq_true_eq] at h
          exact h.2
        have hmemB1 : ∀ x, x ∈ b :: B' → x ∉ A0 → x ∈ (b :: B').filter (fun x => decide (x ∉ A0)) := by
          intro x hx hx0
          rw [List.mem_filter, decide_eq_true_eq]
          exact ⟨hx, hx0⟩
        have hm1in : ∀ x, x ∈ A0 → m1 x ∈ cover cov ground A0 := by
          intro x hx
          exact cover_mono cov ground
            (fun y hy => by rw [List.mem_singleton] at hy; exact hy ▸ hx) (hm1mem x hx)
        refine ⟨fun x => if x ∈ A0 then m1 x else m2 x, ?_, ?_⟩
        · intro x hx
          by_cases hx0 : x ∈ A0
          · simp only [hx0, if_true]
            exact hm1mem x hx0
          · simp only [hx0, if_false]
            exact cover_filter_subset cov ground [x] _ (hm2mem x (hmemB1 x hx hx0))
        · intro x hx y hy hxy
          by_cases hx0 : x ∈ A0
          · by_cases hy0 : y ∈ A0
            · simp only [hx0, hy0, if_true] at hxy
              exact hm1inj x hx0 y hy0 hxy
            · simp only [hx0, hy0, if_true, if_false] at hxy
              exact absurd (hxy ▸ hm1in x hx0) (hm2out y (hmemB1 y hy hy0))
          · by_cases hy0 : y ∈ A0
            · simp only [hx0, hy0, if_true, if_false] at hxy
              exact absurd (hxy.symm ▸ hm1in y hy0) (hm2out x (hmemB1 x hx hx0))
            · simp only [hx0, hy0, if_false] at hxy
              exact hm2inj x (hmemB1 x hx hx0) y (hmemB1 y hy hy0) hxy
      · -- Case 1: every non-empty proper sublist has slack.
        have hslack : ∀ A : List Nat, List.Sublist A (b :: B') → A ≠ [] →
            A.length < (b :: B').length → A.length + 1 ≤ (cover cov ground A).length := by
          intro A hA hne hlt
          have h1 := hhall A hA
          have h2 : (cover cov ground A).length ≠ A.length :=
            fun heq => hcrit ⟨A, hA, hne, hlt, heq⟩
          omega
        rw [List.nodup_cons] at hB
        have hbB' : b ∉ B' := hB.1
        have hB'nodup : B'.Nodup := hB.2
        -- Pick `s ∈ cover [b]`.
        have hb1 := hhall [b] (List.Sublist.cons_cons b (List.nil_sublist B'))
        obtain ⟨s, hs⟩ := List.exists_mem_of_length_pos
          (show 0 < (cover cov ground [b]).length by simp at hb1; omega)
        have hg' : (ground.filter (fun t => decide (t ≠ s))).Nodup :=
          List.Nodup.sublist List.filter_sublist hg
        -- Hall's condition for sublists of `B'` with respect to `ground \ {s}`.
        have hhall' : ∀ A : List Nat, List.Sublist A B' →
            A.length ≤ (cover cov (ground.filter (fun t => decide (t ≠ s))) A).length := by
          intro A hA
          by_cases hne : A = []
          · subst hne
            exact Nat.zero_le _
          · have hAB : List.Sublist A (b :: B') := List.Sublist.cons b hA
            have hlt : A.length < (b :: B').length := by
              have := hA.length_le
              simp only [List.length_cons]
              omega
            have h1 := hslack A hAB hne hlt
            rw [cover_filter_ground]
            have h2 := filter_ne_nodup (cover_nodup cov hg A) s
            omega
        obtain ⟨m', hm'mem, hm'inj⟩ := ih (ground.filter (fun t => decide (t ≠ s))) hg' B' hB'nodup
          (by simp only [List.length_cons] at hlen; omega) hhall'
        have hm'ne : ∀ x, x ∈ B' → m' x ≠ s := by
          intro x hx
          have h := (cover_sublist cov _ [x]).subset (hm'mem x hx)
          rw [List.mem_filter, decide_eq_true_eq] at h
          exact h.2
        refine ⟨fun x => if x = b then s else m' x, ?_, ?_⟩
        · intro x hx
          rw [List.mem_cons] at hx
          rcases hx with rfl | hx
          · simp only [if_true]
            exact hs
          · have hxb : x ≠ b := fun hxb => hbB' (hxb ▸ hx)
            simp only [hxb, if_false]
            exact cover_filter_subset cov ground [x] _ (hm'mem x hx)
        · intro x hx y hy hxy
          rw [List.mem_cons] at hx hy
          rcases hx with rfl | hx
          · rcases hy with rfl | hy
            · rfl
            · have hyb : y ≠ x := fun hyb => hbB' (hyb ▸ hy)
              simp only [hyb, if_true, if_false] at hxy
              exact absurd hxy.symm (hm'ne y hy)
          · have hxb : x ≠ b := fun hxb => hbB' (hxb ▸ hx)
            rcases hy with rfl | hy
            · simp only [hxb, if_true, if_false] at hxy
              exact absurd hxy (hm'ne x hx)
            · have hyb : y ≠ b := fun hyb => hbB' (hyb ▸ hy)
              simp only [hxb, hyb, if_false] at hxy
              exact hm'inj x hx y hy hxy

/-- **Hall's marriage theorem for lists.** If every sublist `A` of a nodup `B` satisfies
`|A| ≤ |cover cov ground A|`, then some `m` sends each `b ∈ B` into `cover cov ground [b]`
and is injective on `B`. -/
theorem hall_matching (cov : Nat → Nat → Bool) (ground : List Nat) (hg : ground.Nodup)
    (B : List Nat) (hB : B.Nodup)
    (hhall : ∀ A : List Nat, List.Sublist A B → A.length ≤ (cover cov ground A).length) :
    ∃ m : Nat → Nat, (∀ b ∈ B, m b ∈ cover cov ground [b]) ∧
      (∀ b ∈ B, ∀ b' ∈ B, m b = m b' → b = b') :=
  hall_matching_aux cov B.length ground hg B hB (Nat.le_refl _) hhall

/-- **Onto form.** Under Hall's condition, a tight `B` (`|cover cov ground B| = |B|`) has a
matching that is also onto `cover cov ground B`: the `|B|` distinct images all lie in a
nodup list of length `|B|`, so nothing is missed. -/
theorem hall_matching_onto (cov : Nat → Nat → Bool) (ground : List Nat) (hg : ground.Nodup)
    (B : List Nat) (hB : B.Nodup)
    (hhall : ∀ A : List Nat, List.Sublist A B → A.length ≤ (cover cov ground A).length)
    (htight : (cover cov ground B).length = B.length) :
    ∃ m : Nat → Nat, (∀ b ∈ B, m b ∈ cover cov ground [b]) ∧
      (∀ b ∈ B, ∀ b' ∈ B, m b = m b' → b = b') ∧
      (∀ s ∈ cover cov ground B, ∃ b ∈ B, m b = s) := by
  obtain ⟨m, hmem, hinj⟩ := hall_matching cov ground hg B hB hhall
  refine ⟨m, hmem, hinj, ?_⟩
  intro s hs
  by_cases hex : ∃ b ∈ B, m b = s
  · exact hex
  · exfalso
    have hnodup : (B.map m).Nodup := nodup_map_of_inj_on m B hB hinj
    have hsub : B.map m ⊆ cover cov ground B := by
      intro t ht
      rw [List.mem_map] at ht
      obtain ⟨b, hb, rfl⟩ := ht
      exact cover_mono cov ground
        (fun x hx => by rw [List.mem_singleton] at hx; exact hx ▸ hb) (hmem b hb)
    have hsnot : s ∉ B.map m := by
      intro hs'
      rw [List.mem_map] at hs'
      obtain ⟨b, hb, hbs⟩ := hs'
      exact hex ⟨b, hb, hbs⟩
    have hnodup' : (s :: B.map m).Nodup := List.nodup_cons.mpr ⟨hsnot, hnodup⟩
    have hsub' : (s :: B.map m) ⊆ cover cov ground B := by
      intro t ht
      rw [List.mem_cons] at ht
      rcases ht with rfl | ht
      · exact hs
      · exact hsub ht
    have hle := hnodup'.length_le_of_subset hsub'
    rw [List.length_cons, List.length_map] at hle
    omega

/-- **Owner map of a tight subset.** Under Hall's condition on `U`, a tight sublist `B ⊆ U`
(|N(B)| = |B|) has an owner map `own : B → N(B)`: each member owns a subtraction phase of its own
window, distinct members own distinct phases, and every phase of `N(B)` is owned by a member. -/
theorem tight_owner_map (e : Int → Bool) (p : Nat) (U B : List Nat) (lag : Nat → Nat)
    (hU : U.Nodup)
    (hhall : ∀ A : List Nat, List.Sublist A U → A.length ≤ (neighborhood e p A lag).length)
    (hB : List.Sublist B U)
    (htight : (neighborhood e p B lag).length = B.length) :
    ∃ own : Nat → Nat, (∀ b ∈ B, own b ∈ neighborhood e p [b] lag) ∧
      (∀ b ∈ B, ∀ b' ∈ B, own b = own b' → b = b') ∧
      (∀ s ∈ neighborhood e p B lag, ∃ b ∈ B, own b = s) := by
  have hBnodup : B.Nodup := List.Nodup.sublist hB hU
  have hhallB : ∀ A : List Nat, List.Sublist A B →
      A.length ≤ (cover (fun u s => isCoveredByWindow e p (u : Int) (lag u) s)
        (LagElevenPeriodic.subPhases e 0 p) A).length := by
    intro A hA
    rw [← neighborhood_eq_cover]
    exact hhall A (hA.trans hB)
  have htight' : (cover (fun u s => isCoveredByWindow e p (u : Int) (lag u) s)
      (LagElevenPeriodic.subPhases e 0 p) B).length = B.length := by
    rw [← neighborhood_eq_cover]
    exact htight
  obtain ⟨m, h1, h2, h3⟩ := hall_matching_onto
    (fun u s => isCoveredByWindow e p (u : Int) (lag u) s)
    (LagElevenPeriodic.subPhases e 0 p) (subPhases_nodup e p) B hBnodup hhallB htight'
  refine ⟨m, ?_, h2, ?_⟩
  · intro b hb
    rw [neighborhood_eq_cover]
    exact h1 b hb
  · intro s hs
    rw [neighborhood_eq_cover] at hs
    exact h3 s hs

end Recaman.HallMatching
