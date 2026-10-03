import Recaman.LeadingRunSupply

namespace Recaman.SuffixHallOwnerMap

/-! Suffix Hall for owner maps on the line, for every lag.

A finite closed configuration (matching closure) of the line model (E-356/E-357, H-20261003-01) consists of members `b`
(additions) with windows `[b - lag b, b - 1]` and an owner map `own` sending each member to a
subtraction of its own window, injectively (M1, M1'); M2 says every subtraction inside a member
window is owned. Here only these properties are used, no P2 condition and no lag bound.

`suffix_hall`: if every subtraction clock in `[z, z+n-1]` is owned, the number of these subtractions
is at most the number of members after `z` (each owner lies strictly after the subtraction it owns;
in a finite component whose newest member is `z + n` these are the members in `(z, z+n]`).

`suffix_mass_ge`: if moreover the members are additions, the suffix `[z, z+n-1]` has sign sum at
least `-1`. For a finite closed component `J = [x, y]` (newest member `y + 1`), with
`F t = Σ_{c < t} sign (e c)`, this says `F z ≤ F (y+1) + 1` for every `z ∈ [x, y]`: the walk maximum of
the component exceeds the value at the newest member by at most one.
-/

open ShortPeriodicSupply (sign)

/-- The clocks `z, z+1, ..., z+n-1`. -/
def clocks (z : Int) (n : Nat) : List Int := (List.range n).map fun (i : Nat) => z + (i : Int)

theorem mem_clocks (z c : Int) (n : Nat) : c ∈ clocks z n ↔ z ≤ c ∧ c < z + n := by
  constructor
  · intro h
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp h
    have := List.mem_range.mp hi
    omega
  · rintro ⟨h1, h2⟩
    refine List.mem_map.mpr ⟨(c - z).toNat, List.mem_range.mpr (by omega), by omega⟩

theorem nodup_map_of_inj {α β : Type} (l : List α) (f : α → β) (hl : l.Nodup)
    (hf : ∀ a ∈ l, ∀ b ∈ l, f a = f b → a = b) : (l.map f).Nodup := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.nodup_cons] at hl
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, ih hl.2 (fun x hx y hy hxy => hf x (by simp [hx]) y (by simp [hy]) hxy)⟩
    intro hmem
    obtain ⟨b, hb, hfb⟩ := List.mem_map.mp hmem
    have := hf b (by simp [hb]) a (by simp) hfb
    exact hl.1 (this ▸ hb)

theorem clocks_nodup (z : Int) (n : Nat) : (clocks z n).Nodup :=
  nodup_map_of_inj _ _ List.nodup_range (by intro a _ b _ h; omega)

/-- The owner-map half of a closed configuration (M1 and M1'), for members listed in `M`. -/
structure OwnerMap (e : Int → Bool) (M : List Int) (lag : Int → Nat) (own : Int → Int) : Prop where
  nodup : M.Nodup
  own_lt : ∀ b ∈ M, own b < b
  own_ge : ∀ b ∈ M, b - (lag b : Int) ≤ own b
  own_S : ∀ b ∈ M, e (own b) = false
  inj : ∀ b ∈ M, ∀ b' ∈ M, own b = own b' → b = b'

/-- Suffix Hall: owned subtractions of a suffix are at most the members after its start. -/
theorem suffix_hall (e : Int → Bool) (M : List Int) (lag : Int → Nat) (own : Int → Int)
    (hO : OwnerMap e M lag own) (z : Int) (n : Nat)
    (hcov : ∀ c, z ≤ c → c < z + n → e c = false → ∃ b ∈ M, own b = c) :
    ((clocks z n).filter (fun c => !e c)).length ≤ (M.filter (fun b => decide (z < b))).length := by
  let Ss := (clocks z n).filter (fun c => !e c)
  let ownerOf : Int → Int := fun c => (M.find? (fun b => own b == c)).getD 0
  have howner : ∀ c ∈ Ss, ownerOf c ∈ M ∧ own (ownerOf c) = c := by
    intro c hc
    have hc' := List.mem_filter.mp hc
    have hrange := (mem_clocks z c n).1 hc'.1
    have hS : e c = false := by simpa using hc'.2
    obtain ⟨b, hb, hob⟩ := hcov c hrange.1 hrange.2 hS
    have hsome : (M.find? (fun b => own b == c)).isSome = true :=
      List.find?_isSome.mpr ⟨b, hb, by simp [hob]⟩
    obtain ⟨b', hb'⟩ := Option.isSome_iff_exists.mp hsome
    have hm := List.mem_of_find?_eq_some hb'
    have hp := List.find?_some hb'
    simp only [ownerOf, hb', Option.getD_some]
    exact ⟨hm, by simpa using hp⟩
  have hnodup : (Ss.map ownerOf).Nodup := by
    apply nodup_map_of_inj _ _ ((clocks_nodup z n).filter _)
    intro a ha b hb hab
    rw [← (howner a ha).2, ← (howner b hb).2, hab]
  have hsub : Ss.map ownerOf ⊆ M.filter (fun b => decide (z < b)) := by
    intro x hx
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
    obtain ⟨hm, ho⟩ := howner c hc
    have hc' := List.mem_filter.mp hc
    have hrange := (mem_clocks z c n).1 hc'.1
    have hlt := hO.own_lt _ hm
    apply List.mem_filter.mpr
    refine ⟨hm, ?_⟩
    simp only [decide_eq_true_eq]
    omega
  have := hnodup.length_le_of_subset hsub
  simpa [Ss] using this

/-- Sign sum of a list of clocks = #additions − #subtractions. -/
theorem sign_sum_eq (e : Int → Bool) (l : List Int) :
    (l.map fun c => sign (e c)).sum =
      ((l.filter fun c => e c).length : Int) - (l.filter fun c => !e c).length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons, ih]
    cases h : e a <;> simp [h, ShortPeriodicSupply.sign] <;> omega

theorem clocks_succ_left (z : Int) (n : Nat) : clocks z (n+1) = z :: clocks (z+1) n := by
  apply List.ext_getElem
  · simp [clocks]
  · intro i h1 h2
    cases i with
    | zero => simp [clocks]
    | succ i => simp [clocks]; omega

theorem clocks_succ_right (z : Int) (n : Nat) : clocks z (n+1) = clocks z n ++ [z + n] := by
  simp [clocks, List.range_succ]

/-- Every suffix of a finite closed component has sign sum at least `-1`. Hypotheses: owner map
(M1, M1'), every subtraction of `[z, z+n-1]` owned (M2 on a component), members are additions and
lie at or before `z + n`. -/
theorem suffix_mass_ge (e : Int → Bool) (M : List Int) (lag : Int → Nat) (own : Int → Int)
    (hO : OwnerMap e M lag own) (hA : ∀ b ∈ M, e b = true) (z : Int) (n : Nat)
    (hcov : ∀ c, z ≤ c → c < z + n → e c = false → ∃ b ∈ M, own b = c)
    (hM : ∀ b ∈ M, b ≤ z + n) :
    -1 ≤ ((clocks z n).map fun c => sign (e c)).sum := by
  have hhall := suffix_hall e M lag own hO z n hcov
  -- members after z are additions in [z+1, z+n]
  have hmem : (M.filter (fun b => decide (z < b))).length ≤
      ((clocks (z+1) n).filter fun c => e c).length := by
    apply List.Nodup.length_le_of_subset (hO.nodup.filter (fun b => decide (z < b)))
    intro b hb
    have hb' := List.mem_filter.mp hb
    have hz : z < b := by simpa using hb'.2
    apply List.mem_filter.mpr
    refine ⟨(mem_clocks (z+1) b n).2 ⟨by omega, by have := hM b hb'.1; omega⟩, by simp [hA b hb'.1]⟩
  rw [sign_sum_eq]
  -- #A[z, z+n-1] ≥ #A[z+1, z+n] - 1
  cases n with
  | zero => simp [clocks]
  | succ n =>
    have hL := clocks_succ_left z n
    have hR := clocks_succ_right (z+1) n
    have hA1 : ((clocks z (n+1)).filter fun c => e c).length + 1 ≥
        ((clocks (z+1) (n+1)).filter fun c => e c).length := by
      rw [hL, hR]
      simp only [List.filter_cons, List.filter_append, List.length_append]
      split <;> (cases e (z + 1 + (n : Int)) <;> simp) <;> omega
    omega

end Recaman.SuffixHallOwnerMap
