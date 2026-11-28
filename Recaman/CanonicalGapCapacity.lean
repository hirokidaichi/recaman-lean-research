import Recaman.OrbitBounds
import Recaman.History

namespace Recaman.CanonicalGapCapacity

open Recaman

/-! # Spatial gap capacity and walk-length bounds for the canonical Recamán orbit

For every canonical clock `b : Nat`, the visited set `valuesThrough b` is traced by
steps of sizes `1, 2, ..., b` starting from `a 0 = 0`.  Consequently:

1. Walk-length peak bound: `2 * a t ≤ a b + upperTri b` for all `t ≤ b`.
2. Prefix trapping across any empty band `(lo, hi)` in `valuesThrough b`:
   every step `t < hi - lo` satisfies `a t ≤ lo`.
3. Distinct tail cardinality above any empty band `(lo, hi)`:
   at most `b + 1 - (hi - lo)` distinct elements of `valuesThrough b` lie at or above `hi`.
   In particular, no empty band in `valuesThrough b` of width `> b` has any visited value
   at or above `hi`.
4. Tail peak bound above an empty band `(lo, hi)`:
   for any `t ≤ b` with `hi ≤ a t`,
   `2 * a t + upperTri (hi - lo - 1) ≤ a b + lo + upperTri b`.
5. Descending gap-rank capacity:
   any strictly ordered sequence of `m` empty bands of width `> θ` whose upper endpoints
   belong to `valuesThrough b` has length `m ≤ b - θ`.
-/

/-- Helper: every step changes `a` by at most its clock, bounding downward drift. -/
theorem a_add_upperTri_mono {s b : Nat} (hsb : s ≤ b) :
    a s + upperTri s ≤ a b + upperTri b := by
  induction b with
  | zero =>
      have hs0 : s = 0 := by omega
      subst hs0
      exact Nat.le_refl _
  | succ b ih =>
      rcases Nat.eq_or_lt_of_le hsb with rfl | hlt
      · exact Nat.le_refl _
      · have ih' := ih (Nat.le_of_lt_succ hlt)
        have hrec := recurrence b
        rw [upperTri]
        split at hrec <;> omega

/-- Helper: every step increases `a` by at most its clock, bounding upward drift. -/
theorem a_le_a_add_upperTri_diff {s b : Nat} (hsb : s ≤ b) :
    a b + upperTri s ≤ a s + upperTri b := by
  induction b with
  | zero =>
      have hs0 : s = 0 := by omega
      subst hs0
      exact Nat.le_refl _
  | succ b ih =>
      rcases Nat.eq_or_lt_of_le hsb with rfl | hlt
      · exact Nat.le_refl _
      · have ih' := ih (Nat.le_of_lt_succ hlt)
        have hrec := recurrence b
        rw [upperTri]
        split at hrec <;> omega

/-- Walk-length peak bound: any value visited by clock `b` obeys
`2 * a t ≤ a b + upperTri b`. Sharp at `b = 1, 2, 3, 4`. -/
theorem walk_peak_le_upperTri (b t : Nat) (htb : t ≤ b) :
    2 * a t ≤ a b + upperTri b := by
  have h1 := a_le_upperTri t
  have h2 := a_add_upperTri_mono htb
  omega

/-- Prefix trapping: if `(lo, hi)` contains no visited value up to clock `b`,
then every clock `t < hi - lo` (with `t ≤ b`) stays at or below `lo`. -/
theorem empty_gap_prefix_trapped (b lo hi : Nat)
    (hempty : ∀ v ∈ valuesThrough b, v ≤ lo ∨ hi ≤ v) :
    ∀ t, t ≤ b → t < hi - lo → a t ≤ lo := by
  intro t
  induction t with
  | zero =>
      intro _ _
      simp [a, stateAt, initial]
  | succ t ih =>
      intro ht1b ht1g
      have hprev : a t ≤ lo := ih (by omega) (by omega)
      have hrec := recurrence t
      have hstep_le : a (t + 1) ≤ a t + (t + 1) := by
        split at hrec <;> omega
      have hmem : a (t + 1) ∈ valuesThrough b :=
        mem_valuesThrough_iff.mpr ⟨t + 1, ht1b, rfl⟩
      rcases hempty (a (t + 1)) hmem with hle | hge
      · exact hle
      · omega

/-- Necessity of the adjacent-gap-`≤ b` spatial filter: if an empty band `(lo, hi)`
in `valuesThrough b` has width `> b`, then every visited value up to `b` is `≤ lo`. -/
theorem no_empty_gap_gt_clock (b lo hi : Nat)
    (hempty : ∀ v ∈ valuesThrough b, v ≤ lo ∨ hi ≤ v)
    (hgap : b < hi - lo) :
    ∀ v ∈ valuesThrough b, v ≤ lo := by
  intro v hv
  rcases mem_valuesThrough_iff.mp hv with ⟨t, htb, rfl⟩
  exact empty_gap_prefix_trapped b lo hi hempty t htb (by omega)

/-- Tail peak bound above an empty band `(lo, hi)`: any visited value `a t ≥ hi`
obeys `2 * a t + upperTri (hi - lo - 1) ≤ a b + lo + upperTri b`. -/
theorem empty_gap_tail_peak_le (b lo hi t : Nat) (htb : t ≤ b)
    (hgt : lo < hi) (hhi : hi ≤ a t)
    (hempty : ∀ v ∈ valuesThrough b, v ≤ lo ∨ hi ≤ v) :
    2 * a t + upperTri (hi - lo - 1) ≤ a b + lo + upperTri b := by
  have htge : hi - lo ≤ t := by
    apply Classical.byContradiction
    intro hlt
    have htrap := empty_gap_prefix_trapped b lo hi hempty t htb (by omega)
    omega
  have hanchor : a (hi - lo - 1) ≤ lo :=
    empty_gap_prefix_trapped b lo hi hempty (hi - lo - 1) (by omega) (by omega)
  have hup := a_le_a_add_upperTri_diff (s := hi - lo - 1) (b := t) (by omega)
  have hdn := a_add_upperTri_mono htb
  omega

/-- Auxiliary: if a `Nodup` list `L` is contained in a list `M`, then `L.length ≤ M.length`. -/
private theorem nodup_length_le_of_subset :
    ∀ {L M : List Nat}, L.Nodup → (∀ x ∈ L, x ∈ M) → L.length ≤ M.length
  | [], _, _, _ => Nat.zero_le _
  | x :: xs, M, hnd, hsub => by
      have hxM : x ∈ M := hsub x (List.mem_cons_self ..)
      have hnd' := List.nodup_cons.mp hnd
      have hxnot : x ∉ xs := hnd'.1
      have hxsnd : xs.Nodup := hnd'.2
      have hsub' : ∀ y ∈ xs, y ∈ M.erase x := by
        intro y hy
        have hyx : y ≠ x := fun heq => hxnot (heq ▸ hy)
        exact (List.mem_erase_of_ne hyx).mpr (hsub y (List.mem_cons_of_mem x hy))
      have ih := nodup_length_le_of_subset hxsnd hsub'
      have herase : (M.erase x).length + 1 = M.length := by
        have hlen := List.length_erase_of_mem hxM
        have hpos : 0 < M.length := List.length_pos_of_mem hxM
        omega
      simp only [List.length_cons]
      omega

/-- Distinct tail cardinality above an empty band `(lo, hi)`: any duplicate-free list `L`
of visited values in `valuesThrough b` all `≥ hi` has length `≤ b + 1 - (hi - lo)`. -/
theorem empty_gap_distinct_tail_count_le (b lo hi : Nat) (L : List Nat)
    (hgt : lo < hi)
    (hempty : ∀ v ∈ valuesThrough b, v ≤ lo ∨ hi ≤ v)
    (hnd : L.Nodup)
    (hsub : ∀ v ∈ L, v ∈ valuesThrough b ∧ hi ≤ v) :
    L.length ≤ b + 1 - (hi - lo) := by
  let g := hi - lo
  let M := (List.range (b + 1 - g)).map (fun i => a (g + i))
  have hMsub : ∀ v ∈ L, v ∈ M := by
    intro v hv
    obtain ⟨hvmem, hvhi⟩ := hsub v hv
    obtain ⟨t, htb, rfl⟩ := mem_valuesThrough_iff.mp hvmem
    have htge : g ≤ t := by
      apply Classical.byContradiction
      intro hlt
      have htrap := empty_gap_prefix_trapped b lo hi hempty t htb (by omega)
      omega
    refine List.mem_map.mpr ⟨t - g, ?_, ?_⟩
    · exact List.mem_range.mpr (by omega)
    · congr 1; omega
  have hle := nodup_length_le_of_subset hnd hMsub
  simpa [M] using hle

/-- Strictly separated list of gap intervals: each `(lo, hi)` satisfies `lo < hi` and
each `hi` is at most every later `lo`. -/
def GapChain : List (Nat × Nat) → Prop
  | [] => True
  | p :: ps => p.1 < p.2 ∧ (∀ q ∈ ps, p.2 ≤ q.1) ∧ GapChain ps

private theorem gapChain_snd_nodup :
    ∀ {gaps : List (Nat × Nat)}, GapChain gaps → (gaps.map Prod.snd).Nodup
  | [], _ => List.nodup_nil
  | p :: ps, ⟨hlt, hsep, hrest⟩ => by
      refine List.nodup_cons.mpr ⟨?_, gapChain_snd_nodup hrest⟩
      intro hmem
      obtain ⟨q, hq, hqp⟩ := List.mem_map.mp hmem
      have h1 := hsep q hq
      have h2 : q.1 < q.2 := by
        clear hmem hqp h1 hlt hsep
        induction ps with
        | nil => cases hq
        | cons r rs ih =>
            rcases List.mem_cons.mp hq with rfl | hq'
            · exact hrest.1
            · exact ih hrest.2.2 hq'
      omega

/-- Descending gap-rank capacity: any ordered chain of `m` empty bands of width `> θ`
whose upper endpoints occur in `valuesThrough b` satisfies `m ≤ b - θ`. -/
theorem multi_gap_rank_bound (b θ : Nat) (gaps : List (Nat × Nat))
    (hchain : GapChain gaps)
    (hwidth : ∀ p ∈ gaps, θ < p.2 - p.1)
    (hempty : ∀ p ∈ gaps, ∀ v ∈ valuesThrough b, v ≤ p.1 ∨ p.2 ≤ v)
    (hvis : ∀ p ∈ gaps, p.2 ∈ valuesThrough b) :
    gaps.length ≤ b - θ := by
  cases gaps with
  | nil => exact Nat.zero_le _
  | cons p ps =>
      have hp_lt : p.1 < p.2 := hchain.1
      have hp_sep : ∀ q ∈ ps, p.2 ≤ q.1 := hchain.2.1
      have hp_w : θ < p.2 - p.1 := hwidth p (List.mem_cons_self ..)
      have hp_emp := hempty p (List.mem_cons_self ..)
      have hnd := gapChain_snd_nodup hchain
      have hsub : ∀ v ∈ (p :: ps).map Prod.snd, v ∈ valuesThrough b ∧ p.2 ≤ v := by
        intro v hv
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hv
        refine ⟨hvis q hq, ?_⟩
        rcases List.mem_cons.mp hq with rfl | hq'
        · exact Nat.le_refl _
        · have h1 := hp_sep q hq'
          have h2 := hwidth q (List.mem_cons_of_mem p hq')
          omega
      have hcard := empty_gap_distinct_tail_count_le b p.1 p.2 ((p :: ps).map Prod.snd)
        hp_lt hp_emp hnd hsub
      simp only [List.length_map] at hcard
      omega

end Recaman.CanonicalGapCapacity
