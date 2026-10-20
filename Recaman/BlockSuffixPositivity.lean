import Recaman.SingleWindowEquality
import Recaman.CapacityEqualityInduction

namespace Recaman.BlockSuffixPositivity

open Recaman.LeadingRunSupply
open Recaman.LineCapacityPeriodic
open Recaman.CapacityEqualityInduction
open Recaman.SingleWindowEquality
open Recaman.ShortPeriodicSupply (sign)

/-! # Suffixes of padded block words have positive rise and area

`areaW w` is the area of the oldest-first word `w` above its start level:
the sum of the masses of its nonempty prefixes. -/

def areaW : List Bool → Int
  | [] => 0
  | x :: w => sign x * ((w.length : Int) + 1) + areaW w

theorem areaW_append (u v : List Bool) :
    areaW (u ++ v) = areaW u + (v.length : Int) * mass u + areaW v := by
  induction u with
  | nil => simp [areaW]
  | cons x u ih =>
    show sign x * (((u ++ v).length : Int) + 1) + areaW (u ++ v) = _
    rw [ih, List.length_append]
    show _ = sign x * ((u.length : Int) + 1) + areaW u + _ + _
    rw [mass_cons]
    cases x <;> simp [sign] <;> grind

theorem areaW_single (x : Bool) : areaW [x] = sign x := by
  simp [areaW]

theorem mass_rep_false (j : Nat) : mass (List.replicate j false) = -(j : Int) := by
  induction j with
  | zero => rfl
  | succ j ih => rw [List.replicate_succ, mass_cons, ih]; simp [sign]; omega

/-- Every nonempty suffix has mass `≥ 1` and area `≥ 1`. -/
def SufPos (l : List Bool) : Prop :=
  ∀ u v : List Bool, u ++ v = l → v ≠ [] → 1 ≤ mass v ∧ 1 ≤ areaW v

theorem sufPos_nil : SufPos [] := by
  intro u v h hv
  exact absurd (List.append_eq_nil_iff.mp h).2 hv

theorem sufPos_of_drops (B : List Bool)
    (h : ∀ k, k < B.length → 1 ≤ mass (B.drop k) ∧ 1 ≤ areaW (B.drop k)) : SufPos B := by
  intro u v huv hv
  have hvd : v = B.drop u.length := by rw [← huv, List.drop_left]
  have hlen : u.length < B.length := by
    rw [← huv, List.length_append]
    have : v.length ≠ 0 := fun h0 => hv (List.length_eq_zero_iff.mp h0)
    omega
  rw [hvd]; exact h _ hlen

theorem sufPos_free : SufPos [true] := sufPos_of_drops _ (by decide)
theorem sufPos_aas : SufPos [false, true, true, true] := sufPos_of_drops _ (by decide)
theorem sufPos_triple :
    SufPos [false, false, true, true, true, true, false, true, true, true] :=
  sufPos_of_drops _ (by decide)

theorem sufPos_append (w B : List Bool) (hw : SufPos w) (hB : SufPos B) (hBne : B ≠ [])
    (hBa : 0 ≤ areaW B) : SufPos (w ++ B) := by
  intro u v h hv
  have hBm := (hB [] B rfl hBne).1
  rcases List.append_eq_append_iff.mp h with ⟨a', h1, h2⟩ | ⟨c', _, h2⟩
  · subst h2
    by_cases ha : a' = []
    · subst ha; exact hB [] B rfl hBne
    · obtain ⟨m1, a1⟩ := hw u a' h1.symm ha
      have hnn : 0 ≤ (B.length : Int) * mass a' :=
        Int.mul_nonneg (Int.natCast_nonneg _) (by omega)
      rw [mass_append, areaW_append]
      omega
  · exact hB c' v h2.symm hv

theorem sufPos_block {w : List Bool} (h : BlockWord w) : SufPos w := by
  induction h with
  | nil => exact sufPos_nil
  | free _ ih => exact sufPos_append _ _ ih sufPos_free (by simp) (by decide)
  | aas _ ih => exact sufPos_append _ _ ih sufPos_aas (by simp) (by decide)
  | triple _ ih => exact sufPos_append _ _ ih sufPos_triple (by simp) (by decide)

/-- **Lemma 1 (word form).** Every nonempty suffix of `β ++ A^a`, `β` a block
word, has mass `≥ 1` and area `≥ 1`. -/
theorem block_suffix_positive {β : List Bool} (hβ : BlockWord β) :
    ∀ a : Nat, SufPos (β ++ List.replicate a true)
  | 0 => by rw [List.replicate_zero, List.append_nil]; exact sufPos_block hβ
  | a+1 => by
      rw [List.replicate_succ', ← List.append_assoc]
      exact sufPos_append _ _ (block_suffix_positive hβ a) sufPos_free (by simp) (by decide)

/-! ## Walk form -/

theorem Ar_areaW (f : Nat → Bool) (t : Nat) : ∀ k : Nat, Ar f t k = areaW (seg f t k)
  | 0 => by simp [Ar, seg, areaW]
  | k+1 => by
      rw [Ar_succ, seg_succ, areaW_append, areaW_single, ← Ar_areaW f t k, seg_mass,
        show t + k + 1 = (t + k) + 1 from rfl, Fw_succ]
      simp
      omega

theorem seg_false (f : Nat → Bool) (s : Nat) :
    ∀ j : Nat, (∀ i, s ≤ i → i < s + j → f i = false) → seg f s j = List.replicate j false
  | 0, _ => by simp [seg]
  | j+1, h => by
      rw [seg_succ, seg_false f s j (fun i h1 h2 => h i h1 (by omega)), h (s+j) (by omega) (by omega),
        List.replicate_succ']

theorem suffix_split (f : Nat → Bool) (s n t : Nat) (h1 : s ≤ t) (h2 : t ≤ s + n) :
    seg f s n = seg f s (t - s) ++ seg f t (s + n - t) := by
  have := seg_add f s (t - s) (s + n - t)
  rw [show t - s + (s + n - t) = n by omega, show s + (t - s) = t by omega] at this
  exact this

/-- **Lemma 1 (walk form).** If the clocks `[s, s+n)` read `β ++ A^a` with `β`
a block word, then for every `t ∈ [s, s+n)`:
`Fw(s+n) - Fw(t) ≥ 1` and the area `Ar t (s+n-t) ≥ 1`. -/
theorem block_suffix_positive_walk (f : Nat → Bool) (s n a : Nat) {β : List Bool}
    (hβ : BlockWord β) (hseg : seg f s n = β ++ List.replicate a true)
    (t : Nat) (h1 : s ≤ t) (h2 : t < s + n) :
    1 ≤ Fw f (s + n) - Fw f t ∧ 1 ≤ Ar f t (s + n - t) := by
  have hsp := suffix_split f s n t h1 (by omega)
  rw [hseg] at hsp
  have hne : seg f t (s + n - t) ≠ [] := by
    intro h0
    have := seg_length f t (s + n - t)
    rw [h0] at this; simp at this; omega
  obtain ⟨hm, ha⟩ := block_suffix_positive hβ a _ _ hsp.symm hne
  rw [seg_mass, show t + (s + n - t) = s + n by omega] at hm
  rw [Ar_areaW]
  exact ⟨hm, ha⟩

/-! ## Lemma 1': no P2 window after an S-run -/

theorem fw_false_run (f : Nat → Bool) (t : Nat) :
    ∀ k : Nat, (∀ i, t ≤ i → i < t + k → f i = false) → Fw f (t + k) = Fw f t - k
  | 0, _ => by simp
  | k+1, h => by
      have ih := fw_false_run f t k (fun i h1 h2 => h i h1 (by omega))
      rw [show t + (k+1) = (t + k) + 1 from rfl, Fw_succ, ih, h (t+k) (by omega) (by omega)]
      simp [sign]; omega

theorem area_after_false (j : Nat) : ∀ v : List Bool, 1 ≤ areaW v → (j : Int) + 1 ≤ mass v →
    1 ≤ areaW (v ++ List.replicate j false) := by
  induction j with
  | zero => intro v h _; simpa using h
  | succ j ih =>
    intro v ha hm
    rw [List.replicate_succ, ← List.singleton_append, ← List.append_assoc]
    apply ih
    · rw [areaW_append, areaW_single]; simp [sign]; omega
    · rw [mass_append]; simp [sign]; omega

/-- **Lemma 1'.** If `[s, s+n)` reads `β ++ A^a` (`β` a block word), the clocks
`[s+n, s+n+j)` are all subtractions, then no P2 window starting at or after `s`
ends at `s+n+j`. -/
theorem no_window_after_S_run (f : Nat → Bool) (s n a j : Nat) {β : List Bool}
    (hβ : BlockWord β) (hseg : seg f s n = β ++ List.replicate a true)
    (hS : ∀ i, s + n ≤ i → i < s + n + j → f i = false) :
    ¬ EndN f s (s + n + j) := by
  rintro ⟨_, t, k, hst, htk, hk0, hF, hAr⟩
  by_cases ht : s + n ≤ t
  · have := fw_false_run f t k (fun i h1 h2 => hS i (by omega) (by omega))
    omega
  · have hsp := suffix_split f s n t hst (by omega)
    rw [hseg] at hsp
    have hne : seg f t (s + n - t) ≠ [] := by
      intro h0
      have := seg_length f t (s + n - t)
      rw [h0] at this; simp at this; omega
    obtain ⟨hm, ha⟩ := block_suffix_positive hβ a _ _ hsp.symm hne
    have hk : k = (s + n - t) + j := by omega
    have hsk : seg f t k = seg f t (s + n - t) ++ List.replicate j false := by
      rw [hk, seg_add, show t + (s + n - t) = s + n by omega,
        seg_false f (s + n) j hS]
    have hmass : mass (seg f t k) = 1 := by
      rw [seg_mass]; omega
    rw [hsk, mass_append, mass_rep_false] at hmass
    have hpos := area_after_false j _ ha (by omega)
    rw [← hsk, ← Ar_areaW] at hpos
    omega

/-- Lemma 1' on integer clocks: `[p, p+n)` reads `β ++ A^a`, `[p+n, p+n+j)` is
an S-run; then `p+n+j` is not endable from `p`. -/
theorem no_endable_after_S_run (e : Int → Bool) (p : Int) (n a j : Nat) {β : List Bool}
    (hβ : BlockWord β) (hseg : segment e p n = β ++ List.replicate a true)
    (hS : ∀ i : Nat, i < j → e (p + ((n + i : Nat) : Int)) = false) :
    ¬ Endable e p (p + ((n + j : Nat) : Int)) := by
  have hp0 : p = p + ((0 : Nat) : Int) := by simp
  rw [endable_iff e p p _ 0 (n + j) hp0 rfl]
  rw [segment_seg e p p 0 hp0] at hseg
  have := no_window_after_S_run (fun i => e (p + (i : Int))) 0 n a j hβ hseg
    (fun i h1 h2 => by
      have := hS (i - n) (by omega)
      rwa [show n + (i - n) = i by omega] at this)
  rwa [Nat.zero_add] at this

/-! ## TS1: an endable clock after an S-run forces strict slack -/

/-- **TS1.** Assume line capacity on `[p, p+m)` and the equality-class property
for every `m ≤ n`. If `[p+n, p+n+j)` is an S-run and `p+n+j` is endable from
`p`, then `[p, p+n)` has strictly more subtractions than endable clocks. -/
theorem ts_one (e : Int → Bool) (p : Int) (n j : Nat)
    (hH : ∀ m, m ≤ n → HCap e p m) (hE : ∀ m, m ≤ n → EqClassW e p m)
    (hS : ∀ i : Nat, i < j → e (p + ((n + i : Nat) : Int)) = false)
    (hb : Endable e p (p + ((n + j : Nat) : Int))) :
    endableCount e p n + 1 ≤ subtractionCount e p n := by
  apply Classical.byContradiction
  intro hneg
  have hle : subtractionCount e p n ≤ endableCount e p n := by omega
  obtain ⟨m', hm'le, hm'mark, hm'none⟩ := last_mark (Endable e p) p n
  have hEq : endableCount e p n = endableCount e p m' := by
    have h := @countP_add (Endable e p) (classDec _) p m' (n - m')
    rw [Nat.add_sub_cancel' hm'le] at h
    have h0 : @countP (Endable e p) (classDec _) (p + m') (n - m') = 0 := by
      apply @countP_eq_zero_of (Endable e p) (classDec _)
      intro i hi
      have := hm'none (m' + i) (by omega) (by omega)
      rwa [show p + ((m' + i : Nat) : Int) = p + (m' : Int) + (i : Int) by omega] at this
    show @countP (Endable e p) (classDec _) p n = @countP (Endable e p) (classDec _) p m'
    rw [h, h0, Nat.add_zero]
  have hSadd : subtractionCount e p n =
      subtractionCount e p m' + subtractionCount e (p + m') (n - m') := by
    have h := countP_add (fun c => e c = false) p m' (n - m')
    rw [Nat.add_sub_cancel' hm'le] at h
    exact h
  have hHm' : endableCount e p m' ≤ subtractionCount e p m' := hH m' hm'le
  have htail0 : subtractionCount e (p + m') (n - m') = 0 := by omega
  have hall := not_of_countP_eq_zero _ (p + m') (n - m') htail0
  have hseg : segment e p n = segment e p m' ++ List.replicate (n - m') true := by
    rw [← segment_true e (p + m') (n - m') (fun i hi => by
      have := hall i hi
      cases h : e (p + (m' : Int) + (i : Int))
      · exact absurd h this
      · rfl)]
    rw [← segment_add, Nat.add_sub_cancel' hm'le]
  have hBW : BlockWord (segment e p m') := by
    by_cases h0 : m' = 0
    · subst h0; exact BlockWord.nil
    · rcases hm'mark with h0' | hmk
      · exact absurd h0' h0
      · exact hE m' hm'le (by omega) (by omega) hmk
  exact no_endable_after_S_run e p n (n - m') j hBW hseg hS hb

end Recaman.BlockSuffixPositivity
