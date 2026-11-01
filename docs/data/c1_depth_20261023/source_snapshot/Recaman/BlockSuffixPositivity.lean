import Recaman.SingleWindowEquality
import Recaman.CapacityEqualityInduction
import Recaman.ThreeNonsuppliedData
import Recaman.ThreeNonsuppliedQData

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

/-! ## Low clocks after a padded block prefix

The lower bound `m` need not be attained. This is the running-minimum
exclusion used in the C1 area argument; it does not prove that argument's
remaining area inequality. -/

theorem area_nondecreasing_tail (f : Nat → Bool) (t n : Nat) : ∀ j : Nat,
    (∀ i, n < i → i ≤ n + j → Fw f t ≤ Fw f (t + i)) →
    Ar f t n ≤ Ar f t (n + j)
  | 0, _ => by simp
  | j+1, h => by
      have ih := area_nondecreasing_tail f t n j (fun i hi hle => h i hi (by omega))
      have hlast := h (n + j + 1) (by omega) (by omega)
      rw [show n + (j + 1) = n + j + 1 from rfl, Ar_succ]
      have heq : t + (n + j) + 1 = t + (n + j + 1) := by omega
      rw [heq]
      omega

/-- A supplied clock after a padded block prefix is at least two levels above
every lower bound on the intervening walk. The prefix and the tail are both
about the same sign string; no capacity or equality conjecture is assumed. -/
theorem block_prefix_low_clock_not_endable (f : Nat → Bool) (n a b : Nat)
    {β : List Bool} (hβ : BlockWord β)
    (hseg : seg f 0 n = β ++ List.replicate a true)
    (hnb : n ≤ b) (m : Int)
    (hmin : ∀ u, n ≤ u → u ≤ b → m ≤ Fw f u)
    (hlow : Fw f b ≤ m + 1) : ¬ EndN f 0 b := by
  rintro ⟨_, t, k, _, htk, hk, hF, hAr⟩
  rw [htk] at hF
  have htm : Fw f t ≤ m := by omega
  by_cases htn : t < n
  · obtain ⟨_, hpos⟩ := block_suffix_positive_walk f 0 n a hβ hseg t
      (Nat.zero_le t) (by omega)
    simp only [Nat.zero_add] at hpos
    have hnk : n - t ≤ k := by omega
    have hext := area_nondecreasing_tail f t (n - t) (k - (n - t)) (by
      intro i hi hle
      have hlo := hmin (t + i) (by omega) (by omega)
      omega)
    rw [show n - t + (k - (n - t)) = k by omega] at hext
    omega
  · have hbase := hmin t (by omega) (by omega)
    have hge := area_ge f t k (by
      intro i hi hle
      have hlo := hmin (t + i) (by omega) (by omega)
      omega)
    rw [htk] at hge
    omega

theorem two_marks_le_count (P : Nat → Prop) (s u v : Nat) : ∀ j : Nat,
    s ≤ u → u < v → v < s + j → P u → P v → 2 ≤ cN P s j
  | 0, hsu, huv, hv, _, _ => by omega
  | j+1, hsu, huv, hv, hpu, hpv => by
      classical
      by_cases hvj : v < s + j
      · have ih := two_marks_le_count P s u v j hsu huv hvj hpu hpv
        by_cases hp : P (s+j)
        · rw [cN_succ_pos P s j hp]; omega
        · rw [cN_succ_neg P s j hp]; exact ih
      · have hveq : v = s + j := by omega
        have hpos : 1 ≤ cN P s j := by
          apply Classical.byContradiction
          intro h
          have hz : cN P s j = 0 := by omega
          exact not_of_cN_zero P s j hz u hsu (by omega) hpu
        have hp : P (s+j) := by simpa [hveq] using hpv
        rw [cN_succ_pos P s j hp]
        omega

/-- Recovering two levels from a low visit forces two distinct nonsupplied A
clocks after that visit. Both are nonsupplied with respect to the original
left endpoint, rather than a rebased interval. -/
theorem two_nonsupplied_additions_of_recovery (f : Nat → Bool) (n a r b : Nat)
    {β : List Bool} (hβ : BlockWord β)
    (hseg : seg f 0 n = β ++ List.replicate a true)
    (hnr : n ≤ r) (hrb : r ≤ b) (m : Int) (hr : Fw f r = m)
    (hmin : ∀ u, n ≤ u → u ≤ b → m ≤ Fw f u)
    (hhigh : m + 2 ≤ Fw f b) :
    ∃ u v, r ≤ u ∧ u < v ∧ v < b ∧
      Fw f u = m ∧ Fw f v = m + 1 ∧
      f u = true ∧ ¬ EndN f 0 u ∧ f v = true ∧ ¬ EndN f 0 v := by
  obtain ⟨v, hrv, hvb, hv, hvA⟩ := ivt f b (m+2) hhigh (b-r) r (by omega) (by omega)
  obtain ⟨u, hru, huv, hu, huA⟩ := ivt f v (m+1) (by omega) (v-r) r (by omega) (by omega)
  have hnu := block_prefix_low_clock_not_endable f n a u hβ hseg (by omega) m
    (fun i hni hiu => hmin i hni (by omega)) (by omega)
  have hnv := block_prefix_low_clock_not_endable f n a v hβ hseg (by omega) m
    (fun i hni hiv => hmin i hni (by omega)) (by omega)
  exact ⟨u, v, hru, huv, hvb, by omega, by omega, huA, hnu, hvA, hnv⟩

theorem shifted_area_nonneg (f : Nat → Bool) (t : Nat) (level : Int) : ∀ k : Nat,
    (∀ i, 1 ≤ i → i ≤ k → level - 1 ≤ Fw f (t+i)) →
    0 ≤ Ar f t k + (k : Int) * (Fw f t - level + 1)
  | 0, _ => by simp [Ar]
  | k+1, h => by
      have ih := shifted_area_nonneg f t level k (fun i hi hle => h i hi (by omega))
      have hlast := h (k+1) (by omega) (by omega)
      rw [Ar_succ]
      push_cast
      have heq : t + k + 1 = t + (k+1) := by omega
      rw [heq]
      grind

/-- The C1 area inequality holds if the walk visits a lower bound after q0
and there is at most one nonsupplied A from q0 to b. In particular this covers
the case when a minimum of the entire tail is attained after q0. It leaves
the case of an older minimum open. -/
theorem area_nonneg_of_fresh_low_visit (f : Nat → Bool) (n a q0 r b : Nat)
    {β : List Bool} (hβ : BlockWord β)
    (hseg : seg f 0 n = β ++ List.replicate a true)
    (hnq : n ≤ q0) (hqr : q0 ≤ r) (hrb : r ≤ b)
    (m : Int) (hr : Fw f r = m)
    (hmin : ∀ u, n ≤ u → u ≤ b → m ≤ Fw f u)
    (hbudget : cN (fun u => f u = true ∧ ¬ EndN f 0 u) q0 (b-q0) ≤ 1) :
    0 ≤ Ar f n (b-n) + ((b-n : Nat) : Int) * (Fw f n - Fw f b + 1) := by
  have htop : Fw f b ≤ m + 1 := by
    apply Classical.byContradiction
    intro h
    obtain ⟨u, v, hru, huv, hvb, _, _, huA, hnu, hvA, hnv⟩ :=
      two_nonsupplied_additions_of_recovery f n a r b hβ hseg (by omega) hrb m hr hmin (by omega)
    have htwo := two_marks_le_count (fun u => f u = true ∧ ¬ EndN f 0 u)
      q0 u v (b-q0) (by omega) huv (by omega) ⟨huA, hnu⟩ ⟨hvA, hnv⟩
    omega
  exact shifted_area_nonneg f n (Fw f b) (b-n) (by
    intro i hi hle
    have hm := hmin (n+i) (by omega) (by omega)
    omega)

open Classical in
/-- Integer-clock form, with nonsupplied A clocks counted from the original
left endpoint p throughout. The area uses the walk translated to p. -/
theorem area_nonneg_of_fresh_low_visit_int (e : Int → Bool) (p : Int)
    (n a q0 r b : Nat) {β : List Bool} (hβ : BlockWord β)
    (hseg : segment e p n = β ++ List.replicate a true)
    (hnq : n ≤ q0) (hqr : q0 ≤ r) (hrb : r ≤ b)
    (m : Int) (hr : Fw (fun i => e (p + (i : Int))) r = m)
    (hmin : ∀ u, n ≤ u → u ≤ b → m ≤ Fw (fun i => e (p + (i : Int))) u)
    (hbudget : countP (fun c => e c = true ∧ ¬ Endable e p c)
      (p + (q0 : Int)) (b-q0) ≤ 1) :
    0 ≤ Ar (fun i => e (p + (i : Int))) n (b-n) +
      ((b-n : Nat) : Int) *
        (Fw (fun i => e (p + (i : Int))) n - Fw (fun i => e (p + (i : Int))) b + 1) := by
  classical
  have hp0 : p = p + ((0 : Nat) : Int) := by simp
  rw [segment_seg e p p 0 hp0] at hseg
  have hb := countP_cN (fun c => e c = true ∧ ¬ Endable e p c)
    p (p + (q0 : Int)) q0 rfl (b-q0)
  rw [hb] at hbudget
  have hc := cN_congr
    (fun i => e (p + (i : Int)) = true ∧ ¬ Endable e p (p + (i : Int)))
    (fun i => e (p + (i : Int)) = true ∧ ¬ EndN (fun j => e (p + (j : Int))) 0 i)
    q0 (b-q0) (by
      intro i _ _
      rw [endable_iff e p p (p + (i : Int)) 0 i hp0 rfl])
  rw [hc] at hbudget
  exact area_nonneg_of_fresh_low_visit (fun i => e (p + (i : Int))) n a q0 r b
    hβ hseg hnq hqr hrb m hr hmin hbudget

/-! ## Exact old-history trimming under a depth bound -/

/-- A padded block suffix of mass r has length at most 5r/2. -/
theorem block_prefix_suffix_length_bound (f : Nat → Bool) (n a t : Nat)
    {β : List Bool} (hβ : BlockWord β)
    (hseg : seg f 0 n = β ++ List.replicate a true) (htn : t ≤ n) :
    2 * ((n-t : Nat) : Int) ≤ 5 * (Fw f n - Fw f t) := by
  have hdense := dense_pad hβ a
  rw [← hseg] at hdense
  have hsplit := suffix_split f 0 n t (Nat.zero_le _) (by omega)
  simp only [Nat.zero_add, Nat.sub_zero] at hsplit
  have hd := hdense (seg f 0 t) (seg f t (n-t)) hsplit.symm
  have hm := mass_cntF (seg f t (n-t))
  rw [seg_mass, show t + (n-t) = n by omega] at hm
  have hl := seg_length f t (n-t)
  rw [hl] at hm hd
  omega

/-- No endpoint whose height is at least g-D needs a start more than
5(D+1)/2 clocks before the end of a padded block prefix. This equivalence
preserves every actual supply clock, including windows of arbitrary lag. -/
theorem endable_iff_trimmed_block_prefix (f : Nat → Bool) (n a s b D : Nat)
    {β : List Bool} (hβ : BlockWord β)
    (hseg : seg f 0 n = β ++ List.replicate a true)
    (hsn : s ≤ n) (_hnb : n ≤ b)
    (hlevel : Fw f n - (D : Int) ≤ Fw f b)
    (hradius : 5 * ((D : Int) + 1) < 2 * (((n-s : Nat) : Int) + 1)) :
    EndN f 0 b ↔ EndN f s b := by
  constructor
  · rintro ⟨hA, t, k, _, htk, hk, hF, hAr⟩
    have hst : s ≤ t := by
      apply Classical.byContradiction
      intro h
      have ht : t ≤ n := by omega
      have hbnd := block_prefix_suffix_length_bound f n a t hβ hseg ht
      rw [htk] at hF
      omega
    exact ⟨hA, t, k, hst, htk, hk, hF, hAr⟩
  · exact end_mono f 0 s b (Nat.zero_le s)

/-- The density bound and mass parity improve the depth-four radius to 11. -/
theorem block_prefix_suffix_length_le_eleven (f : Nat → Bool) (n a t : Nat)
    {β : List Bool} (hβ : BlockWord β)
    (hseg : seg f 0 n = β ++ List.replicate a true) (htn : t ≤ n)
    (hmass : Fw f n - Fw f t ≤ 5) : n-t ≤ 11 := by
  have hbnd := block_prefix_suffix_length_bound f n a t hβ hseg htn
  have hm := mass_cntF (seg f t (n-t))
  rw [seg_mass, show t + (n-t) = n by omega, seg_length] at hm
  omega

/-- Exact history reduction at depth four. Starts before s can be discarded
when at least the last 11 clocks of the padded block prefix remain. -/
theorem endable_iff_last_eleven_of_depth_four (f : Nat → Bool) (n a s b : Nat)
    {β : List Bool} (hβ : BlockWord β)
    (hseg : seg f 0 n = β ++ List.replicate a true)
    (hsn : s ≤ n) (_hnb : n ≤ b) (hwidth : 11 ≤ n-s)
    (hlevel : Fw f n - 4 ≤ Fw f b) : EndN f 0 b ↔ EndN f s b := by
  constructor
  · rintro ⟨hA, t, k, _, htk, hk, hF, hAr⟩
    have hst : s ≤ t := by
      apply Classical.byContradiction
      intro h
      rw [htk] at hF
      have hbnd := block_prefix_suffix_length_le_eleven f n a t hβ hseg
        (by omega) (by omega)
      omega
    exact ⟨hA, t, k, hst, htk, hk, hF, hAr⟩
  · exact end_mono f 0 s b (Nat.zero_le s)

theorem block_append {u v : List Bool} (hu : BlockWord u) (hv : BlockWord v) :
    BlockWord (u ++ v) := by
  induction hv with
  | nil => simpa using hu
  | free _ ih => simpa [List.append_assoc] using BlockWord.free ih
  | aas _ ih => simpa [List.append_assoc] using BlockWord.aas ih
  | triple _ ih => simpa [List.append_assoc] using BlockWord.triple ih

theorem block_replicate_A : ∀ j : Nat, BlockWord (List.replicate j true)
  | 0 => BlockWord.nil
  | j+1 => by
      rw [List.replicate_succ']
      exact BlockWord.free (block_replicate_A j)

theorem block_drop_free (k : Nat) : BlockWord (([true] : List Bool).drop k) := by
  cases k with
  | zero => exact BlockWord.free BlockWord.nil
  | succ k => simp; exact BlockWord.nil

theorem block_drop_aas (k : Nat) : BlockWord (aasW.drop k) := by
  have hk : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ 4 ≤ k := by omega
  rcases hk with rfl | rfl | rfl | rfl | hk
  · exact BlockWord.aas BlockWord.nil
  · exact block_replicate_A 3
  · exact block_replicate_A 2
  · exact block_replicate_A 1
  · have hz : aasW.drop k = [] := List.drop_eq_nil_iff.mpr (by simpa [aasW] using hk)
    rw [hz]; exact BlockWord.nil

theorem block_drop_triple (k : Nat) : BlockWord (tripW.drop k) := by
  have hk : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨
      k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ 10 ≤ k := by omega
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hk
  · exact BlockWord.triple BlockWord.nil
  · exact BlockWord.aas (BlockWord.free (BlockWord.aas BlockWord.nil))
  · exact BlockWord.aas (block_replicate_A 4)
  · exact BlockWord.aas (block_replicate_A 3)
  · exact BlockWord.aas (block_replicate_A 2)
  · exact BlockWord.aas (block_replicate_A 1)
  · exact BlockWord.aas BlockWord.nil
  · exact block_replicate_A 3
  · exact block_replicate_A 2
  · exact block_replicate_A 1
  · have hz : tripW.drop k = [] := List.drop_eq_nil_iff.mpr (by simpa [tripW] using hk)
    rw [hz]; exact BlockWord.nil

theorem block_suffix_append (w B : List Bool)
    (hw : ∀ u v, u ++ v = w → BlockWord v)
    (hB : ∀ k, BlockWord (B.drop k)) :
    ∀ u v, u ++ v = w ++ B → BlockWord v := by
  intro u v h
  rcases List.append_eq_append_iff.mp h with ⟨a', h1, h2⟩ | ⟨c', _, h2⟩
  · rw [h2]
    have hfull : BlockWord B := by simpa using hB 0
    exact block_append (hw u a' h1.symm) hfull
  · have hv : v = B.drop c'.length := by rw [h2, List.drop_left]
    rw [hv]
    exact hB _

/-- The block-word language is closed under arbitrary suffixes. -/
theorem block_suffix {w : List Bool} (hw : BlockWord w) :
    ∀ u v : List Bool, u ++ v = w → BlockWord v := by
  induction hw with
  | nil =>
      intro u v h
      have hv := (List.append_eq_nil_iff.mp h).2
      rw [hv]; exact BlockWord.nil
  | free _ ih => exact block_suffix_append _ _ ih block_drop_free
  | aas _ ih => exact block_suffix_append _ _ ih block_drop_aas
  | triple _ ih => exact block_suffix_append _ _ ih block_drop_triple

/-- Every W-clock suffix of a block word is itself a block word, so old
contexts have representatives of length exactly W. -/
theorem block_suffix_representative (W : Nat) {w : List Bool}
    (hw : BlockWord w) (hW : W ≤ w.length) :
    ∃ u v : List Bool, w = u ++ v ∧ BlockWord v ∧ v.length = W := by
  let u := w.take (w.length-W)
  let v := w.drop (w.length-W)
  have heq : u ++ v = w := List.take_append_drop _ _
  exact ⟨u, v, heq.symm, block_suffix hw u v heq, by simp [v]; omega⟩

/-! ## Quadratic area retained by the old block prefix -/

/-- A mass-sensitive lower bound, sharper than positive area alone. -/
theorem block_area_quadratic_lower {w : List Bool} (hw : BlockWord w) :
    mass w * (mass w + 1) ≤ 2 * areaW w + 2 := by
  induction hw with
  | nil => decide
  | @free w hw ih =>
      rw [areaW_append, mass_append]
      change (mass w + 1) * (mass w + 1 + 1) ≤
        2 * (areaW w + 1 * mass w + 1) + 2
      grind
  | @aas w hw ih =>
      rcases block_mass hw with he | hm
      · subst w; decide
      · rw [areaW_append, mass_append]
        change (mass w + 2) * (mass w + 2 + 1) ≤
          2 * (areaW w + 4 * mass w + 2) + 2
        grind
  | @triple w hw ih =>
      rcases block_mass hw with he | hm
      · subst w; decide
      · rw [areaW_append, mass_append]
        change (mass w + 4) * (mass w + 4 + 1) ≤
          2 * (areaW w + 10 * mass w + 9) + 2
        grind

/-- The additive constant 2 is sharp at every mass at least 2. -/
theorem block_area_quadratic_sharp (j : Nat) :
    2 * areaW (aasW ++ List.replicate j true) + 2 =
      mass (aasW ++ List.replicate j true) * (mass (aasW ++ List.replicate j true) + 1) := by
  induction j with
  | zero => decide
  | succ j ih =>
      rw [List.replicate_succ', ← List.append_assoc,
        areaW_append (aasW ++ List.replicate j true) [true],
        mass_append (aasW ++ List.replicate j true) [true]]
      change 2 * (areaW (aasW ++ List.replicate j true) +
          1 * mass (aasW ++ List.replicate j true) + 1) + 2 =
        (mass (aasW ++ List.replicate j true) + 1) *
          (mass (aasW ++ List.replicate j true) + 1 + 1)
      grind

theorem triple_area_quadratic_sharp (j : Nat) :
    2 * areaW (tripW ++ List.replicate j true) + 2 =
      mass (tripW ++ List.replicate j true) * (mass (tripW ++ List.replicate j true) + 1) := by
  induction j with
  | zero => decide
  | succ j ih =>
      rw [List.replicate_succ', ← List.append_assoc,
        areaW_append (tripW ++ List.replicate j true) [true],
        mass_append (tripW ++ List.replicate j true) [true]]
      change 2 * (areaW (tripW ++ List.replicate j true) +
          1 * mass (tripW ++ List.replicate j true) + 1) + 2 =
        (mass (tripW ++ List.replicate j true) + 1) *
          (mass (tripW ++ List.replicate j true) + 1 + 1)
      grind

/-- The extremal prefix area has exactly two block shapes, followed only by A. -/
theorem block_area_quadratic_equality {w : List Bool} (hw : BlockWord w) :
    (2 * areaW w + 2 = mass w * (mass w + 1)) ↔
      ∃ j : Nat, w = aasW ++ List.replicate j true ∨ w = tripW ++ List.replicate j true := by
  constructor
  · induction hw with
    | nil => intro he; contradiction
    | @free w hw ih =>
        intro he
        have hprev : 2 * areaW w + 2 = mass w * (mass w + 1) := by
          rw [areaW_append, mass_append] at he
          change 2 * (areaW w + 1 * mass w + 1) + 2 =
            (mass w + 1) * (mass w + 1 + 1) at he
          grind
        obtain ⟨j, hj | hj⟩ := ih hprev
        · refine ⟨j+1, Or.inl ?_⟩
          rw [hj, List.replicate_succ', List.append_assoc]
        · refine ⟨j+1, Or.inr ?_⟩
          rw [hj, List.replicate_succ', List.append_assoc]
    | @aas w hw ih =>
        intro he
        rcases block_mass hw with hz | hm
        · subst w
          exact ⟨0, Or.inl rfl⟩
        · have hb := block_area_quadratic_lower hw
          rw [areaW_append, mass_append] at he
          change 2 * (areaW w + 4 * mass w + 2) + 2 =
            (mass w + 2) * (mass w + 2 + 1) at he
          grind
    | @triple w hw ih =>
        intro he
        rcases block_mass hw with hz | hm
        · subst w
          exact ⟨0, Or.inr rfl⟩
        · have hb := block_area_quadratic_lower hw
          rw [areaW_append, mass_append] at he
          change 2 * (areaW w + 10 * mass w + 9) + 2 =
            (mass w + 4) * (mass w + 4 + 1) at he
          grind
  · rintro ⟨j, hj | hj⟩
    · rw [hj]; exact block_area_quadratic_sharp j
    · rw [hj]; exact triple_area_quadratic_sharp j

/-- The actual prefix area of any older start has the same quadratic bound.
It supplies a stronger input to the old-minimum case without assuming Q. -/
theorem block_prefix_area_quadratic_lower (f : Nat → Bool) (n a t : Nat)
    {β : List Bool} (hβ : BlockWord β)
    (hseg : seg f 0 n = β ++ List.replicate a true) (htn : t ≤ n) :
    (Fw f n - Fw f t) * (Fw f n - Fw f t + 1) ≤ 2 * Ar f t (n-t) + 2 := by
  have hfull : BlockWord (seg f 0 n) := by
    rw [hseg]
    exact block_append hβ (block_replicate_A a)
  have hsplit := suffix_split f 0 n t (Nat.zero_le _) (by omega)
  simp only [Nat.zero_add, Nat.sub_zero] at hsplit
  have hsuffix := block_suffix hfull (seg f 0 t) (seg f t (n-t)) hsplit.symm
  have hbound := block_area_quadratic_lower hsuffix
  simpa only [← Ar_areaW, seg_mass, show t + (n-t) = n by omega] using hbound

theorem area_split_at (f : Nat → Bool) (t n b : Nat) (htn : t ≤ n) (hnb : n ≤ b) :
    Ar f t (b-t) = Ar f t (n-t) + Ar f n (b-n) +
      ((b-n : Nat) : Int) * (Fw f n - Fw f t) := by
  have hsplit := suffix_split f t (b-t) n htn (by omega)
  rw [show t + (b-t) = b by omega] at hsplit
  rw [Ar_areaW, hsplit, areaW_append, ← Ar_areaW, ← Ar_areaW, seg_length, seg_mass,
    show t + (n-t) = n by omega]
  omega

/-- Any actual P2 window starting in the old block prefix forces a
mass-dependent negative area after that prefix. This is a necessary
condition on such a window, not its unconditional exclusion. -/
theorem old_window_area_upper (f : Nat → Bool) (n a t b : Nat)
    {β : List Bool} (hβ : BlockWord β)
    (hseg : seg f 0 n = β ++ List.replicate a true)
    (htn : t ≤ n) (hnb : n ≤ b) (hwin : Win f t (b-t)) :
    2 * (Ar f n (b-n) + ((b-n : Nat) : Int) * (Fw f n - Fw f b + 1)) ≤
      2 - (Fw f n - Fw f b + 1) * (Fw f n - Fw f b + 1 + 1) := by
  have hprefix := block_prefix_area_quadratic_lower f n a t hβ hseg htn
  have hsplit := area_split_at f t n b htn hnb
  obtain ⟨_, hF, hzero⟩ := hwin
  rw [show t + (b-t) = b by omega] at hF
  have htlevel : Fw f t = Fw f b - 1 := by omega
  rw [htlevel] at hprefix hsplit
  grind

/-- Over a finite tail, the earliest older window start gives one common
block-prefix representative of mass at most D+1. Every tail supply clock is
preserved. Deficit of the deleted prefix is intentionally not asserted. -/
theorem endable_tail_mass_representative (f : Nat → Bool) (n a B D : Nat)
    {β : List Bool} (hβ : BlockWord β)
    (hseg : seg f 0 n = β ++ List.replicate a true)
    (hmin : ∀ b, n ≤ b → b < B → Fw f n - (D : Int) ≤ Fw f b) :
    ∃ s : Nat, s ≤ n ∧ BlockWord (seg f s (n-s)) ∧
      (s = n ∨ (1 ≤ Fw f n - Fw f s ∧ Fw f n - Fw f s ≤ (D : Int)+1)) ∧
      ∀ b, n ≤ b → b < B → (EndN f 0 b ↔ EndN f s b) := by
  classical
  let P : Nat → Prop := fun t => t < n ∧
    ∃ b, n ≤ b ∧ b < B ∧ f b = true ∧ Win f t (b-t)
  have hfull : BlockWord (seg f 0 n) := by
    rw [hseg]
    exact block_append hβ (block_replicate_A a)
  by_cases hex : ∃ t, P t
  · obtain ⟨t, ht⟩ := hex
    obtain ⟨s, hsn, hsP, hfirst⟩ := first_mark P n ⟨t, by have := ht.1; omega, ht⟩
    obtain ⟨hslt, b, hnb, hbB, _, hw⟩ := hsP
    have hsplit := suffix_split f 0 n s (Nat.zero_le _) (by omega)
    simp only [Nat.zero_add, Nat.sub_zero] at hsplit
    have hsword := block_suffix hfull (seg f 0 s) (seg f s (n-s)) hsplit.symm
    have hpos := (block_suffix_positive_walk f 0 n a hβ hseg s (Nat.zero_le _) (by omega)).1
    simp only [Nat.zero_add] at hpos
    have hlevel := hw.2.1
    rw [show s + (b-s) = b by omega] at hlevel
    have hlo := hmin b hnb hbB
    refine ⟨s, hsn, hsword, Or.inr ⟨hpos, by omega⟩, ?_⟩
    intro u hnu huB
    constructor
    · rintro ⟨hA, t, k, _, htk, hwin⟩
      have hst : s ≤ t := by
        apply Classical.byContradiction
        intro h
        have hPt : P t := by
          refine ⟨by omega, u, hnu, huB, hA, ?_⟩
          have heq : k = u-t := by omega
          simpa only [heq] using hwin
        exact hfirst t (by omega) hPt
      exact ⟨hA, t, k, hst, htk, hwin⟩
    · exact end_mono f 0 s u (Nat.zero_le _)
  · refine ⟨n, Nat.le_refl _, ?_, Or.inl rfl, ?_⟩
    · simpa [seg] using BlockWord.nil
    · intro u hnu huB
      constructor
      · rintro ⟨hA, t, k, _, htk, hwin⟩
        have hnt : n ≤ t := by
          apply Classical.byContradiction
          intro h
          apply hex
          refine ⟨t, by omega, u, hnu, huB, hA, ?_⟩
          have heq : k = u-t := by omega
          simpa only [heq] using hwin
        exact ⟨hA, t, k, hnt, htk, hwin⟩
      · exact end_mono f 0 n u (Nat.zero_le _)

theorem block_mass_nonnegative {w : List Bool} (hw : BlockWord w) : 0 ≤ mass w := by
  rcases block_mass hw with rfl | hm
  · decide
  · omega

theorem block_mass_one {w : List Bool} (hw : BlockWord w) (hm : mass w = 1) : w = [true] := by
  rcases block_first hw with he | ⟨v, hv, he | he | he⟩
  · subst w; simp [mass] at hm
  · rw [he, mass_append] at hm
    change 1 + mass v = 1 at hm
    rcases block_mass hv with hz | hpos
    · rw [hz] at he; simpa using he
    · omega
  · have hv0 := block_mass_nonnegative hv
    rw [he, mass_append] at hm
    have hb : mass aasW = 2 := by decide
    rw [hb] at hm
    omega
  · have hv0 := block_mass_nonnegative hv
    rw [he, mass_append] at hm
    have hb : mass tripW = 4 := by decide
    rw [hb] at hm
    omega

theorem block_mass_two {w : List Bool} (hw : BlockWord w) (hm : mass w = 2) :
    w = [true, true] ∨ w = aasW := by
  rcases block_first hw with he | ⟨v, hv, he | he | he⟩
  · subst w; simp [mass] at hm
  · rw [he, mass_append] at hm
    change 1 + mass v = 2 at hm
    have hv1 := block_mass_one hv (by omega)
    left; rw [he, hv1]; rfl
  · rw [he, mass_append] at hm
    have hb : mass aasW = 2 := by decide
    rw [hb] at hm
    rcases block_mass hv with hz | hpos
    · right; rw [he, hz]; simp
    · omega
  · have hv0 := block_mass_nonnegative hv
    rw [he, mass_append] at hm
    have hb : mass tripW = 4 := by decide
    rw [hb] at hm
    omega

/-- A uniform quadratic upper envelope for every old block-prefix area. -/
theorem block_area_quadratic_upper {w : List Bool} (hw : BlockWord w) :
    4 * areaW w ≤ 5 * mass w * mass w - 11 * mass w + 16 := by
  induction hw with
  | nil => decide
  | @free w hw ih =>
      rcases block_mass hw with hz | hm
      · subst w; decide
      · by_cases h1 : mass w = 1
        · rw [block_mass_one hw h1]; decide
        · have hm2 : 2 ≤ mass w := by omega
          rw [areaW_append, mass_append]
          change 4 * (areaW w + 1 * mass w + 1) ≤
            5 * (mass w + 1) * (mass w + 1) - 11 * (mass w + 1) + 16
          grind
  | @aas w hw ih =>
      rcases block_mass hw with hz | hm
      · subst w; decide
      · by_cases h1 : mass w = 1
        · rw [block_mass_one hw h1]; decide
        · by_cases h2 : mass w = 2
          · rcases block_mass_two hw h2 with he | he <;> rw [he] <;> decide
          · have hm3 : 3 ≤ mass w := by omega
            rw [areaW_append, mass_append]
            change 4 * (areaW w + 4 * mass w + 2) ≤
              5 * (mass w + 2) * (mass w + 2) - 11 * (mass w + 2) + 16
            grind
  | @triple w hw ih =>
      rw [areaW_append, mass_append]
      change 4 * (areaW w + 10 * mass w + 9) ≤
        5 * (mass w + 4) * (mass w + 4) - 11 * (mass w + 4) + 16
      grind

theorem block_area_upper_sharp :
    4 * areaW ([true] ++ aasW) =
      5 * mass ([true] ++ aasW) * mass ([true] ++ aasW) - 11 * mass ([true] ++ aasW) + 16 := by
  decide

theorem block_prefix_area_quadratic_upper (f : Nat → Bool) (n a t : Nat)
    {β : List Bool} (hβ : BlockWord β)
    (hseg : seg f 0 n = β ++ List.replicate a true) (htn : t ≤ n) :
    4 * Ar f t (n-t) ≤
      5 * (Fw f n - Fw f t) * (Fw f n - Fw f t) - 11 * (Fw f n - Fw f t) + 16 := by
  have hfull : BlockWord (seg f 0 n) := by
    rw [hseg]
    exact block_append hβ (block_replicate_A a)
  have hsplit := suffix_split f 0 n t (Nat.zero_le _) (by omega)
  simp only [Nat.zero_add, Nat.sub_zero] at hsplit
  have hsuffix := block_suffix hfull (seg f 0 t) (seg f t (n-t)) hsplit.symm
  have hbound := block_area_quadratic_upper hsuffix
  simpa only [← Ar_areaW, seg_mass, show t + (n-t) = n by omega] using hbound

/-! ## Counts before an older P2 window

The additions in this section count every A in the tail, not merely its
nonsupplied A clocks. No bound on the tail length or subtraction count is assumed. -/

/-- Among words with fixed counts, putting every S before every A minimizes
the sum of prefix levels. -/
theorem areaW_count_lower (w : List Bool) :
    ones w * (ones w+1) - ((w.length : Int)-ones w) * ((w.length : Int)-ones w+1) -
      2 * ones w * ((w.length : Int)-ones w) ≤ 2*areaW w := by
  induction w with
  | nil => decide
  | cons b w ih =>
      have hb := ones_bounds w
      cases b <;> simp [ones, areaW, List.length_cons, sign] at * <;> grind

/-- An actual window starting strictly before the block-prefix boundary can
only end after a tail whose S count is at most twice its total A count minus
two. This is an old-window obstruction, not the desired bound on nonsupplied A. -/
theorem old_window_count_barrier (f : Nat → Bool) (n a t b : Nat)
    {β : List Bool} (hβ : BlockWord β)
    (hseg : seg f 0 n = β ++ List.replicate a true)
    (htn : t < n) (hnb : n < b) (hwin : Win f t (b-t)) :
    ((b-n : Nat) : Int) - ones (seg f n (b-n)) ≤
      2 * ones (seg f n (b-n)) - 2 := by
  have hp := block_suffix_positive_walk f 0 n a hβ hseg t (Nat.zero_le _) (by omega)
  simp only [Nat.zero_add] at hp
  have hquad := old_window_area_upper f n a t b hβ hseg (by omega) (by omega) hwin
  have harea := areaW_count_lower (seg f n (b-n))
  simp only [seg_length, ← Ar_areaW] at harea
  have hmass := mass_eq (seg f n (b-n))
  rw [seg_mass, seg_length, show n + (b-n) = b by omega] at hmass
  have hlevel := hwin.2.1
  rw [show t + (b-t) = b by omega] at hlevel
  have hbnds := ones_bounds (seg f n (b-n))
  rw [seg_length] at hbnds
  have hlen : 0 < ((b-n : Nat) : Int) := by exact_mod_cast Nat.sub_pos_of_lt hnb
  have hs : 0 < ((b-n : Nat) : Int) - ones (seg f n (b-n)) := by omega
  apply Classical.byContradiction
  intro hneg
  have hbad : 2 * ones (seg f n (b-n)) -
      (((b-n : Nat) : Int) - ones (seg f n (b-n))) - 2 < 0 := by omega
  have hprod := Int.mul_neg_of_pos_of_neg hs hbad
  have hrel : Fw f n - Fw f b + 1 =
      ((b-n : Nat) : Int) - 2 * ones (seg f n (b-n)) + 1 := by omega
  rw [hrel] at hquad
  have harith (L A V : Int)
      (hq : 2 * (V + L * (L-2*A+1)) ≤ 2-(L-2*A+1)*(L-2*A+2))
      (hl : A*(A+1)-(L-A)*(L-A+1)-2*A*(L-A) ≤ 2*V) :
      0 ≤ (L-A)*(2*A-(L-A)-2) := by grind
  have hnonneg := harith ((b-n : Nat) : Int) (ones (seg f n (b-n)))
      (Ar f n (b-n)) (by simpa [Int.add_assoc] using hquad) harea
  omega

/-! The finite checker has independent transparent word functions. These
lemmas connect them to the same walk used by the actual P2 windows. -/

theorem checked_wordArea_eq (w : List Bool) :
    Recaman.ThreeNonsuppliedData.wordArea w = areaW w := by
  induction w with
  | nil => rfl
  | cons c w ih => simp [Recaman.ThreeNonsuppliedData.wordArea, areaW, ih]

theorem ones_drop_le (w : List Bool) (t : Nat) : ones (w.drop t) ≤ ones w := by
  have h := ones_bounds (w.take t)
  have hs : w.take t ++ w.drop t = w := List.take_append_drop t w
  have hsum := ones_append (w.take t) (w.drop t)
  rw [hs] at hsum
  omega

theorem localSupply_iff (w : List Bool) :
    Recaman.ThreeNonsuppliedData.localSupply w=true ↔
      ∃ t, t<w.length ∧ mass (w.drop t)=1 ∧
        Recaman.ThreeNonsuppliedData.wordArea (w.drop t)=0 := by
  simp [Recaman.ThreeNonsuppliedData.localSupply, List.any_eq_true]

theorem localSupply_trim (w : List Bool) (hA : ones w ≤ 7) :
    Recaman.ThreeNonsuppliedData.localSupply (Recaman.ThreeNonsuppliedData.trim w) =
      Recaman.ThreeNonsuppliedData.localSupply w := by
  apply Bool.eq_iff_iff.mpr
  rw [localSupply_iff, localSupply_iff]
  unfold Recaman.ThreeNonsuppliedData.trim
  constructor
  · rintro ⟨t, ht, hwin⟩
    have htlen := ht
    refine ⟨w.length-13+t, ?_, ?_⟩
    · simp only [List.length_drop] at htlen
      omega
    · simpa only [List.drop_drop, Nat.add_comm] using hwin
  · rintro ⟨t, ht, hwin⟩
    have htlen := ht
    have hw : mass (w.drop t) = 1 ∧
        Recaman.ThreeNonsuppliedData.wordArea (w.drop t) = 0 := hwin
    have hm := mass_eq (w.drop t)
    rw [hw.1, List.length_drop] at hm
    have hones := ones_drop_le w t
    have hnear : w.length-13 ≤ t := by omega
    refine ⟨t-(w.length-13), ?_, ?_⟩
    · simp only [List.length_drop]
      omega
    · rw [List.drop_drop, show w.length-13+(t-(w.length-13)) = t by omega]
      exact hwin

theorem seg_drop (f : Nat → Bool) (s m j : Nat) (hj : j ≤ m) :
    (seg f s m).drop j = seg f (s+j) (m-j) := by
  have h := seg_add f s j (m-j)
  rw [Nat.add_sub_cancel' hj] at h
  calc
    (seg f s m).drop j = (seg f s j ++ seg f (s+j) (m-j)).drop
        (seg f s j).length := by rw [h, seg_length]
    _ = _ := List.drop_left

theorem localSupply_seg_iff (f : Nat → Bool) (n b : Nat) (hnb : n ≤ b)
    (hA : f b = true) :
    Recaman.ThreeNonsuppliedData.localSupply (seg f n (b-n)) = true ↔ EndN f n b := by
  rw [localSupply_iff]
  constructor
  · rintro ⟨j, hj, hw⟩
    have hjn := hj
    rw [seg_length] at hjn
    have hdrop := seg_drop f n (b-n) j (by omega)
    have hwp : mass ((seg f n (b-n)).drop j) = 1 ∧
        Recaman.ThreeNonsuppliedData.wordArea ((seg f n (b-n)).drop j) = 0 :=
      hw
    rw [hdrop, checked_wordArea_eq, ← Ar_areaW] at hwp
    rw [seg_mass] at hwp
    refine ⟨hA, n+j, b-(n+j), by omega, by omega, by omega, ?_, ?_⟩
    · rw [show n+j+(b-(n+j))=n+j+(b-n-j) by omega]
      omega
    · rw [show b-(n+j)=b-n-j by omega]
      exact hwp.2
  · rintro ⟨_, t, k, hnt, htk, hk, hlevel, harea⟩
    refine ⟨t-n, ?_, ?_⟩
    · rw [seg_length]; omega
    · rw [seg_drop f n (b-n) (t-n) (by omega),
        show n+(t-n)=t by omega, show b-n-(t-n)=k by omega]
      simp only [checked_wordArea_eq, ← Ar_areaW, seg_mass]
      exact ⟨by omega, harea⟩

theorem old_window_signature (f : Nat → Bool) (n a t b : Nat)
    {β : List Bool} (hβ : BlockWord β)
    (hseg : seg f 0 n = β ++ List.replicate a true)
    (htn : t < n) (hnb : n ≤ b) (hwin : Win f t (b-t)) :
    Recaman.ThreeNonsuppliedData.oldSignature (seg f n (b-n)) = true := by
  have hfull : BlockWord (seg f 0 n) := by
    rw [hseg]; exact block_append hβ (block_replicate_A a)
  have hsplit := suffix_split f 0 n t (Nat.zero_le _) (by omega)
  simp only [Nat.zero_add, Nat.sub_zero] at hsplit
  have hsuffix := block_suffix hfull (seg f 0 t) (seg f t (n-t)) hsplit.symm
  have hp := block_suffix_positive_walk f 0 n a hβ hseg t (Nat.zero_le _) (by omega)
  simp only [Nat.zero_add] at hp
  have hlow := block_area_quadratic_lower hsuffix
  have hupp := block_area_quadratic_upper hsuffix
  have harea := area_split_at f t n b (by omega) hnb
  have hlevel := hwin.2.1
  have hzero := hwin.2.2
  rw [show t+(b-t)=b by omega] at hlevel
  have hr : 1-mass (seg f n (b-n)) = mass (seg f t (n-t)) := by
    rw [seg_mass, seg_mass, show n+(b-n)=b by omega, show t+(n-t)=n by omega]
    omega
  have hB : -Recaman.ThreeNonsuppliedData.wordArea (seg f n (b-n)) -
      ((seg f n (b-n)).length : Int)*(1-mass (seg f n (b-n))) =
      areaW (seg f t (n-t)) := by
    rw [checked_wordArea_eq, ← Ar_areaW, ← Ar_areaW, seg_length, hr, seg_mass,
      show t+(n-t)=n by omega]
    grind
  have hmpos : 1 ≤ mass (seg f t (n-t)) := by
    rw [seg_mass, show t+(n-t)=n by omega]; exact hp.1
  have hapos : 1 ≤ areaW (seg f t (n-t)) := by
    rw [← Ar_areaW]; exact hp.2
  have hone : mass (seg f t (n-t))=1 → areaW (seg f t (n-t))=1 := by
    intro hm
    rw [block_mass_one hsuffix hm]
    decide
  simp only [Recaman.ThreeNonsuppliedData.oldSignature, decide_eq_true_eq]
  rw [hB, hr]
  exact ⟨hmpos, hapos, hlow, hupp, hone⟩

theorem ones_seg_eq_count (f : Nat → Bool) (n k : Nat) :
    ones (seg f n k) = (cN (fun u => f u=true) n k : Int) := by
  have hm := mass_eq (seg f n k)
  rw [seg_mass, seg_length] at hm
  have hc := cN_walk f n k
  omega

/-- Every actual supplied clock has either a local P2 suffix or a necessary
old-prefix signature. The old alternative is impossible once thirteen S
have occurred while at most seven A have occurred. -/
theorem supply_clock_smallA (f : Nat → Bool) (n a b : Nat)
    {β : List Bool} (hβ : BlockWord β)
    (hseg : seg f 0 n = β ++ List.replicate a true) (hnb : n ≤ b)
    (hA : ones (seg f n (b-n)) ≤ 7) (he : EndN f 0 b) :
    Recaman.ThreeNonsuppliedData.localSupply (seg f n (b-n))=true ∨
      ((((b-n : Nat) : Int)-ones (seg f n (b-n)) < 13) ∧
        Recaman.ThreeNonsuppliedData.oldSignature (seg f n (b-n))=true) := by
  obtain ⟨hbA, t, k, ht0, htk, hk, hF, hAr⟩ := he
  by_cases htn : n ≤ t
  · left
    apply (localSupply_seg_iff f n b hnb hbA).mpr
    exact ⟨hbA, t, k, htn, htk, hk, hF, hAr⟩
  · have hwin : Win f t (b-t) := by
      have heq : b-t=k := by omega
      simpa only [heq] using (show Win f t k from ⟨hk,hF,hAr⟩)
    have hsig := old_window_signature f n a t b hβ hseg (by omega) hnb hwin
    right; refine ⟨?_, hsig⟩
    by_cases hneq : n=b
    · rw [← hneq]; simp [seg, ones]
    · have hcount := old_window_count_barrier f n a t b hβ hseg (by omega) (by omega) hwin
      omega

theorem trim_append_letter (w : List Bool) (c : Bool) :
    Recaman.ThreeNonsuppliedData.trim (Recaman.ThreeNonsuppliedData.trim w ++ [c]) =
      Recaman.ThreeNonsuppliedData.trim (w++[c]) := by
  unfold Recaman.ThreeNonsuppliedData.trim
  by_cases hlen : w.length ≤ 13
  · simp [show w.length-13=0 by omega]
  · have hw : 13 < w.length := by omega
    simp only [List.length_append, List.length_drop, List.length_singleton]
    rw [show w.length-(w.length-13)+1-13=1 by omega,
      List.drop_append_of_le_length (by simp only [List.length_drop]; omega), List.drop_drop,
      List.drop_append_of_le_length (by omega)]
    congr 2
    omega

noncomputable def actualSmallState (f : Nat → Bool) (n k : Nat) :
    Recaman.ThreeNonsuppliedData.State :=
  let s := cN (fun u => f u=false) n k
  let w := seg f n k
  ⟨if 13≤s then Recaman.ThreeNonsuppliedData.trim w else w,
    cN (fun u => f u=true) n k, min 13 s,
    cN (fun u => f u=true ∧ ¬EndN f 0 u) n k⟩

theorem actualSmallState_zero (f : Nat → Bool) (n : Nat) :
    actualSmallState f n 0 = ⟨[],0,0,0⟩ := by
  simp [actualSmallState, cN, seg]

theorem actualSmallState_S (f : Nat → Bool) (n k : Nat) (hS : f (n+k)=false) :
    Recaman.ThreeNonsuppliedData.stepS (actualSmallState f n k) =
      actualSmallState f n (k+1) := by
  have ha := cN_succ_neg (fun u => f u=true) n k (by simp [hS])
  have hs := cN_succ_pos (fun u => f u=false) n k hS
  have han := cN_succ_neg (fun u => f u=true ∧ ¬EndN f 0 u) n k (by simp [hS])
  by_cases hbig : 13≤cN (fun u => f u=false) n k
  · have hm : min 13 (cN (fun u => f u=false) n k)=13 := by omega
    have hm' : min 13 (cN (fun u => f u=false) n k+1)=13 := by omega
    have hbig' : 13≤cN (fun u => f u=false) n k+1 := by omega
    simp [actualSmallState, Recaman.ThreeNonsuppliedData.stepS, ha, hs, han,
      seg_succ, hS, hbig, hbig', hm, hm', trim_append_letter]
  · by_cases hbig' : 13≤cN (fun u => f u=false) n k+1
    · have hm : min 13 (cN (fun u => f u=false) n k)=12 := by omega
      have hm' : min 13 (cN (fun u => f u=false) n k+1)=13 := by omega
      simp [actualSmallState, Recaman.ThreeNonsuppliedData.stepS, ha, hs, han,
        seg_succ, hS, hbig, hbig', hm, hm']
    · have hm : min 13 (cN (fun u => f u=false) n k)=cN (fun u => f u=false) n k := by omega
      have hm' : min 13 (cN (fun u => f u=false) n k+1)=cN (fun u => f u=false) n k+1 := by omega
      have hne : cN (fun u => f u=false) n k+1 ≠13 := by omega
      simp [actualSmallState, Recaman.ThreeNonsuppliedData.stepS, ha, hs, han,
        seg_succ, hS, hbig, hbig', hm, hm', hne]

theorem actualSmallState_local (f : Nat → Bool) (n k : Nat)
    (hA : cN (fun u => f u=true) n k ≤ 7) :
    Recaman.ThreeNonsuppliedData.localSupply (actualSmallState f n k).word =
      Recaman.ThreeNonsuppliedData.localSupply (seg f n k) := by
  have hones : ones (seg f n k) ≤ 7 := by rw [ones_seg_eq_count]; omega
  unfold actualSmallState
  dsimp only
  split
  · exact localSupply_trim _ hones
  · rfl

theorem actualSmallState_admitted (f : Nat → Bool) (n a k : Nat)
    {β : List Bool} (hβ : BlockWord β)
    (hseg : seg f 0 n = β ++ List.replicate a true)
    (hA : f (n+k)=true) (hcount : cN (fun u => f u=true) n k ≤ 7)
    (e : Bool) (he : if e then EndN f 0 (n+k) else ¬EndN f 0 (n+k)) :
    (if e then Recaman.ThreeNonsuppliedData.localSupply (actualSmallState f n k).word ||
      (decide ((actualSmallState f n k).subtractions<13) &&
        Recaman.ThreeNonsuppliedData.oldSignature (actualSmallState f n k).word)
      else !Recaman.ThreeNonsuppliedData.localSupply (actualSmallState f n k).word)=true := by
  have hlocal := actualSmallState_local f n k hcount
  cases e
  · have hfalse : Recaman.ThreeNonsuppliedData.localSupply (seg f n k)=false := by
      cases h : Recaman.ThreeNonsuppliedData.localSupply (seg f n k)
      · rfl
      · have hloc : EndN f n (n+k) := (localSupply_seg_iff f n (n+k) (by omega) hA).mp
            (by simpa using h)
        exact absurd (end_mono f 0 n (n+k) (Nat.zero_le _) hloc) he
    simp [hlocal, hfalse]
  · have hones : ones (seg f n k) ≤ 7 := by rw [ones_seg_eq_count]; omega
    have hsup := supply_clock_smallA f n a (n+k) hβ hseg (by omega)
      (by simpa using hones) he
    simp only [Nat.add_sub_cancel_left] at hsup
    rcases hsup with hl | ⟨hs, ho⟩
    · simp [hlocal, hl]
    · have hc := cN_walk f n k
      have hon := ones_seg_eq_count f n k
      have hslt : cN (fun u => f u=false) n k<13 := by omega
      have hmin : min 13 (cN (fun u => f u=false) n k) = cN (fun u => f u=false) n k := by omega
      have hnot : ¬13≤cN (fun u => f u=false) n k := by omega
      simp [actualSmallState, hnot, hmin, hslt, ho]

theorem actualSmallState_A (f : Nat → Bool) (n a k : Nat)
    {β : List Bool} (hβ : BlockWord β)
    (hseg : seg f 0 n = β ++ List.replicate a true)
    (hA : f (n+k)=true) (hcount : cN (fun u => f u=true) n k ≤ 7)
    (e : Bool) (he : if e then EndN f 0 (n+k) else ¬EndN f 0 (n+k))
    (hbudget : cN (fun u => f u=true ∧ ¬EndN f 0 u) n (k+1)≤3)
    (hbalance : 1 ≤ (cN (fun u => f u=false) n k : Int) -
      (cN (fun u => f u=true) n k+1 : Nat) +
      (cN (fun u => f u=true ∧ ¬EndN f 0 u) n (k+1) : Int)) :
    Recaman.ThreeNonsuppliedData.stepA (actualSmallState f n k) e =
      some (actualSmallState f n (k+1)) := by
  have ha := cN_succ_pos (fun u => f u=true) n k hA
  have hs := cN_succ_neg (fun u => f u=false) n k (by simp [hA])
  have han : cN (fun u => f u=true ∧ ¬EndN f 0 u) n (k+1) =
      cN (fun u => f u=true ∧ ¬EndN f 0 u) n k + (if e then 0 else 1) := by
    cases e
    · exact cN_succ_pos _ n k ⟨hA,he⟩
    · have he' : EndN f 0 (n+k) := by simpa using he
      have hn := cN_succ_neg (fun u => f u=true ∧ ¬EndN f 0 u) n k (fun h => h.2 he')
      simpa using hn
  have hadmit := actualSmallState_admitted f n a k hβ hseg hA hcount e he
  have hb : (actualSmallState f n k).nonsupplied+(if e then 0 else 1)≤3 := by
    change cN (fun u => f u=true ∧ ¬EndN f 0 u) n k + _ ≤ 3
    rw [← han]; exact hbudget
  have hd : (actualSmallState f n k).subtractions=13 ∨
      1≤((actualSmallState f n k).subtractions : Int) -
        ((actualSmallState f n k).additions+1 : Nat) +
        ((actualSmallState f n k).nonsupplied+(if e then 0 else 1) : Nat) := by
    by_cases hbig : 13≤cN (fun u => f u=false) n k
    · left; simp only [actualSmallState]; omega
    · right
      have hm : min 13 (cN (fun u => f u=false) n k)=cN (fun u => f u=false) n k := by omega
      simpa only [actualSmallState, hm, ← han] using hbalance
  have heval : Recaman.ThreeNonsuppliedData.stepA (actualSmallState f n k) e =
      some ⟨if (actualSmallState f n k).subtractions=13 then
          Recaman.ThreeNonsuppliedData.trim ((actualSmallState f n k).word++[true])
          else (actualSmallState f n k).word++[true],
        (actualSmallState f n k).additions+1, (actualSmallState f n k).subtractions,
        (actualSmallState f n k).nonsupplied+(if e then 0 else 1)⟩ := by
    push_cast at hd
    simp [Recaman.ThreeNonsuppliedData.stepA, hadmit, hb, hd]
  rw [heval]
  by_cases hbig : 13≤cN (fun u => f u=false) n k
  · have hm : min 13 (cN (fun u => f u=false) n k)=13 := by omega
    simp [actualSmallState, ha, hs, han, seg_succ, hA, hbig, hm, trim_append_letter]
  · have hm : min 13 (cN (fun u => f u=false) n k)=cN (fun u => f u=false) n k := by omega
    have hne : cN (fun u => f u=false) n k≠13 := by omega
    simp [actualSmallState, ha, hs, han, seg_succ, hA, hbig, hm, hne]

theorem count_prefix_le (P : Nat → Prop) (n k B : Nat) (hk : k≤B) :
    cN P n k ≤ cN P n B := by
  have h := cN_add P n k (B-k)
  rw [Nat.add_sub_cancel' hk] at h
  omega

theorem addition_endable_partition (f : Nat → Bool) (n k : Nat) :
    cN (fun u => f u=true) n k = cN (EndN f 0) n k +
      cN (fun u => f u=true ∧ ¬EndN f 0 u) n k := by
  have h := cN_split (fun u => f u=true) (EndN f 0) n k
  have heq : cN (fun u => f u=true ∧ EndN f 0 u) n k = cN (EndN f 0) n k := by
    apply cN_congr
    intro u _ _
    exact ⟨fun h => h.2, fun h => ⟨h.1,h⟩⟩
  omega

/-- Every actual prefix of a positive-deficit excursion with at most three
nonsupplied additions is represented by the kernel-checked finite graph.
The bound of seven previous additions is supplied by the induction invariant,
not assumed for the whole input word. -/
theorem three_nonsupplied_state_member (f : Nat → Bool) (n a B : Nat)
    {β : List Bool} (hβ : BlockWord β)
    (hseg : seg f 0 n = β ++ List.replicate a true)
    (hpos : ∀ k, 0<k → k≤B → cN (EndN f 0) n k+1 ≤ cN (fun u => f u=false) n k)
    (hbudget : cN (fun u => f u=true ∧ ¬EndN f 0 u) n B≤3) :
    Recaman.ThreeNonsuppliedData.Member Recaman.ThreeNonsuppliedData.rows
      (actualSmallState f n B) := by
  have hmember : ∀ k, k≤B → Recaman.ThreeNonsuppliedData.Member
      Recaman.ThreeNonsuppliedData.rows (actualSmallState f n k) := by
    intro k
    induction k with
    | zero =>
        intro _
        rw [actualSmallState_zero]
        exact Recaman.ThreeNonsuppliedData.initial_member
    | succ k ih =>
        intro hk
        have hprev := ih (by omega)
        have hcount : cN (fun u => f u=true) n k≤7 := by
          have h := Recaman.ThreeNonsuppliedData.member_additions_lt_eight
            Recaman.ThreeNonsuppliedData.rows Recaman.ThreeNonsuppliedData.rows_verified
            (actualSmallState f n k) hprev
          change cN (fun u => f u=true) n k<8 at h
          omega
        by_cases hS : f (n+k)=false
        · rw [← actualSmallState_S f n k hS]
          exact Recaman.ThreeNonsuppliedData.member_stepS _
            Recaman.ThreeNonsuppliedData.rows_verified _ hprev
        · have hA : f (n+k)=true := by cases h : f (n+k) <;> simp_all
          have hbud : cN (fun u => f u=true ∧ ¬EndN f 0 u) n (k+1)≤3 := by
            have h := count_prefix_le (fun u => f u=true ∧ ¬EndN f 0 u) n (k+1) B hk
            omega
          have hpar := addition_endable_partition f n (k+1)
          have hp := hpos (k+1) (by omega) hk
          have ha := cN_succ_pos (fun u => f u=true) n k hA
          have hs := cN_succ_neg (fun u => f u=false) n k (by simp [hA])
          have hbal : 1≤(cN (fun u => f u=false) n k : Int)-
              (cN (fun u => f u=true) n k+1 : Nat)+
              (cN (fun u => f u=true ∧ ¬EndN f 0 u) n (k+1) : Int) := by omega
          by_cases he : EndN f 0 (n+k)
          · exact Recaman.ThreeNonsuppliedData.member_stepA _
              Recaman.ThreeNonsuppliedData.rows_verified _ _ true hprev
              (actualSmallState_A f n a k hβ hseg hA hcount true he hbud hbal)
          · exact Recaman.ThreeNonsuppliedData.member_stepA _
              Recaman.ThreeNonsuppliedData.rows_verified _ _ false hprev
              (actualSmallState_A f n a k hβ hseg hA hcount false he hbud hbal)
  exact hmember B (Nat.le_refl _)

theorem three_nonsupplied_additions_le_seven (f : Nat → Bool) (n a B : Nat)
    {β : List Bool} (hβ : BlockWord β)
    (hseg : seg f 0 n = β ++ List.replicate a true)
    (hpos : ∀ k, 0<k → k≤B → cN (EndN f 0) n k+1 ≤ cN (fun u => f u=false) n k)
    (hbudget : cN (fun u => f u=true ∧ ¬EndN f 0 u) n B≤3) :
    cN (fun u => f u=true) n B≤7 := by
  have hm := three_nonsupplied_state_member f n a B hβ hseg hpos hbudget
  have h := Recaman.ThreeNonsuppliedData.member_additions_lt_eight
    Recaman.ThreeNonsuppliedData.rows Recaman.ThreeNonsuppliedData.rows_verified _ hm
  change cN (fun u => f u=true) n B<8 at h
  omega

theorem seg_take (f : Nat → Bool) (n B j : Nat) (hj : j≤B) :
    (seg f n B).take j = seg f n j := by
  have h := seg_add f n j (B-j)
  rw [Nat.add_sub_cancel' hj] at h
  calc
    (seg f n B).take j = (seg f n j ++ seg f (n+j) (B-j)).take
        (seg f n j).length := by rw [seg_length, h]
    _ = _ := List.take_left

theorem endpoint_words_depth_checked :
    (Recaman.ThreeNonsuppliedData.endpointWords.all fun w =>
      (List.range (w.length+1)).all fun j => decide (-4 ≤ mass (w.take j)))=true := by decide

theorem endpoint_word_prefix_depth (w : List Bool)
    (hw : w ∈ Recaman.ThreeNonsuppliedData.endpointWords) (j : Nat) (hj : j≤w.length) :
    -4≤mass (w.take j) := by
  have h := List.all_eq_true.mp endpoint_words_depth_checked w hw
  exact of_decide_eq_true (List.all_eq_true.mp h j (List.mem_range.mpr (by omega)))

/-- The eight endpoint words are classified for arbitrary length and arbitrary
old block prefix, using the original-base supplies throughout. -/
theorem three_nonsupplied_excursion_word (f : Nat → Bool) (n a B : Nat)
    {β : List Bool} (hβ : BlockWord β)
    (hseg : seg f 0 n = β ++ List.replicate a true)
    (hpos : ∀ k, 0<k → k≤B → cN (EndN f 0) n k+1 ≤ cN (fun u => f u=false) n k)
    (hbudget : cN (fun u => f u=true ∧ ¬EndN f 0 u) n B≤3)
    (hend : cN (EndN f 0) n B+1 = cN (fun u => f u=false) n B) :
    seg f n B ∈ Recaman.ThreeNonsuppliedData.endpointWords := by
  have hm := three_nonsupplied_state_member f n a B hβ hseg hpos hbudget
  have ha := three_nonsupplied_additions_le_seven f n a B hβ hseg hpos hbudget
  have hpar := addition_endable_partition f n B
  have hslt : cN (fun u => f u=false) n B<13 := by omega
  have hnot : ¬13≤cN (fun u => f u=false) n B := by omega
  have hmin : min 13 (cN (fun u => f u=false) n B)=cN (fun u => f u=false) n B := by omega
  have hbal : ((actualSmallState f n B).subtractions : Int)-
      ((actualSmallState f n B).additions : Int)+
      ((actualSmallState f n B).nonsupplied : Int)=1 := by
    simp only [actualSmallState, hmin]
    omega
  have h := Recaman.ThreeNonsuppliedData.member_endpoint_word
    Recaman.ThreeNonsuppliedData.rows Recaman.ThreeNonsuppliedData.rows_verified _ hm hbal
  simpa only [actualSmallState, if_neg hnot] using h

theorem three_nonsupplied_excursion_depth_offset (f : Nat → Bool) (n a B : Nat)
    {β : List Bool} (hβ : BlockWord β)
    (hseg : seg f 0 n = β ++ List.replicate a true)
    (hpos : ∀ k, 0<k → k≤B → cN (EndN f 0) n k+1 ≤ cN (fun u => f u=false) n k)
    (hbudget : cN (fun u => f u=true ∧ ¬EndN f 0 u) n B≤3)
    (hend : cN (EndN f 0) n B+1 = cN (fun u => f u=false) n B)
    (j : Nat) (hj : j≤B) : Fw f n-4 ≤ Fw f (n+j) := by
  have hw := three_nonsupplied_excursion_word f n a B hβ hseg hpos hbudget hend
  have hd := endpoint_word_prefix_depth (seg f n B) hw j (by rw [seg_length]; exact hj)
  rw [seg_take f n B j hj, seg_mass] at hd
  omega

/-- Card H-20261023-01 in the original left-base convention. The old global
deficit is zero at n and positive afterwards, with final deficit one. -/
theorem three_nonsupplied_excursion_depth (f : Nat → Bool) (n a q : Nat)
    {β : List Bool} (hβ : BlockWord β)
    (hseg : seg f 0 n = β ++ List.replicate a true) (hnq : n≤q)
    (hzero : cN (EndN f 0) 0 n = cN (fun u => f u=false) 0 n)
    (hpos : ∀ u, n<u → u≤q → cN (EndN f 0) 0 u+1 ≤ cN (fun u => f u=false) 0 u)
    (hend : cN (EndN f 0) 0 q+1 = cN (fun u => f u=false) 0 q)
    (hbudget : cN (fun u => f u=true ∧ ¬EndN f 0 u) n (q-n)≤3) :
    ∀ u, n≤u → u≤q → Fw f n-4≤Fw f u := by
  have hrel : ∀ k, 0<k → k≤q-n →
      cN (EndN f 0) n k+1≤cN (fun u => f u=false) n k := by
    intro k hk hkle
    have hp := hpos (n+k) (by omega) (by omega)
    have he := cN_add (EndN f 0) 0 n k
    have hs := cN_add (fun u => f u=false) 0 n k
    simp only [Nat.zero_add] at he hs
    omega
  have hlast : cN (EndN f 0) n (q-n)+1=cN (fun u => f u=false) n (q-n) := by
    have he := cN_add (EndN f 0) 0 n (q-n)
    have hs := cN_add (fun u => f u=false) 0 n (q-n)
    rw [Nat.add_sub_cancel' hnq] at he hs
    simp only [Nat.zero_add] at he hs
    omega
  intro u hnu huq
  have h := three_nonsupplied_excursion_depth_offset f n a (q-n) hβ hseg hrel hbudget hlast
    (u-n) (by omega)
  simpa only [Nat.add_sub_cancel' hnu] using h

-- Checker controls: a missing legal edge, an out-of-range S edge, and a
-- forbidden supply tag must be rejected. The transition function itself
-- permits an eighth A; its absence is established by the checked graph.
example :
    let rs := Recaman.ThreeNonsuppliedData.rows
    let bad : Recaman.ThreeNonsuppliedData.Table := ⟨rs.size, fun i =>
      let row := rs.get i
      if i=1 then (row.1,row.2.1,0,row.2.2.2) else row⟩
    Recaman.ThreeNonsuppliedData.checkOne bad 1=false := by decide

example :
    let rs := Recaman.ThreeNonsuppliedData.rows
    let bad : Recaman.ThreeNonsuppliedData.Table := ⟨rs.size, fun i =>
      let row := rs.get i
      if i=0 then (row.1,rs.size,row.2.2.1,row.2.2.2) else row⟩
    Recaman.ThreeNonsuppliedData.checkOne bad 0=false := by decide

example :
    let rs := Recaman.ThreeNonsuppliedData.rows
    let bad : Recaman.ThreeNonsuppliedData.Table := ⟨rs.size, fun i =>
      let row := rs.get i
      if i=0 then (row.1,row.2.1,row.2.2.1,1) else row⟩
    Recaman.ThreeNonsuppliedData.checkOne bad 0=false := by decide

example : (Recaman.ThreeNonsuppliedData.stepA
    ⟨[false,true,true],7,12,2⟩ true).map (fun s => s.additions) = some 8 := by decide

-- Without BlockWord, SSAAA | AS gives an old P2 window with only one tail A
-- and one tail S, violating s≤2a−2. This is a hypothesis control, not a Q counterexample.
example : mass [false,false,true,true,true,true,false]=1 ∧
    areaW [false,false,true,true,true,true,false]=0 := by decide

theorem wordSupply_admitted (f : Nat → Bool) (n a b : Nat)
    {β : List Bool} (hβ : BlockWord β)
    (hseg : seg f 0 n = β ++ List.replicate a true) (hnb : n≤b) (hA : f b=true)
    (e : Bool) (he : if e then EndN f 0 b else ¬EndN f 0 b) :
    (if e then Recaman.ThreeNonsuppliedData.localSupply (seg f n (b-n)) ||
        Recaman.ThreeNonsuppliedData.oldSignature (seg f n (b-n))
      else !Recaman.ThreeNonsuppliedData.localSupply (seg f n (b-n)))=true := by
  cases e
  · cases hl : Recaman.ThreeNonsuppliedData.localSupply (seg f n (b-n))
    · rfl
    · have hloc := (localSupply_seg_iff f n b hnb hA).mp hl
      exact False.elim (he (end_mono f 0 n b (Nat.zero_le _) hloc))
  · obtain ⟨_,t,k,_,htk,hk,hF,hAr⟩ := he
    by_cases htn : n≤t
    · have hl := (localSupply_seg_iff f n b hnb hA).mpr
        ⟨hA,t,k,htn,htk,hk,hF,hAr⟩
      simp [hl]
    · have hwin : Win f t (b-t) := by
        have heq : b-t=k := by omega
        simpa only [heq] using (show Win f t k from ⟨hk,hF,hAr⟩)
      have ho := old_window_signature f n a t b hβ hseg (by omega) hnb hwin
      simp [ho]

noncomputable def actualQState (f : Nat → Bool) (n q k : Nat) :
    Recaman.ThreeNonsuppliedQData.State :=
  ⟨seg f n (q-n),seg f n (q-n+k),cN (fun u => f u=true ∧ ¬EndN f 0 u) q k⟩

theorem actualQState_zero (f : Nat → Bool) (n q : Nat) :
    actualQState f n q 0 = ⟨seg f n (q-n),seg f n (q-n),0⟩ := by
  simp [actualQState,cN]

theorem actualQState_deficit (f : Nat → Bool) (n q k : Nat) (hnq : n≤q)
    (hend : cN (EndN f 0) n (q-n)+1=cN (fun u => f u=false) n (q-n)) :
    mass (actualQState f n q k).root+1+
      ((actualQState f n q k).nonsupplied : Int)-mass (actualQState f n q k).word =
      (cN (fun u => f u=false) n (q-n+k) : Int) - (cN (EndN f 0) n (q-n+k) : Int) := by
  have hr := cN_walk f n (q-n)
  have hw := cN_walk f n (q-n+k)
  have hpr := addition_endable_partition f n (q-n)
  have hpw := addition_endable_partition f n (q-n+k)
  have hsplit := cN_add (fun u => f u=true ∧ ¬EndN f 0 u) n (q-n) k
  rw [Nat.add_sub_cancel' hnq] at hsplit
  simp only [actualQState,seg_mass]
  omega

theorem actualQState_S (f : Nat → Bool) (n q k : Nat) (hnq : n≤q)
    (hS : f (q+k)=false) (hdepth : -4≤mass (actualQState f n q (k+1)).word) :
    Recaman.ThreeNonsuppliedQData.stepS (actualQState f n q k) =
      some (actualQState f n q (k+1)) := by
  have han := cN_succ_neg (fun u => f u=true ∧ ¬EndN f 0 u) q k (by simp [hS])
  have hw : (actualQState f n q (k+1)).word = (actualQState f n q k).word++[false] := by
    simp only [actualQState]
    rw [show q-n+(k+1)=q-n+k+1 by omega,seg_succ,
      show n+(q-n+k)=q+k by omega,hS]
  have hd : -4≤mass ((actualQState f n q k).word++[false]) := by rwa [←hw]
  simp only [Recaman.ThreeNonsuppliedQData.stepS,if_pos hd]
  apply congrArg some
  simp only [actualQState,han] at hw ⊢
  rw [← hw]

theorem actualQState_A (f : Nat → Bool) (n a q k : Nat)
    {β : List Bool} (hβ : BlockWord β)
    (hseg : seg f 0 n = β ++ List.replicate a true) (hnq : n≤q)
    (hA : f (q+k)=true) (e : Bool)
    (he : if e then EndN f 0 (q+k) else ¬EndN f 0 (q+k))
    (hbudget : (actualQState f n q (k+1)).nonsupplied≤1)
    (hbalance : 1≤mass (actualQState f n q (k+1)).root+1+
      ((actualQState f n q (k+1)).nonsupplied : Int)-mass (actualQState f n q (k+1)).word) :
    Recaman.ThreeNonsuppliedQData.stepA (actualQState f n q k) e =
      some (actualQState f n q (k+1)) := by
  have han : cN (fun u => f u=true ∧ ¬EndN f 0 u) q (k+1) =
      cN (fun u => f u=true ∧ ¬EndN f 0 u) q k+(if e then 0 else 1) := by
    cases e
    · exact cN_succ_pos _ q k ⟨hA,he⟩
    · have he' : EndN f 0 (q+k) := by simpa using he
      have h := cN_succ_neg (fun u => f u=true ∧ ¬EndN f 0 u) q k (fun h => h.2 he')
      simpa using h
  have hw : (actualQState f n q (k+1)).word = (actualQState f n q k).word++[true] := by
    simp only [actualQState]
    rw [show q-n+(k+1)=q-n+k+1 by omega,seg_succ,
      show n+(q-n+k)=q+k by omega,hA]
  have hadmit : (if e then Recaman.ThreeNonsuppliedData.localSupply (actualQState f n q k).word ||
        Recaman.ThreeNonsuppliedData.oldSignature (actualQState f n q k).word
      else !Recaman.ThreeNonsuppliedData.localSupply (actualQState f n q k).word)=true := by
    have h := wordSupply_admitted f n a (q+k) hβ hseg (by omega) hA e he
    simpa only [actualQState,show q+k-n=q-n+k by omega] using h
  have hb : (actualQState f n q k).nonsupplied+(if e then 0 else 1)≤1 := by
    simpa only [actualQState,han] using hbudget
  have hd : 1≤mass (actualQState f n q k).root+1+
      ((actualQState f n q k).nonsupplied+(if e then 0 else 1) : Nat)-
      mass ((actualQState f n q k).word++[true]) := by
    rw [←hw]
    simpa only [actualQState,han] using hbalance
  have heval : Recaman.ThreeNonsuppliedQData.stepA (actualQState f n q k) e =
      some ⟨(actualQState f n q k).root,(actualQState f n q k).word++[true],
        (actualQState f n q k).nonsupplied+(if e then 0 else 1)⟩ := by
    push_cast at hd
    simp [Recaman.ThreeNonsuppliedQData.stepA,hadmit,hb,hd]
  rw [heval]
  apply congrArg some
  simp only [actualQState,han] at hw ⊢
  rw [←hw]

theorem three_nonsupplied_Q_state_member (f : Nat → Bool) (n a q K : Nat)
    {β : List Bool} (hβ : BlockWord β)
    (hseg : seg f 0 n = β ++ List.replicate a true) (hnq : n≤q)
    (hpos : ∀ j, 0<j → j≤q-n+K → cN (EndN f 0) n j+1≤cN (fun u => f u=false) n j)
    (hroot : cN (EndN f 0) n (q-n)+1=cN (fun u => f u=false) n (q-n))
    (haz : cN (fun u => f u=true ∧ ¬EndN f 0 u) n (q-n)≤3)
    (hay : cN (fun u => f u=true ∧ ¬EndN f 0 u) q K≤1)
    (hdepth : ∀ j, j≤q-n+K → -4≤mass (seg f n j)) :
    Recaman.ThreeNonsuppliedQData.Member Recaman.ThreeNonsuppliedQData.rows
      (actualQState f n q K) := by
  have hposz : ∀ j, 0<j → j≤q-n → cN (EndN f 0) n j+1≤cN (fun u => f u=false) n j := by
    intro j hj hjq; exact hpos j hj (by omega)
  have hw := three_nonsupplied_excursion_word f n a (q-n) hβ hseg hposz haz hroot
  have hmember : ∀ k, k≤K → Recaman.ThreeNonsuppliedQData.Member
      Recaman.ThreeNonsuppliedQData.rows (actualQState f n q k) := by
    intro k
    induction k with
    | zero =>
        intro _
        rw [actualQState_zero]
        exact Recaman.ThreeNonsuppliedQData.initial_member _ hw
    | succ k ih =>
        intro hk
        have hprev := ih (by omega)
        by_cases hS : f (q+k)=false
        · apply Recaman.ThreeNonsuppliedQData.member_stepS _
            Recaman.ThreeNonsuppliedQData.rows_verified _ _ hprev
          apply actualQState_S f n q k hnq hS
          exact hdepth _ (by omega)
        · have hA : f (q+k)=true := by cases h : f (q+k) <;> simp_all
          have hbud : (actualQState f n q (k+1)).nonsupplied≤1 := by
            have hc := count_prefix_le (fun u => f u=true ∧ ¬EndN f 0 u) q (k+1) K hk
            change cN (fun u => f u=true ∧ ¬EndN f 0 u) q (k+1)≤1
            omega
          have hbal : 1≤mass (actualQState f n q (k+1)).root+1+
              ((actualQState f n q (k+1)).nonsupplied : Int)-mass (actualQState f n q (k+1)).word := by
            rw [actualQState_deficit f n q (k+1) hnq hroot]
            have hp := hpos (q-n+(k+1)) (by omega) (by omega)
            omega
          by_cases he : EndN f 0 (q+k)
          · exact Recaman.ThreeNonsuppliedQData.member_stepA _
              Recaman.ThreeNonsuppliedQData.rows_verified _ _ true hprev
              (actualQState_A f n a q k hβ hseg hnq hA true he hbud hbal)
          · exact Recaman.ThreeNonsuppliedQData.member_stepA _
              Recaman.ThreeNonsuppliedQData.rows_verified _ _ false hprev
              (actualQState_A f n a q k hβ hseg hnq hA false he hbud hbal)
  exact hmember K (Nat.le_refl _)

theorem three_nonsupplied_area_of_depth_four (f : Nat → Bool) (n a q K : Nat)
    {β : List Bool} (hβ : BlockWord β)
    (hseg : seg f 0 n = β ++ List.replicate a true) (hnq : n≤q)
    (hpos : ∀ j, 0<j → j≤q-n+K → cN (EndN f 0) n j+1≤cN (fun u => f u=false) n j)
    (hroot : cN (EndN f 0) n (q-n)+1=cN (fun u => f u=false) n (q-n))
    (haz : cN (fun u => f u=true ∧ ¬EndN f 0 u) n (q-n)≤3)
    (hay : cN (fun u => f u=true ∧ ¬EndN f 0 u) q K≤1)
    (hdepth : ∀ j, j≤q-n+K → Fw f n-4≤Fw f (n+j))
    (hguard : Fw f (q+K)≤Fw f n) :
    1≤Ar f n (q-n+K)+((q-n+K : Nat) : Int)*(Fw f n-Fw f (q+K)+1) := by
  have hd : ∀ j, j≤q-n+K → -4≤mass (seg f n j) := by
    intro j hj
    rw [seg_mass]
    have h := hdepth j hj
    omega
  have hm := three_nonsupplied_Q_state_member f n a q K hβ hseg hnq hpos hroot haz hay hd
  have hg : mass (actualQState f n q K).word≤0 := by
    simp only [actualQState,seg_mass]
    rw [show n+(q-n+K)=q+K by omega]
    omega
  have harea := Recaman.ThreeNonsuppliedQData.member_area
    Recaman.ThreeNonsuppliedQData.rows Recaman.ThreeNonsuppliedQData.rows_verified _ hm hg
  simp only [actualQState,checked_wordArea_eq,←Ar_areaW,seg_length,seg_mass] at harea
  rw [show n+(q-n+K)=q+K by omega] at harea
  grind

theorem exists_minimum_visit (f : Nat → Bool) (n : Nat) : ∀ B : Nat,
    ∃ r, n≤r ∧ r≤n+B ∧ ∀ u, n≤u → u≤n+B → Fw f r≤Fw f u
  | 0 => by
      refine ⟨n,Nat.le_refl _,by omega,?_⟩
      intro u hu hu'
      have heq : u=n := by omega
      rw [heq]
      exact Int.le_refl _
  | B+1 => by
      obtain ⟨r,hnr,hrb,hmin⟩ := exists_minimum_visit f n B
      by_cases hlast : Fw f (n+B+1)≤Fw f r
      · refine ⟨n+B+1,by omega,by omega,?_⟩
        intro u hnu hub
        by_cases hu : u≤n+B
        · have hm := hmin u hnu hu; omega
        · have : u=n+B+1 := by omega
          simp [this]
      · refine ⟨r,hnr,by omega,?_⟩
        intro u hnu hub
        by_cases hu : u≤n+B
        · exact hmin u hnu hu
        · have : u=n+B+1 := by omega
          rw [this]; omega

/-- Q for at most three nonsupplied additions before q, with arbitrary
future length and depth. Deep future visits use the independent fresh-low
area lemma, rather than a finite-depth assumption on the final theorem. -/
theorem three_nonsupplied_area_nonnegative (f : Nat → Bool) (n a q K : Nat)
    {β : List Bool} (hβ : BlockWord β)
    (hseg : seg f 0 n = β ++ List.replicate a true) (hnq : n≤q)
    (hpos : ∀ j, 0<j → j≤q-n+K → cN (EndN f 0) n j+1≤cN (fun u => f u=false) n j)
    (hroot : cN (EndN f 0) n (q-n)+1=cN (fun u => f u=false) n (q-n))
    (haz : cN (fun u => f u=true ∧ ¬EndN f 0 u) n (q-n)≤3)
    (hay : cN (fun u => f u=true ∧ ¬EndN f 0 u) q K≤1)
    (hguard : Fw f (q+K)≤Fw f n) :
    0≤Ar f n (q-n+K)+((q-n+K : Nat) : Int)*(Fw f n-Fw f (q+K)+1) := by
  by_cases hdepth : ∀ j, j≤q-n+K → Fw f n-4≤Fw f (n+j)
  · have h := three_nonsupplied_area_of_depth_four f n a q K hβ hseg hnq hpos hroot haz hay hdepth hguard
    omega
  · obtain ⟨r,hnr,hrb,hmin⟩ := exists_minimum_visit f n (q-n+K)
    have hposz : ∀ j, 0<j → j≤q-n → cN (EndN f 0) n j+1≤cN (fun u => f u=false) n j := by
      intro j hj hjq; exact hpos j hj (by omega)
    have hqr : q≤r := by
      apply Classical.byContradiction
      intro hneg
      have hz := three_nonsupplied_excursion_depth_offset f n a (q-n) hβ hseg hposz haz hroot
        (r-n) (by omega)
      rw [Nat.add_sub_cancel' hnr] at hz
      apply hdepth
      intro j hj
      have hm := hmin (n+j) (by omega) (by omega)
      omega
    have harea := area_nonneg_of_fresh_low_visit f n a q r (q+K) hβ hseg hnq hqr
      (by omega) (Fw f r) rfl (by
        intro u hnu hub
        apply hmin u hnu
        omega) (by simpa using hay)
    simpa only [show q+K-n=q-n+K by omega] using harea

/-- Original-base deficit form of Q. Both z and y may have arbitrary length;
there is no depth hypothesis on the final statement. -/
theorem three_nonsupplied_area_from_zero (f : Nat → Bool) (n a q b : Nat)
    {β : List Bool} (hβ : BlockWord β)
    (hseg : seg f 0 n = β ++ List.replicate a true) (hnq : n≤q) (hqb : q≤b)
    (hzero : cN (EndN f 0) 0 n=cN (fun u => f u=false) 0 n)
    (hpos : ∀ u, n<u → u≤b → cN (EndN f 0) 0 u+1≤cN (fun u => f u=false) 0 u)
    (hroot : cN (EndN f 0) 0 q+1=cN (fun u => f u=false) 0 q)
    (haz : cN (fun u => f u=true ∧ ¬EndN f 0 u) n (q-n)≤3)
    (hay : cN (fun u => f u=true ∧ ¬EndN f 0 u) q (b-q)≤1)
    (hguard : Fw f b≤Fw f n) :
    0≤Ar f n (b-n)+((b-n : Nat) : Int)*(Fw f n-Fw f b+1) := by
  have hrel : ∀ j, 0<j → j≤q-n+(b-q) →
      cN (EndN f 0) n j+1≤cN (fun u => f u=false) n j := by
    intro j hj hjb
    have hp := hpos (n+j) (by omega) (by omega)
    have he := cN_add (EndN f 0) 0 n j
    have hs := cN_add (fun u => f u=false) 0 n j
    simp only [Nat.zero_add] at he hs
    omega
  have hr : cN (EndN f 0) n (q-n)+1=cN (fun u => f u=false) n (q-n) := by
    have he := cN_add (EndN f 0) 0 n (q-n)
    have hs := cN_add (fun u => f u=false) 0 n (q-n)
    rw [Nat.add_sub_cancel' hnq] at he hs
    simp only [Nat.zero_add] at he hs
    omega
  have h := three_nonsupplied_area_nonnegative f n a q (b-q) hβ hseg hnq hrel hr haz hay
    (by simpa only [Nat.add_sub_cancel' hqb] using hguard)
  simpa only [Nat.add_sub_cancel' hqb,show q-n+(b-q)=b-n by omega] using h

/-- The a_z≤3 subcase of C1: an older P2 start is impossible under the
actual positive-deficit and nonsupplied-A budgets. This does not cover a_z≥4. -/
theorem three_nonsupplied_no_old_window (f : Nat → Bool) (n a q b t : Nat)
    {β : List Bool} (hβ : BlockWord β)
    (hseg : seg f 0 n = β ++ List.replicate a true) (hnq : n≤q) (hqb : q≤b)
    (hzero : cN (EndN f 0) 0 n=cN (fun u => f u=false) 0 n)
    (hpos : ∀ u, n<u → u≤b → cN (EndN f 0) 0 u+1≤cN (fun u => f u=false) 0 u)
    (hroot : cN (EndN f 0) 0 q+1=cN (fun u => f u=false) 0 q)
    (haz : cN (fun u => f u=true ∧ ¬EndN f 0 u) n (q-n)≤3)
    (hay : cN (fun u => f u=true ∧ ¬EndN f 0 u) q (b-q)≤1)
    (htn : t<n) : ¬Win f t (b-t) := by
  intro hwin
  have hp := block_suffix_positive_walk f 0 n a hβ hseg t (Nat.zero_le _) (by omega)
  simp only [Nat.zero_add] at hp
  have hlevel := hwin.2.1
  rw [show t+(b-t)=b by omega] at hlevel
  have hguard : Fw f b≤Fw f n := by omega
  have harea := three_nonsupplied_area_from_zero f n a q b hβ hseg hnq hqb hzero hpos hroot haz hay hguard
  have hsplit := area_split_at f t n b (by omega) (by omega)
  have heq : Fw f n-Fw f t=Fw f n-Fw f b+1 := by omega
  rw [heq] at hsplit
  have hzeroAr := hwin.2.2
  omega

-- A positive control for the second checker: full words of length21 are
-- legal transition outputs. The observed maximum20 is supplied by closure,
-- rather than imposed as a cutoff in the transition function.
example : (Recaman.ThreeNonsuppliedQData.stepS
    ⟨[false],List.replicate 20 true,0⟩).map (fun s => s.word.length)=some 21 := by decide

/-- Before the next supplied addition, an S-only gap has length at most
twice the number of all A clocks already in the tail minus two. The bound
depends on the present word, not on a fixed length, depth or A-budget cutoff. -/
theorem supplied_after_S_gap_bound (f : Nat → Bool) (n a b j : Nat)
    {β : List Bool} (hβ : BlockWord β)
    (hseg : seg f 0 n = β ++ List.replicate a true) (hnb : n<b)
    (hS : ∀ u, b≤u → u<b+j → f u=false) (he : EndN f 0 (b+j)) :
    (j : Int)≤2*ones (seg f n (b-n))-2 := by
  have hword : seg f n (b+j-n)=seg f n (b-n)++List.replicate j false := by
    have h := seg_add f n (b-n) j
    rw [show n+(b-n)=b by omega,seg_false f b j hS] at h
    simpa only [show b-n+j=b+j-n by omega] using h
  have hrep : ones (List.replicate j false)=0 := by
    have hm := mass_eq (List.replicate j false)
    rw [mass_rep_false,List.length_replicate] at hm
    omega
  have hAcount : ones (seg f n (b+j-n))=ones (seg f n (b-n)) := by
    rw [hword,ones_append,hrep]; omega
  obtain ⟨_,t,k,_,htk,hk,hF,hAr⟩ := he
  by_cases htn : t<n
  · have hwin : Win f t (b+j-t) := by
      have heq : b+j-t=k := by omega
      simpa only [heq] using (show Win f t k from ⟨hk,hF,hAr⟩)
    have hc := old_window_count_barrier f n a t (b+j) hβ hseg htn (by omega) hwin
    rw [hAcount] at hc
    have hb := ones_bounds (seg f n (b-n))
    rw [seg_length] at hb
    omega
  · by_cases htb : b≤t
    · have hdown := fw_false_run f t k (fun u htu huk => hS u (by omega) (by omega))
      omega
    · have hdrop : (seg f n (b-n)).drop (t-n)=seg f t (b-t) := by
        have h := seg_drop f n (b-n) (t-n) (by omega)
        simpa only [show n+(t-n)=t by omega,show b-n-(t-n)=b-t by omega] using h
      have hle := ones_drop_le (seg f n (b-n)) (t-n)
      rw [hdrop] at hle
      have hm := mass_eq (seg f t (b-t))
      rw [seg_mass,show t+(b-t)=b by omega] at hm
      have hb := ones_bounds (seg f t (b-t))
      have hdown := fw_false_run f b j hS
      rw [htk] at hF
      have hmass : (j : Int)+1≤ones (seg f n (b-n)) := by omega
      omega

def tail_S5A3S4A4SA3 : List Bool :=
  List.replicate 5 false ++ List.replicate 3 true ++ List.replicate 4 false ++
    List.replicate 4 true ++ [false] ++ List.replicate 3 true

theorem tail_S5A3S4A4SA3_no_supply_check :
    ((List.range 19).all fun j =>
      !(Recaman.ThreeNonsuppliedData.localSupply (tail_S5A3S4A4SA3++List.replicate j false) ||
        Recaman.ThreeNonsuppliedData.oldSignature (tail_S5A3S4A4SA3++List.replicate j false)))=true := by decide

/-- This actual twenty-clock tail cannot produce any further A if no
additional nonsupplied A is available. The future length K is arbitrary;
the nineteen checks concern the first possible supplied A, not a K cutoff. -/
theorem no_additions_after_S5A3S4A4SA3 (f : Nat → Bool) (n a b K : Nat)
    {β : List Bool} (hβ : BlockWord β)
    (hseg : seg f 0 n = β ++ List.replicate a true) (hnb : n<b)
    (hword : seg f n (b-n)=tail_S5A3S4A4SA3)
    (hfree : cN (fun u => f u=true ∧ ¬EndN f 0 u) b K=0) :
    cN (fun u => f u=true) b K=0 := by
  have hall : ∀ j, j<K → f (b+j)=false := by
    intro j
    induction j using Nat.strongRecOn with
    | ind j ih =>
      intro hjK
      cases hA : f (b+j)
      · rfl
      · have hnot := not_of_cN_zero (fun u => f u=true ∧ ¬EndN f 0 u) b K hfree
          (b+j) (by omega) (by omega)
        have he : EndN f 0 (b+j) := by
          apply Classical.byContradiction
          intro hn
          exact hnot ⟨hA,hn⟩
        have hgap : ∀ u, b≤u → u<b+j → f u=false := by
          intro u hbu huj
          have h := ih (u-b) (by omega) (by omega)
          simpa only [Nat.add_sub_cancel' hbu] using h
        have hbound := supplied_after_S_gap_bound f n a b j hβ hseg hnb hgap he
        rw [hword] at hbound
        have hones : ones tail_S5A3S4A4SA3=10 := by decide
        rw [hones] at hbound
        have hj19 : j<19 := by omega
        have hw : seg f n (b+j-n)=tail_S5A3S4A4SA3++List.replicate j false := by
          have h := seg_add f n (b-n) j
          rw [show n+(b-n)=b by omega,seg_false f b j hgap,hword] at h
          simpa only [show b-n+j=b+j-n by omega] using h
        have hadmit := wordSupply_admitted f n a (b+j) hβ hseg (by omega) hA true he
        change (Recaman.ThreeNonsuppliedData.localSupply (seg f n (b+j-n)) ||
          Recaman.ThreeNonsuppliedData.oldSignature (seg f n (b+j-n)))=true at hadmit
        rw [hw] at hadmit
        have hc := List.all_eq_true.mp tail_S5A3S4A4SA3_no_supply_check j (List.mem_range.mpr hj19)
        simp [hadmit] at hc
  apply cN_zero_of
  intro u hbu huend
  have hf := hall (u-b) (by omega)
  rw [Nat.add_sub_cancel' hbu] at hf
  simp [hf]

/-! Integer-clock adapters for the completed C1 setting. These only translate
the already-proved natural-clock result; they are not separate research claims. -/

open Classical in
theorem nonsupplied_count_shift (e : Int → Bool) (p : Int) (s m : Nat) :
    countP (fun c => e c=true ∧ ¬Endable e p c) (p+(s : Int)) m =
      cN (fun i => e (p+(i : Int))=true ∧
        ¬EndN (fun j => e (p+(j : Int))) 0 i) s m := by
  classical
  rw [countP_cN (fun c => e c=true ∧ ¬Endable e p c) p (p+(s : Int)) s rfl m]
  apply cN_congr
  intro i _ _
  rw [endable_iff e p p (p+(i : Int)) 0 i (by simp) rfl]

theorem endableCount_shift (e : Int → Bool) (p : Int) (m : Nat) :
    endableCount e p m = cN (EndN (fun i => e (p+(i : Int))) 0) 0 m := by
  classical
  have h := @countP_cN (Endable e p) (classDec _) p p 0 (by simp) m
  change @countP (Endable e p) (classDec _) p m = _
  rw [h]
  apply cN_congr
  intro i _ _
  exact endable_iff e p p (p+(i : Int)) 0 i (by simp) rfl

theorem subtractionCount_shift (e : Int → Bool) (p : Int) (m : Nat) :
    subtractionCount e p m = cN (fun i => e (p+(i : Int))=false) 0 m := by
  exact countP_cN (fun c => e c=false) p p 0 (by simp) m

open Classical in
theorem three_nonsupplied_area_int (e : Int → Bool) (p : Int) (n a q b : Nat)
    {β : List Bool} (hβ : BlockWord β)
    (hseg : segment e p n = β ++ List.replicate a true) (hnq : n≤q) (hqb : q≤b)
    (hzero : endableCount e p n=subtractionCount e p n)
    (hpos : ∀ u, n<u → u≤b → endableCount e p u+1≤subtractionCount e p u)
    (hroot : endableCount e p q+1=subtractionCount e p q)
    (haz : countP (fun c => e c=true ∧ ¬Endable e p c) (p+(n : Int)) (q-n)≤3)
    (hay : countP (fun c => e c=true ∧ ¬Endable e p c) (p+(q : Int)) (b-q)≤1)
    (hguard : Fw (fun i => e (p+(i : Int))) b≤Fw (fun i => e (p+(i : Int))) n) :
    0≤Ar (fun i => e (p+(i : Int))) n (b-n)+((b-n : Nat) : Int)*
      (Fw (fun i => e (p+(i : Int))) n-Fw (fun i => e (p+(i : Int))) b+1) := by
  classical
  rw [segment_seg e p p 0 (by simp)] at hseg
  simp only [endableCount_shift,subtractionCount_shift] at hzero hpos hroot
  rw [nonsupplied_count_shift] at haz hay
  exact three_nonsupplied_area_from_zero (fun i => e (p+(i : Int))) n a q b
    hβ hseg hnq hqb hzero hpos hroot haz hay hguard

end Recaman.BlockSuffixPositivity
