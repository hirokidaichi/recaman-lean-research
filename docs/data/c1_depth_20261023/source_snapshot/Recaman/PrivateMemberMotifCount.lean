import Recaman.NewestMemberMotifCount

namespace Recaman.PrivateMemberMotifCount

/-! R' of H-20261003-01: `newest_motif_count` without `hnew` (owners may be newer than `v`).

Counting (`adm_length_le`, `private_motif_count_le`): as in `newest_motif_count`, an AAS-owned
subtraction `s` of the window gives the additions `s+1, s+2, s+3` and a w1-owned one gives `s+5`,
all distinct; now only those older than `v` count. The loss is at most 4 (an AAS-owned subtraction
at `v-1` loses 3, at `v-2` loses 2, these exclude each other, `v-3` cannot be AAS-owned; at most
one w1-owned subtraction lies in `[v-5, v-2]`), and `s ↦ s+1` injects the w1-owned subtractions into
the AAS-owned ones plus `own v`. Hence `L ≤ 15`.

Finite part (`check7`, `check11`, `check15`, by `decide`): the windows of length 7, 11, 15 that pass the
abstract test `admB` (all bits recorded by `MotifOwner`) are exactly `S A A A A S S` and
`S S A A A A A A S S S`, each owning its oldest letter (`private_motif_window`). The second one
really occurs (`eleven_occurs`, `not_three_or_seven`): `MotifOwner` does not record the newest
letter `b - 1` of a w1 owner. With that letter required to be a subtraction (the full w1 word
`S A A A A S S`), only `AAS` and `S A A A A S S` remain (`private_motif_count`). -/

open LeadingRunSupply (P2 past ones mass moment p2_count_identities)
open SuffixHallOwnerMap (OwnerMap nodup_map_of_inj)
open NewestMemberMotifCount (MotifOwner length_filter_partition ones_eq_filter)

/-! ## The abstract window predicate

A newest-first word `w` (letter `w[i]` at clock `v - (i+1)`, `true` = addition) and the offset `j`
of `own v`. Letters newer than the window (offset `i - d < 0`) are not constrained, except that the
clock `v` itself is an addition. -/

/-- The letter `d` clocks newer than offset `i`; `true` when it lies outside the window. -/
def getA (w : List Bool) (i d : Nat) : Bool := if d ≤ i then w.getD (i - d) true else true

/-- The subtraction at offset `i` is owned by an AAS member at clock `clk i + 3` (which is not `v`). -/
def aasB (w : List Bool) (i : Nat) : Bool :=
  i != 2 && getA w i 1 && getA w i 2 && getA w i 3

/-- The bits recorded by `MotifOwner` for a w1 owner at clock `clk i + 7` (which is not `v`) of the
subtraction at offset `i`; its AAS sibling at clock `clk i + 4` owns offset `i - 1`, and this sibling
is `v` exactly when `i = 3`. -/
def w1Base (w : List Bool) (j i : Nat) : Bool :=
  i != 6 && decide (1 ≤ i) && !(w.getD (i-1) true) && getA w i 2 && getA w i 3 && getA w i 4 &&
  getA w i 5 && getA w i 7 && (if i = 3 then j == 2 else j != i - 1)

/-- The newest letter `clk i + 6` of a w1 owner is a subtraction (not recorded by `MotifOwner`). -/
def w1Extra (w : List Bool) (i : Nat) : Bool :=
  i != 5 && (if 6 ≤ i then !(w.getD (i-6) true) else true)

def w1B (full : Bool) (w : List Bool) (j i : Nat) : Bool := w1Base w j i && (!full || w1Extra w i)

/-- Every subtraction of the window other than `own v` (offset `j`) is AAS-owned or w1-owned. -/
def admB (full : Bool) (w : List Bool) (j : Nat) : Bool :=
  decide (j < w.length) && !(w.getD j true) &&
  (List.range w.length).all (fun i => w.getD i true || i == j || aasB w i || w1B full w j i)

theorem getA_spec {w : List Bool} {i d : Nat} (h : getA w i d = true) (hd : d ≤ i) :
    w.getD (i - d) true = true := by
  simpa [getA, hd] using h

theorem aasB_spec {w : List Bool} {i : Nat} (h : aasB w i = true) :
    i ≠ 2 ∧ ∀ d, 1 ≤ d → d ≤ 3 → d ≤ i → w.getD (i - d) true = true := by
  simp only [aasB, Bool.and_eq_true, bne_iff_ne, ne_eq, and_assoc] at h
  obtain ⟨h2, h1, h2', h3⟩ := h
  refine ⟨h2, fun d hd1 hd3 hdi => ?_⟩
  rcases (by omega : d = 1 ∨ d = 2 ∨ d = 3) with rfl | rfl | rfl
  · exact getA_spec h1 hdi
  · exact getA_spec h2' hdi
  · exact getA_spec h3 hdi

theorem w1B_spec {full : Bool} {w : List Bool} {j i : Nat} (h : w1B full w j i = true) :
    i ≠ 6 ∧ 1 ≤ i ∧ w.getD (i-1) true = false ∧
    (∀ d, 2 ≤ d → d ≤ 5 → d ≤ i → w.getD (i - d) true = true) ∧
    (i = 3 → j = 2) ∧ (i ≠ 3 → j ≠ i - 1) := by
  simp only [w1B, w1Base, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq,
    Bool.not_eq_true', and_assoc] at h
  obtain ⟨h6, h1, hS, g2, g3, g4, g5, _, hj, _⟩ := h
  refine ⟨h6, h1, hS, fun d hd2 hd5 hdi => ?_, fun h3 => ?_, fun h3 => ?_⟩
  · rcases (by omega : d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5) with rfl | rfl | rfl | rfl
    · exact getA_spec g2 hdi
    · exact getA_spec g3 hdi
    · exact getA_spec g4 hdi
    · exact getA_spec g5 hdi
  · rw [if_pos h3] at hj; simpa using hj
  · rw [if_neg h3] at hj; simpa using hj

/-- A nodup list whose elements are pairwise equal has length at most one. -/
theorem length_le_one_of_eq {α : Type} (l : List α) (hl : l.Nodup)
    (h : ∀ x ∈ l, ∀ y ∈ l, x = y) : l.length ≤ 1 := by
  match l, hl, h with
  | [], _, _ => simp
  | [_], _, _ => simp
  | a :: b :: t, hl, h =>
    exfalso
    have hab := h a (by simp) b (by simp)
    subst hab
    simp at hl

/-- Filtering out at most one element. -/
theorem length_le_filter_succ (l : List Nat) (p : Nat → Bool) (hl : l.Nodup)
    (h : ∀ x ∈ l, ∀ y ∈ l, p x = false → p y = false → x = y) :
    l.length ≤ (l.filter p).length + 1 := by
  have hpart := length_filter_partition l p
  have h1 : (l.filter (fun x => !p x)).length ≤ 1 := by
    apply length_le_one_of_eq _ (hl.filter _)
    intro x hx y hy
    have hx' := List.mem_filter.mp hx
    have hy' := List.mem_filter.mp hy
    exact h x hx'.1 y hy'.1 (by simpa using hx'.2) (by simpa using hy'.2)
  omega

theorem eq_map_getD (w : List Bool) : w = (List.range w.length).map (fun i => w.getD i true) := by
  apply List.ext_getElem
  · simp
  · intro n h1 h2; simp [h1]

/-- Counting: an admissible P2 window has length at most 15. -/
theorem adm_length_le (full : Bool) (w : List Bool) (j : Nat) (hP : P2 w)
    (hadm : admB full w j = true) : w.length ≤ 15 := by
  simp only [admB, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', List.all_eq_true,
    List.mem_range] at hadm
  obtain ⟨⟨hjL, hjS⟩, hall⟩ := hadm
  let L := w.length
  let f : Nat → Bool := fun i => w.getD i true
  let Sv := (List.range L).filter (fun i => !f i)
  let T := Sv.filter (fun i => i != j)
  let TA := T.filter (aasB w)
  let TW := T.filter (fun i => !aasB w i)
  let Av := (List.range L).filter f
  have hSvnodup : Sv.Nodup := List.nodup_range.filter _
  have hTnodup : T.Nodup := hSvnodup.filter _
  have hTAnodup : TA.Nodup := hTnodup.filter _
  have hTWnodup : TW.Nodup := hTnodup.filter _
  have memT : ∀ i ∈ T, i < L ∧ f i = false ∧ i ≠ j := by
    intro i hi
    have h := List.mem_filter.mp hi
    have h' := List.mem_filter.mp h.1
    refine ⟨List.mem_range.mp h'.1, by simpa using h'.2, by simpa using h.2⟩
  have TAsub : ∀ i ∈ TA, i ∈ T := fun i hi => (List.mem_filter.mp hi).1
  have TWsub : ∀ i ∈ TW, i ∈ T := fun i hi => (List.mem_filter.mp hi).1
  have inT : ∀ i, i < L → f i = false → i ≠ j → i ∈ T := fun i h1 h2 h3 =>
    List.mem_filter.mpr ⟨List.mem_filter.mpr ⟨List.mem_range.mpr h1, by simp [h2]⟩, by simpa using h3⟩
  have factA : ∀ i ∈ TA, i ≠ 2 ∧ ∀ d, 1 ≤ d → d ≤ 3 → d ≤ i → f (i - d) = true := by
    intro i hi
    exact aasB_spec (List.mem_filter.mp hi).2
  have factW : ∀ i ∈ TW, i ≠ 6 ∧ 1 ≤ i ∧ f (i-1) = false ∧
      (∀ d, 2 ≤ d → d ≤ 5 → d ≤ i → f (i - d) = true) ∧ ((i - 1) ∈ TA ∨ i - 1 = j) := by
    intro i hi
    have h := List.mem_filter.mp hi
    have hnA : aasB w i = false := by simpa using h.2
    obtain ⟨hiL, hS, hne⟩ := memT i h.1
    have hw : w1B full w j i = true := by
      have := hall i hiL
      have hS' : w.getD i true = false := hS
      have hne' : (i == j) = false := by simpa using hne
      rw [hS', hne', hnA] at this
      simpa using this
    obtain ⟨h6, h1, hS1, hA, hj3, hjn⟩ := w1B_spec hw
    refine ⟨h6, h1, hS1, hA, ?_⟩
    by_cases h3 : i = 3
    · right; have := hj3 h3; omega
    · left
      have hT1 : (i - 1) ∈ T := inT (i - 1) (by omega) hS1 (fun h => hjn h3 h.symm)
      apply List.mem_filter.mpr
      refine ⟨hT1, ?_⟩
      have h' := hall (i - 1) (by omega)
      have hne1 : (i - 1 == j) = false := by simpa using (fun h => hjn h3 h.symm)
      rw [hS1, hne1] at h'
      simp only [Bool.false_or, Bool.or_eq_true] at h'
      rcases h' with h' | h'
      · exact h'
      · exfalso
        obtain ⟨_, h1', hS2, _⟩ := w1B_spec h'
        have := hA 2 (Nat.le_refl _) (by omega) (by omega)
        have e : i - 1 - 1 = i - 2 := by omega
        rw [e] at hS2
        have this' : w.getD (i - 2) true = true := this
        rw [hS2] at this'
        exact absurd this' (by decide)
  -- an S offset is not an A offset
  have notA : ∀ i ∈ T, ∀ k, f k = true → i ≠ k := by
    intro i hi k hk heq
    subst heq
    rw [(memT i hi).2.1] at hk
    exact absurd hk (by decide)
  -- the additions generated inside the window
  let A1 := (TA.filter (fun i => decide (1 ≤ i))).map (fun i => i - 1)
  let A2 := (TA.filter (fun i => decide (2 ≤ i))).map (fun i => i - 2)
  let A3 := (TA.filter (fun i => decide (3 ≤ i))).map (fun i => i - 3)
  let W5 := (TW.filter (fun i => decide (5 ≤ i))).map (fun i => i - 5)
  let Bl := A1 ++ A2 ++ A3 ++ W5
  have memF : ∀ (l : List Nat) (a i : Nat), i ∈ l.filter (fun i => decide (a ≤ i)) → i ∈ l ∧ a ≤ i :=
    fun l a i hi => by
      have h := List.mem_filter.mp hi
      exact ⟨h.1, by simpa using h.2⟩
  have inAv : ∀ k, k < L → f k = true → k ∈ Av := fun k hk he =>
    List.mem_filter.mpr ⟨List.mem_range.mpr hk, he⟩
  have hBsub : Bl ⊆ Av := by
    intro k hk
    simp only [Bl, A1, A2, A3, W5, List.mem_append, List.mem_map] at hk
    rcases hk with ((⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩
    · obtain ⟨hi, ha⟩ := memF _ _ _ hi
      have hiL := (memT i (TAsub i hi)).1
      exact inAv _ (by omega) ((factA i hi).2 1 (Nat.le_refl _) (by omega) ha)
    · obtain ⟨hi, ha⟩ := memF _ _ _ hi
      have hiL := (memT i (TAsub i hi)).1
      exact inAv _ (by omega) ((factA i hi).2 2 (by omega) (by omega) ha)
    · obtain ⟨hi, ha⟩ := memF _ _ _ hi
      have hiL := (memT i (TAsub i hi)).1
      exact inAv _ (by omega) ((factA i hi).2 3 (by omega) (Nat.le_refl _) ha)
    · obtain ⟨hi, ha⟩ := memF _ _ _ hi
      have hiL := (memT i (TWsub i hi)).1
      exact inAv _ (by omega) ((factW i hi).2.2.2.1 5 (by omega) (Nat.le_refl _) ha)
  have shiftNodup : ∀ (d : Nat) (l : List Nat), l.Nodup →
      ((l.filter (fun i => decide (d ≤ i))).map (fun i => i - d)).Nodup :=
    fun d l hl => nodup_map_of_inj _ _ (hl.filter _) (fun a ha b hb h => by
      have := (memF l d a ha).2; have := (memF l d b hb).2; omega)
  -- i - a = i' - b with a < b forces the S offset i to be an A offset of i'
  have dAA : ∀ (a b : Nat), a < b → b ≤ 3 → ∀ i ∈ TA, ∀ i' ∈ TA, a ≤ i → b ≤ i' → i - a ≠ i' - b := by
    intro a b hab hb3 i hi i' hi' ha hb heq
    exact notA i (TAsub i hi) (i' - (b - a))
      ((factA i' hi').2 (b - a) (by omega) (by omega) (by omega)) (by omega)
  have dAW : ∀ (a : Nat), 1 ≤ a → a ≤ 3 → ∀ i ∈ TA, ∀ i' ∈ TW, a ≤ i → 5 ≤ i' → i - a ≠ i' - 5 := by
    intro a ha1 ha3 i hi i' hi' ha hb heq
    exact notA i (TAsub i hi) (i' - (5 - a))
      ((factW i' hi').2.2.2.1 (5 - a) (by omega) (by omega) (by omega)) (by omega)
  have hBnodup : Bl.Nodup := by
    simp only [Bl]
    rw [List.nodup_append, List.nodup_append, List.nodup_append]
    refine ⟨⟨⟨shiftNodup 1 TA hTAnodup, shiftNodup 2 TA hTAnodup, ?_⟩,
      shiftNodup 3 TA hTAnodup, ?_⟩, shiftNodup 5 TW hTWnodup, ?_⟩
    · intro x hx y hy
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      obtain ⟨i', hi', rfl⟩ := List.mem_map.mp hy
      obtain ⟨hi, ha⟩ := memF _ _ _ hi
      obtain ⟨hi', hb⟩ := memF _ _ _ hi'
      exact dAA 1 2 (by omega) (by omega) i hi i' hi' ha hb
    · intro x hx y hy
      obtain ⟨i', hi', rfl⟩ := List.mem_map.mp hy
      obtain ⟨hi', hb⟩ := memF _ _ _ hi'
      rcases List.mem_append.mp hx with hx | hx
      · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
        obtain ⟨hi, ha⟩ := memF _ _ _ hi
        exact dAA 1 3 (by omega) (Nat.le_refl _) i hi i' hi' ha hb
      · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
        obtain ⟨hi, ha⟩ := memF _ _ _ hi
        exact dAA 2 3 (by omega) (Nat.le_refl _) i hi i' hi' ha hb
    · intro x hx y hy
      obtain ⟨i', hi', rfl⟩ := List.mem_map.mp hy
      obtain ⟨hi', hb⟩ := memF _ _ _ hi'
      rcases List.mem_append.mp hx with hx | hx
      · rcases List.mem_append.mp hx with hx | hx
        · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
          obtain ⟨hi, ha⟩ := memF _ _ _ hi
          exact dAW 1 (Nat.le_refl _) (by omega) i hi i' hi' ha hb
        · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
          obtain ⟨hi, ha⟩ := memF _ _ _ hi
          exact dAW 2 (by omega) (by omega) i hi i' hi' ha hb
      · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
        obtain ⟨hi, ha⟩ := memF _ _ _ hi
        exact dAW 3 (by omega) (Nat.le_refl _) i hi i' hi' ha hb
  have hBle : Bl.length ≤ Av.length := hBnodup.length_le_of_subset hBsub
  -- boundary losses: at most one offset of each kind is too new
  have lossA1 : TA.length ≤ (TA.filter (fun i => decide (1 ≤ i))).length + 1 := by
    apply length_le_filter_succ _ _ hTAnodup
    intro x _ y _ hx hy
    simp only [decide_eq_false_iff_not] at hx hy
    omega
  have exclA01 : ¬ (0 ∈ TA ∧ 1 ∈ TA) := by
    rintro ⟨h0, h1⟩
    have := (factA 1 h1).2 1 (Nat.le_refl _) (by omega) (Nat.le_refl _)
    exact notA 0 (TAsub 0 h0) (1 - 1) this rfl
  have lossA2 : TA.length ≤ (TA.filter (fun i => decide (2 ≤ i))).length + 1 := by
    apply length_le_filter_succ _ _ hTAnodup
    intro x hx y hy hx' hy'
    simp only [decide_eq_false_iff_not] at hx' hy'
    rcases (by omega : x = 0 ∨ x = 1) with rfl | rfl <;>
      rcases (by omega : y = 0 ∨ y = 1) with rfl | rfl
    · rfl
    · exact absurd ⟨hx, hy⟩ exclA01
    · exact absurd ⟨hy, hx⟩ exclA01
    · rfl
  have lossA3 : TA.length ≤ (TA.filter (fun i => decide (3 ≤ i))).length + 1 := by
    apply length_le_filter_succ _ _ hTAnodup
    intro x hx y hy hx' hy'
    simp only [decide_eq_false_iff_not] at hx' hy'
    have hx2 := (factA x hx).1
    have hy2 := (factA y hy).1
    rcases (by omega : x = 0 ∨ x = 1) with rfl | rfl <;>
      rcases (by omega : y = 0 ∨ y = 1) with rfl | rfl
    · rfl
    · exact absurd ⟨hx, hy⟩ exclA01
    · exact absurd ⟨hy, hx⟩ exclA01
    · rfl
  have lossW : TW.length ≤ (TW.filter (fun i => decide (5 ≤ i))).length + 1 := by
    apply length_le_filter_succ _ _ hTWnodup
    -- two w1-owned offsets below 5 coincide
    have key : ∀ x ∈ TW, ∀ y ∈ TW, x < y → y < 5 → False := by
      intro x hx y hy hxy hy5
      obtain ⟨_, hx1, hxS, _⟩ := factW x hx
      obtain ⟨_, _, _, hyA, _⟩ := factW y hy
      by_cases hyx : y = x + 1
      · have := hyA 2 (Nat.le_refl _) (by omega) (by omega)
        have e : y - 2 = x - 1 := by omega
        rw [e, hxS] at this
        exact absurd this (by decide)
      · have := hyA (y - x) (by omega) (by omega) (by omega)
        exact notA x (TWsub x hx) (y - (y - x)) this (by omega)
    intro x hx y hy hx' hy'
    simp only [decide_eq_false_iff_not] at hx' hy'
    rcases Nat.lt_trichotomy x y with h | h | h
    · exact (key x hx y hy h (by omega)).elim
    · exact h
    · exact (key y hy x hx h (by omega)).elim
  have hBlen : Bl.length = (TA.filter (fun i => decide (1 ≤ i))).length +
      (TA.filter (fun i => decide (2 ≤ i))).length + (TA.filter (fun i => decide (3 ≤ i))).length +
      (TW.filter (fun i => decide (5 ≤ i))).length := by
    simp [Bl, A1, A2, A3, W5]; omega
  -- w1-owned offsets inject into AAS-owned ones and `j`
  have hWA : TW.length ≤ TA.length + 1 := by
    have hsub : TW.map (fun i => i - 1) ⊆ TA ++ [j] := by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      rcases (factW i hi).2.2.2.2 with h | h
      · exact List.mem_append_left _ h
      · rw [h]; simp
    have hnd : (TW.map (fun i => i - 1)).Nodup :=
      nodup_map_of_inj _ _ hTWnodup (fun a ha b hb h => by
        have := (factW a ha).2.1; have := (factW b hb).2.1; omega)
    have := hnd.length_le_of_subset hsub
    simpa using this
  have hpart : TA.length + TW.length = T.length := length_filter_partition T (aasB w)
  -- counting the window
  have hAvS : Av.length + Sv.length = L := by
    have := length_filter_partition (List.range L) f
    simpa [Av, Sv] using this
  have hones : ones w = Av.length := by
    have h1 := ones_eq_filter f L
    rw [← eq_map_getD w] at h1
    exact h1
  have hTS : T.length + 1 = Sv.length := by
    have hpS := length_filter_partition Sv (fun i => i != j)
    have hjmem : j ∈ Sv.filter (fun i => !(i != j)) := by
      apply List.mem_filter.mpr
      refine ⟨List.mem_filter.mpr ⟨List.mem_range.mpr hjL, by
        show (!w.getD j true) = true
        rw [hjS]; rfl⟩, by simp⟩
    have hone : (Sv.filter (fun i => !(i != j))).length = 1 := by
      have h1 : (Sv.filter (fun i => !(i != j))).length ≤ 1 := by
        apply length_le_one_of_eq _ (hSvnodup.filter _)
        intro x hx y hy
        have hx' := (List.mem_filter.mp hx).2
        have hy' := (List.mem_filter.mp hy).2
        simp at hx' hy'
        omega
      have h2 := List.length_pos_of_mem hjmem
      omega
    simp only [T]; omega
  have hc := p2_count_identities w hP
  rw [hones] at hc
  obtain ⟨hL, -, hev⟩ := hc
  have hLL : (L : Int) = w.length := rfl
  omega

/-! ## Finite check of the windows of length 7, 11, 15 -/

def allWords : Nat → List (List Bool)
  | 0 => [[]]
  | n+1 => (allWords n).flatMap (fun w => [true :: w, false :: w])

theorem mem_allWords (w : List Bool) : w ∈ allWords w.length := by
  induction w with
  | nil => simp [allWords]
  | cons b w ih =>
    simp only [allWords, List.length_cons, List.mem_flatMap]
    exact ⟨w, ih, by cases b <;> simp⟩

def p2B (w : List Bool) : Bool := mass w == 1 && moment w == 0

theorem p2B_of_P2 (w : List Bool) (h : P2 w) : p2B w = true := by
  obtain ⟨h1, h2⟩ := h
  simp [p2B, h1, h2]

def checkL (L : Nat) (good : List Bool → Nat → Bool) : Bool :=
  (allWords L).all (fun w => !(p2B w) || (List.range L).all (fun j => !(admB false w j) || good w j))

theorem checkL_sound (L : Nat) (good : List Bool → Nat → Bool) (hc : checkL L good = true)
    (w : List Bool) (hw : w.length = L) (hP : P2 w) (j : Nat) (hadm : admB false w j = true) :
    good w j = true := by
  have hjL : j < L := by
    simp only [admB, Bool.and_eq_true, decide_eq_true_eq] at hadm
    omega
  simp only [checkL, List.all_eq_true] at hc
  have hmem : w ∈ allWords L := by rw [← hw]; exact mem_allWords w
  have h1 := hc w hmem
  rw [p2B_of_P2 w hP] at h1
  simp only [Bool.not_true, Bool.false_or, List.all_eq_true, List.mem_range] at h1
  have h2 := h1 j hjL
  rw [hadm] at h2
  simpa using h2

/-- The window `S A A A A S S` (newest first). -/
def W7 : List Bool := [false, true, true, true, true, false, false]
/-- The window `S S A A A A A A S S S` (newest first). -/
def W11 : List Bool := [false, false, true, true, true, true, true, true, false, false, false]

set_option maxRecDepth 100000 in
theorem check7 : checkL 7 (fun w j => w == W7 && j == 6) = true := by decide

set_option maxRecDepth 100000 in
theorem check11 : checkL 11 (fun w j => w == W11 && j == 10) = true := by decide

/-- Number of additions of a word. -/
def cntA : List Bool → Nat
  | [] => 0
  | b :: w => cntA w + (if b then 1 else 0)

theorem ones_eq_cntA (w : List Bool) : ones w = (cntA w : Int) := by
  induction w with
  | nil => simp [ones, cntA]
  | cons b w ih => cases b <;> simp [ones, cntA, ih] <;> omega

/-- The words of length `n` with `k` additions. -/
def wordsWith : Nat → Nat → List (List Bool)
  | 0, 0 => [[]]
  | 0, _ + 1 => []
  | n + 1, 0 => (wordsWith n 0).map (false :: ·)
  | n + 1, k + 1 => (wordsWith n (k+1)).map (false :: ·) ++ (wordsWith n k).map (true :: ·)

theorem mem_wordsWith (w : List Bool) : w ∈ wordsWith w.length (cntA w) := by
  induction w with
  | nil => simp [wordsWith, cntA]
  | cons b w ih =>
    cases b with
    | true => simp [wordsWith, cntA, ih]
    | false =>
      cases h : cntA w with
      | zero => rw [h] at ih; simp [wordsWith, cntA, h, ih]
      | succ k => rw [h] at ih; simp [wordsWith, cntA, h, ih]

def checkK (L k : Nat) (good : List Bool → Nat → Bool) : Bool :=
  (wordsWith L k).all (fun w => !(p2B w) || (List.range L).all (fun j => !(admB false w j) || good w j))

theorem checkK_sound (L k : Nat) (good : List Bool → Nat → Bool) (hc : checkK L k good = true)
    (w : List Bool) (hw : w.length = L) (hk : cntA w = k) (hP : P2 w) (j : Nat)
    (hadm : admB false w j = true) : good w j = true := by
  have hjL : j < L := by
    simp only [admB, Bool.and_eq_true, decide_eq_true_eq] at hadm
    omega
  simp only [checkK, List.all_eq_true] at hc
  have hmem : w ∈ wordsWith L k := by rw [← hw, ← hk]; exact mem_wordsWith w
  have h1 := hc w hmem
  rw [p2B_of_P2 w hP] at h1
  simp only [Bool.not_true, Bool.false_or, List.all_eq_true, List.mem_range] at h1
  have h2 := h1 j hjL
  rw [hadm] at h2
  simpa using h2

set_option maxRecDepth 100000 in
/-- The 6435 words of length 15 with 8 additions (a few seconds of kernel reduction). -/
theorem check15 : checkK 15 8 (fun _ _ => false) = true := by decide +kernel

theorem admB_false_of (full : Bool) (w : List Bool) (j : Nat) (h : admB full w j = true) :
    admB false w j = true := by
  simp only [admB, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h ⊢
  refine ⟨h.1, fun i hi => ?_⟩
  have h' := h.2 i hi
  simp only [Bool.or_eq_true] at h' ⊢
  rcases h' with h' | h'
  · exact Or.inl h'
  · right
    simp only [w1B, Bool.and_eq_true] at h' ⊢
    exact ⟨h'.1, by simp⟩

theorem w11_not_full : admB true W11 10 = false := by decide

/-! ## From a configuration to the abstract predicate -/

theorem getD_past (e : Int → Bool) (v : Int) (L i : Nat) (hi : i < L) :
    (past e v L).getD i true = e (v - ((i : Int) + 1)) := by
  simp [past, hi]

theorem adm_of_config (full : Bool) (e : Int → Bool) (M : List Int) (lag : Int → Nat)
    (own : Int → Int) (hO : OwnerMap e M lag own) (hA : ∀ b ∈ M, e b = true)
    (v : Int) (hv : v ∈ M) (L : Nat) (hown : v - (L : Int) ≤ own v)
    (hcov : ∀ c : Int, v - L ≤ c → c < v → e c = false → c ≠ own v →
      ∃ b ∈ M, b ≠ v ∧ own b = c)
    (hmotif : ∀ b ∈ M, b ≠ v → MotifOwner e M own b)
    (hfull : full = true → ∀ b ∈ M, b ≠ v → own b = b - 7 → e (b - 1) = false) :
    admB full (past e v L) (v - own v - 1).toNat = true := by
  have hlt := hO.own_lt v hv
  have hlen : (past e v L).length = L := by simp [past]
  have hjclk : v - (((v - own v - 1).toNat : Nat) + 1 : Int) = own v := by omega
  have gd : ∀ i, i < L → (past e v L).getD i true = e (v - ((i : Int) + 1)) :=
    fun i hi => getD_past e v L i hi
  have hjL : (v - own v - 1).toNat < L := by omega
  simp only [admB, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', List.all_eq_true,
    List.mem_range, hlen]
  refine ⟨⟨hjL, by rw [gd _ hjL, hjclk]; exact hO.own_S v hv⟩, fun i hi => ?_⟩
  -- a newer letter known to be an addition gives `getA = true`
  have eA : ∀ (d : Nat) (x : Int), x = v - ((i : Int) + 1) + (d : Int) → e x = true →
      getA (past e v L) i d = true := by
    intro d x hx hex
    by_cases h : d ≤ i
    · simp only [getA, if_pos h]
      rw [gd (i - d) (by omega)]
      have : v - (((i - d : Nat) : Int) + 1) = x := by omega
      rw [this]; exact hex
    · simp only [getA]; rw [if_neg h]
  cases hei : e (v - ((i : Int) + 1)) with
  | true => rw [gd i hi, hei]; simp
  | false =>
    by_cases hij : i = (v - own v - 1).toNat
    · simp [hij]
    · have hne : v - ((i : Int) + 1) ≠ own v := by
        intro h; apply hij; omega
      obtain ⟨b, hb, hbv, hob⟩ := hcov _ (by omega) (by omega) hei hne
      rcases hmotif b hb hbv with ⟨ho, h1, h2⟩ | ⟨ho, h2, h3, h4, h5, h6, hsib, hsibo⟩
      · -- AAS owner at `clk i + 3`
        have c1 : (i != 2) = true := by
          simp only [bne_iff_ne, ne_eq]
          intro h; apply hbv; omega
        have c2 := eA 1 (b - 2) (by omega) h2
        have c3 := eA 2 (b - 1) (by omega) h1
        have c4 := eA 3 b (by omega) (hA b hb)
        have haas : aasB (past e v L) i = true := by
          simp only [aasB, c1, c2, c3, c4, Bool.and_self]
        simp only [haas, Bool.or_true, Bool.true_or]
      · -- w1 owner at `clk i + 7`
        have hb7 : b = v - ((i : Int) + 1) + 7 := by omega
        have hi1 : 1 ≤ i := by
          by_cases h0 : i = 0
          · exfalso
            have : b - 6 = v := by subst h0; omega
            rw [this, hA v hv] at h6
            exact absurd h6 (by decide)
          · omega
        have c1 : (i != 6) = true := by
          simp only [bne_iff_ne, ne_eq]
          intro h; apply hbv; omega
        have c2 : decide (1 ≤ i) = true := by simp [hi1]
        have c3 : (!(past e v L).getD (i - 1) true) = true := by
          rw [gd (i - 1) (by omega)]
          have : v - (((i - 1 : Nat) : Int) + 1) = b - 6 := by omega
          rw [this, h6]; rfl
        have c4 := eA 2 (b - 5) (by omega) h5
        have c5 := eA 3 (b - 4) (by omega) h4
        have c6 := eA 4 (b - 3) (by omega) h3
        have c7 := eA 5 (b - 2) (by omega) h2
        have c8 := eA 7 b (by omega) (hA b hb)
        have c9 : (if i = 3 then (v - own v - 1).toNat == 2
            else (v - own v - 1).toNat != i - 1) = true := by
          by_cases h3' : i = 3
          · rw [if_pos h3']
            have hs : b - 3 = v := by omega
            rw [hs] at hsibo
            simp only [beq_iff_eq]
            omega
          · rw [if_neg h3']
            simp only [bne_iff_ne, ne_eq]
            intro hj
            have hov : own v = b - 6 := by omega
            have := hO.inj (b - 3) hsib v hv (by rw [hsibo, hov])
            omega
        have cx : (!full || w1Extra (past e v L) i) = true := by
          cases full with
          | false => rfl
          | true =>
            have hb1 := hfull rfl b hb hbv ho
            have d1 : (i != 5) = true := by
              simp only [bne_iff_ne, ne_eq]
              intro h5'
              have : b - 1 = v := by omega
              rw [this, hA v hv] at hb1
              exact absurd hb1 (by decide)
            have d2 : (if 6 ≤ i then !(past e v L).getD (i - 6) true else true) = true := by
              by_cases h6' : 6 ≤ i
              · rw [if_pos h6', gd (i - 6) (by omega)]
                have : v - (((i - 6 : Nat) : Int) + 1) = b - 1 := by omega
                rw [this, hb1]; rfl
              · rw [if_neg h6']
            simp only [w1Extra, d1, d2, Bool.not_true, Bool.false_or, Bool.and_self]
        have hw : w1B full (past e v L) (v - own v - 1).toNat i = true := by
          simp only [w1B, w1Base, c1, c2, c3, c4, c5, c6, c7, c8, c9, cx, Bool.and_self]
        simp only [hw, Bool.or_true]

/-! ## Main theorems -/

theorem past_length (e : Int → Bool) (v : Int) (L : Nat) : (past e v L).length = L := by
  simp [past]

/-- Counting part of R' (no `hnew`): the window of `v` has length at most 15. -/
theorem private_motif_count_le (e : Int → Bool) (M : List Int) (lag : Int → Nat) (own : Int → Int)
    (hO : OwnerMap e M lag own) (hA : ∀ b ∈ M, e b = true)
    (v : Int) (hv : v ∈ M) (L : Nat) (hP : P2 (past e v L)) (hown : v - (L : Int) ≤ own v)
    (hcov : ∀ c : Int, v - L ≤ c → c < v → e c = false → c ≠ own v →
      ∃ b ∈ M, b ≠ v ∧ own b = c)
    (hmotif : ∀ b ∈ M, b ≠ v → MotifOwner e M own b) :
    L ≤ 15 := by
  have h := adm_length_le false _ _ hP
    (adm_of_config false e M lag own hO hA v hv L hown hcov hmotif (fun h => absurd h (by decide)))
  rwa [past_length] at h

/-- In the window `W7` the subtractions `v - 1` and `v - 6` are owned by AAS members at `v + 2` and
`v - 3`. -/
theorem seven_owners (e : Int → Bool) (M : List Int) (own : Int → Int)
    (hA : ∀ b ∈ M, e b = true) (v : Int) (hv : v ∈ M)
    (hcov : ∀ c : Int, v - ((7 : Nat) : Int) ≤ c → c < v → e c = false → c ≠ own v →
      ∃ b ∈ M, b ≠ v ∧ own b = c)
    (hmotif : ∀ b ∈ M, b ≠ v → MotifOwner e M own b)
    (hw : past e v 7 = W7) (hov : own v = v - 7) :
    (v + 2) ∈ M ∧ own (v + 2) = v - 1 ∧ (v - 3) ∈ M ∧ own (v - 3) = v - 6 := by
  have g : ∀ i : Nat, i < 7 → e (v - ((i : Int) + 1)) = W7.getD i true := by
    intro i hi; rw [← getD_past e v 7 i hi, hw]
  have e1 : e (v - 1) = false := by have := g 0 (by omega); simpa [W7] using this
  have e6 : e (v - 6) = false := by have := g 5 (by omega); simpa [W7] using this
  obtain ⟨b, hb, hbv, hob⟩ := hcov (v - 1) (by omega) (by omega) e1 (by omega)
  have hb2 : b = v + 2 := by
    rcases hmotif b hb hbv with ⟨ho, _, _⟩ | ⟨ho, _, _, _, _, h6, _, _⟩
    · omega
    · exfalso
      rw [show b - 6 = v by omega, hA v hv] at h6
      exact absurd h6 (by decide)
  obtain ⟨b', hb', hbv', hob'⟩ := hcov (v - 6) (by omega) (by omega) e6 (by omega)
  have hb3 : b' = v - 3 := by
    rcases hmotif b' hb' hbv' with ⟨ho, _, _⟩ | ⟨ho, h2, _, _, _, _, _, _⟩
    · omega
    · exfalso
      rw [show b' - 2 = v - 1 by omega, e1] at h2
      exact absurd h2 (by decide)
  subst hb2; subst hb3
  exact ⟨hb, hob, hb', hob'⟩

/-- R' with the hypotheses of `newest_motif_count` minus `hnew`: the window of `v` is `AAS`, or the
w1 word `S A A A A S S` owning its oldest letter, or the word `S S A A A A A A S S S` owning its oldest
letter. The third case does occur (`eleven_occurs`); it is excluded by the full w1 shape
(`private_motif_count`). -/
theorem private_motif_window (e : Int → Bool) (M : List Int) (lag : Int → Nat) (own : Int → Int)
    (hO : OwnerMap e M lag own) (hA : ∀ b ∈ M, e b = true)
    (v : Int) (hv : v ∈ M) (L : Nat) (hP : P2 (past e v L)) (hown : v - (L : Int) ≤ own v)
    (hcov : ∀ c : Int, v - L ≤ c → c < v → e c = false → c ≠ own v →
      ∃ b ∈ M, b ≠ v ∧ own b = c)
    (hmotif : ∀ b ∈ M, b ≠ v → MotifOwner e M own b) :
    L = 3 ∨
    (L = 7 ∧ past e v 7 = W7 ∧ own v = v - 7 ∧
      (v + 2) ∈ M ∧ own (v + 2) = v - 1 ∧ (v - 3) ∈ M ∧ own (v - 3) = v - 6) ∨
    (L = 11 ∧ past e v 11 = W11 ∧ own v = v - 11) := by
  have hadm := adm_of_config false e M lag own hO hA v hv L hown hcov hmotif
    (fun h => absurd h (by decide))
  have hle := adm_length_le false _ _ hP hadm
  rw [past_length] at hle
  have hc := p2_count_identities _ hP
  rw [past_length] at hc
  obtain ⟨hL, -, hev⟩ := hc
  have hlt := hO.own_lt v hv
  rcases (by omega : L = 3 ∨ L = 7 ∨ L = 11 ∨ L = 15) with h | h | h | h
  · exact Or.inl h
  · subst h
    have hg := checkL_sound 7 _ check7 _ (past_length e v 7) hP _ hadm
    simp only [Bool.and_eq_true, beq_iff_eq] at hg
    have hov : own v = v - 7 := by have := hg.2; omega
    exact Or.inr (Or.inl ⟨rfl, hg.1, hov,
      seven_owners e M own hA v hv hcov hmotif hg.1 hov⟩)
  · subst h
    have hg := checkL_sound 11 _ check11 _ (past_length e v 11) hP _ hadm
    simp only [Bool.and_eq_true, beq_iff_eq] at hg
    exact Or.inr (Or.inr ⟨rfl, hg.1, by have := hg.2; omega⟩)
  · subst h
    have hk : cntA (past e v 15) = 8 := by
      have := ones_eq_cntA (past e v 15)
      omega
    have hg := checkK_sound 15 8 _ check15 _ (past_length e v 15) hk hP _ hadm
    exact absurd hg (by decide)

/-- R' (corrected): if moreover every w1 owner other than `v` has its newest letter `b - 1` a
subtraction (the full w1 word `S A A A A S S`), then `L = 3`, or `L = 7` with `own v = v - 7` and the
subtractions `v - 1`, `v - 6` owned by AAS members at `v + 2`, `v - 3`. -/
theorem private_motif_count (e : Int → Bool) (M : List Int) (lag : Int → Nat) (own : Int → Int)
    (hO : OwnerMap e M lag own) (hA : ∀ b ∈ M, e b = true)
    (v : Int) (hv : v ∈ M) (L : Nat) (hP : P2 (past e v L)) (hown : v - (L : Int) ≤ own v)
    (hcov : ∀ c : Int, v - L ≤ c → c < v → e c = false → c ≠ own v →
      ∃ b ∈ M, b ≠ v ∧ own b = c)
    (hmotif : ∀ b ∈ M, b ≠ v → MotifOwner e M own b)
    (hw1 : ∀ b ∈ M, b ≠ v → own b = b - 7 → e (b - 1) = false) :
    L = 3 ∨
    (L = 7 ∧ past e v 7 = W7 ∧ own v = v - 7 ∧
      (v + 2) ∈ M ∧ own (v + 2) = v - 1 ∧ (v - 3) ∈ M ∧ own (v - 3) = v - 6) := by
  rcases private_motif_window e M lag own hO hA v hv L hP hown hcov hmotif with h | h | ⟨h11, hw, hov⟩
  · exact Or.inl h
  · exact Or.inr h
  · exfalso
    subst h11
    have hadm := adm_of_config true e M lag own hO hA v hv 11 hown hcov hmotif (fun _ => hw1)
    have hj : (v - own v - 1).toNat = 10 := by omega
    rw [hw, hj, w11_not_full] at hadm
    exact absurd hadm (by decide)

/-! ## The length-11 case occurs under `MotifOwner` alone -/

def cexE (c : Int) : Bool := !(c == -1 || c == -2 || c == -9 || c == -10 || c == -11)
def cexM : List Int := [0, 2, 5, -6, -3]
def cexLag (b : Int) : Nat :=
  if b = 0 then 11 else if b = 2 then 3 else if b = 5 then 7 else if b = -6 then 3 else 7
def cexOwn (b : Int) : Int :=
  if b = 0 then -11 else if b = 2 then -1 else if b = 5 then -2 else if b = -6 then -9 else -10

/-- All hypotheses of `private_motif_window` hold for `v = 0`, `L = 11` (members `0, 2, 5, -6, -3`;
`2`, `-6` are AAS owners, `5`, `-3` are w1 owners whose newest letters `4`, `-4` are additions). -/
theorem eleven_occurs :
    OwnerMap cexE cexM cexLag cexOwn ∧ (∀ b ∈ cexM, cexE b = true) ∧ (0 : Int) ∈ cexM ∧
    P2 (past cexE 0 11) ∧ (0 : Int) - ((11 : Nat) : Int) ≤ cexOwn 0 ∧
    (∀ c : Int, 0 - ((11 : Nat) : Int) ≤ c → c < 0 → cexE c = false → c ≠ cexOwn 0 →
      ∃ b ∈ cexM, b ≠ 0 ∧ cexOwn b = c) ∧
    (∀ b ∈ cexM, b ≠ 0 → MotifOwner cexE cexM cexOwn b) := by
  refine ⟨⟨by decide, by decide, by decide, by decide, by decide⟩, by decide, by decide,
    ?_, by decide, ?_, ?_⟩
  · unfold P2; decide
  · intro c h1 h2 hS hne
    have hc : c = -1 ∨ c = -2 ∨ c = -3 ∨ c = -4 ∨ c = -5 ∨ c = -6 ∨ c = -7 ∨ c = -8 ∨ c = -9 ∨
        c = -10 ∨ c = -11 := by omega
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact absurd hS (by decide)
      | exact absurd (by decide) hne
      | decide
  · intro b hb hbv
    simp only [cexM, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl hbv
    all_goals (unfold MotifOwner; decide)

/-- Hence `L = 3 ∨ L = 7` does not follow from the hypotheses of `newest_motif_count` without `hnew`. -/
theorem not_three_or_seven :
    ¬ (∀ (e : Int → Bool) (M : List Int) (lag : Int → Nat) (own : Int → Int),
      OwnerMap e M lag own → (∀ b ∈ M, e b = true) →
      ∀ v ∈ M, ∀ L : Nat, P2 (past e v L) → v - (L : Int) ≤ own v →
      (∀ c : Int, v - L ≤ c → c < v → e c = false → c ≠ own v → ∃ b ∈ M, b ≠ v ∧ own b = c) →
      (∀ b ∈ M, b ≠ v → MotifOwner e M own b) → L = 3 ∨ L = 7) := by
  intro h
  obtain ⟨hO, hA, hv, hP, hown, hcov, hmotif⟩ := eleven_occurs
  have := h cexE cexM cexLag cexOwn hO hA 0 hv 11 hP hown hcov hmotif
  omega

/-! ## The induction: classification of closed configurations from the existence of private members

`MotifOwnerFull` adds to `MotifOwner` the newest letter `b - 1 = S` of a w1-type member (the full word
`S A A A A S S`). `motifFull_step` is the inductive step for any member `w` (not necessarily the
newest): if `M.erase w` has the full motif shape, so has `M`. `motifFull_of_private` runs the induction
on the number of members, assuming that every nonempty closed configuration (with the same sign word,
lags and owner map) has a member whose owned subtraction lies in no other member's window (Claim P of
H-20261003-01). Claim P itself is NOT proved here; this theorem is the reduction of the classification
to it. -/

open NewestMemberMotifCount (ClosedConfig erase_closed)

/-- The full motif shape of a member: `MotifOwner` plus the newest letter `S` of a w1-type member. -/
def MotifOwnerFull (e : Int → Bool) (M : List Int) (own : Int → Int) (b : Int) : Prop :=
  MotifOwner e M own b ∧ (own b = b - 7 → e (b - 1) = false)

def MotifFull (e : Int → Bool) (M : List Int) (own : Int → Int) : Prop :=
  ∀ b ∈ M, MotifOwnerFull e M own b

/-- A member whose owned subtraction lies in no other member's window. -/
def HasPrivate (_e : Int → Bool) (M : List Int) (lag : Int → Nat) (own : Int → Int) : Prop :=
  ∃ w ∈ M, ∀ b ∈ M, b ≠ w → ¬ (b - (lag b : Int) ≤ own w ∧ own w < b)

/-- Inductive step at any member `w`: if `M.erase w` has the full motif shape, so has `M`. -/
theorem motifFull_step (e : Int → Bool) (M : List Int) (lag : Int → Nat) (own : Int → Int)
    (hC : ClosedConfig e M lag own) (w : Int) (hw : w ∈ M)
    (hrest : MotifFull e (M.erase w) own) : MotifFull e M own := by
  have hnd := hC.owner.nodup
  have mem_er : ∀ b, b ∈ M.erase w ↔ b ≠ w ∧ b ∈ M := fun b => hnd.mem_erase_iff
  have lift : ∀ b ∈ M, b ≠ w → MotifOwnerFull e M own b := by
    intro b hb hbw
    obtain ⟨h, hfull⟩ := hrest b ((mem_er b).2 ⟨hbw, hb⟩)
    refine ⟨?_, hfull⟩
    rcases h with h | ⟨h1, h2, h3, h4, h5, h6, hsib, hsibo⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1, h2, h3, h4, h5, h6, List.mem_of_mem_erase hsib, hsibo⟩
  intro b hb
  by_cases hbw : b = w
  · subst hbw
    have hcov : ∀ c : Int, b - (lag b : Int) ≤ c → c < b → e c = false → c ≠ own b →
        ∃ b' ∈ M, b' ≠ b ∧ own b' = c := by
      intro c h1 h2 hS hne
      obtain ⟨b', hb', hob'⟩ := hC.onto b hb c h1 h2 hS
      refine ⟨b', hb', ?_, hob'⟩
      intro heq; subst heq; exact hne hob'.symm
    have hres := private_motif_count e M lag own hC.owner hC.addA b hb (lag b) (hC.p2 b hb)
      (hC.owner.own_ge b hb) hcov (fun b' hb' hne => (lift b' hb' hne).1)
      (fun b' hb' hne ho => (lift b' hb' hne).2 ho)
    have hlt := hC.owner.own_lt b hb
    have hge := hC.owner.own_ge b hb
    have hS := hC.owner.own_S b hb
    rcases hres with hL | ⟨hL, hw7, hov, _, _, hsib, hsibo⟩
    · -- AAS
      have hwin := P2SubtractionLevelSum.p2_length_three _ (hC.p2 b hb) (by simp [past, hL])
      rw [hL] at hwin hge
      have g : ∀ i : Nat, i < 3 → e (b - ((i : Int) + 1)) = [true, true, false].getD i true := by
        intro i hi; rw [← getD_past e b 3 i hi, hwin]
      have e1 : e (b - 1) = true := by have := g 0 (by omega); simpa using this
      have e2 : e (b - 2) = true := by
        have := g 1 (by omega); simp at this
        have h' : b - (1 + 1) = b - 2 := by omega
        simpa [h'] using this
      have hown : own b = b - 3 := by
        rcases (by omega : own b = b - 1 ∨ own b = b - 2 ∨ own b = b - 3) with h | h | h
        · rw [h, e1] at hS; exact absurd hS (by decide)
        · rw [h, e2] at hS; exact absurd hS (by decide)
        · exact h
      exact ⟨Or.inl ⟨hown, e1, e2⟩, fun h7 => by omega⟩
    · -- the w1 of a triple
      have g : ∀ i : Nat, i < 7 → e (b - ((i : Int) + 1)) = W7.getD i true := by
        intro i hi; rw [← getD_past e b 7 i hi, hw7]
      have bit : ∀ (i : Nat) (hi : i < 7) (c : Int), c = b - ((i : Int) + 1) →
          e c = W7.getD i true := by
        intro i hi c hc; rw [hc]; exact g i hi
      have e1 := bit 0 (by omega) (b - 1) (by omega)
      have e2 := bit 1 (by omega) (b - 2) (by omega)
      have e3 := bit 2 (by omega) (b - 3) (by omega)
      have e4 := bit 3 (by omega) (b - 4) (by omega)
      have e5 := bit 4 (by omega) (b - 5) (by omega)
      have e6 := bit 5 (by omega) (b - 6) (by omega)
      simp [W7] at e1 e2 e3 e4 e5 e6
      exact ⟨Or.inr ⟨hov, e2, e3, e4, e5, e6, hsib, hsibo⟩, fun _ => e1⟩
  · exact lift b hb hbw

/-- Reduction of the classification to Claim P: if every nonempty closed configuration (same sign word,
lags and owner map) has a member with a private owned subtraction, then every closed configuration has
the full motif shape (isolated AAS members and w1 triples, locally). -/
theorem motifFull_of_private (e : Int → Bool) (lag : Int → Nat) (own : Int → Int)
    (hP : ∀ M' : List Int, ClosedConfig e M' lag own → M' ≠ [] → HasPrivate e M' lag own) :
    ∀ M : List Int, ClosedConfig e M lag own → MotifFull e M own := by
  have key : ∀ n : Nat, ∀ M : List Int, M.length ≤ n → ClosedConfig e M lag own → MotifFull e M own := by
    intro n
    induction n with
    | zero =>
      intro M hlen _ b hb
      have : M = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst this; simp at hb
    | succ n ih =>
      intro M hlen hC
      by_cases hM : M = []
      · subst hM; intro b hb; simp at hb
      · obtain ⟨w, hw, hpriv⟩ := hP M hC hM
        have hC' := erase_closed e M lag own hC w hw hpriv
        have hlen' : (M.erase w).length ≤ n := by
          rw [List.length_erase_of_mem hw]; omega
        exact motifFull_step e M lag own hC w hw (ih (M.erase w) hlen' hC')
  exact fun M hC => key M.length M (Nat.le_refl _) hC

end Recaman.PrivateMemberMotifCount
