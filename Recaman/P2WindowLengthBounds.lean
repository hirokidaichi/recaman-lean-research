import Recaman.LeadingRunSupply

namespace Recaman.P2WindowLengthBounds

/-! Lag-uniform length bounds for P2 words: nested windows leave a gap of at least 8, and a leading run
of `m` subtractions forces length at least `4m + 3`.

Part 1 (nested gap).

Words are newest-first. Let `v = p ++ w ++ s` be a P2 word of length `L ≥ 11` and let the last
letter of `p` be an addition: in the periodic picture `v = past e b L`, the clock `b - |p|` is an
addition and `w` is a window of that clock lying inside the window of `b`, `s` is the part of `v`'s
window older than `w`. If `w` is also P2, then `|p| + |s| ≥ 8` (`nested_gap`): since both lengths are
`≡ 3 (mod 4)`, the gap is a positive multiple of 4, and gap 4 is impossible. No minimality and no
lag bound are assumed. Gap 4 does occur for `L = 7` (`AAS` inside `SAAAASS`).
-/

open ShortPeriodicSupply (sign)
open LeadingRunSupply (mass moment P2 mass_append moment_append p2_count_identities ones positions
  ones_append positions_append ones_bounds)

/-- Finite certificate: for every split `p ++ s` of total length 4 whose `p` ends in an addition,
the mass/moment constraints of `p ++ w ++ s` with `w` P2 have no solution with `L ≥ 11`. We encode
the constraint as a Boolean test on the four numbers it depends on. -/
def gapFourOk (p s : List Bool) : Bool :=
  -- returns true when the configuration is excluded for every L ≥ 11
  let mp := mass p
  let ms := mass s
  let c := moment p + moment s + p.length
  -- mass: mp + 1 + ms = 1.  moment: c + (L - s.length) * ms = 0 (derived in `gap_four_eq`).
  decide (mp + ms ≠ 0) ||
  (decide (ms = 0) && decide (c ≠ 0)) ||
  (decide (ms ≠ 0) && decide (c.natAbs < (11 - s.length) * ms.natAbs))

/-- The lists of length at most 4. -/
def wordsUpTo : Nat → List (List Bool)
  | 0 => [[]]
  | n+1 => [[]] ++ ((wordsUpTo n).flatMap fun w => [true :: w, false :: w])

theorem mem_wordsUpTo (w : List Bool) (n : Nat) (h : w.length ≤ n) : w ∈ wordsUpTo n := by
  induction n generalizing w with
  | zero =>
    have : w = [] := List.eq_nil_of_length_eq_zero (by omega)
    simp [wordsUpTo, this]
  | succ n ih =>
    cases w with
    | nil => simp [wordsUpTo]
    | cons b w =>
      simp only [List.length_cons] at h
      have hw := ih w (by omega)
      simp only [wordsUpTo, List.mem_append, List.mem_flatMap]
      right
      exact ⟨w, hw, by cases b <;> simp⟩

/-- All splits checked by `decide`. -/
theorem gapFour_table :
    ∀ p ∈ wordsUpTo 4, ∀ s ∈ wordsUpTo 4,
      p.length + s.length = 4 → p.getLast? = some true → gapFourOk p s = true := by
  decide

/-- The moment equation of `p ++ w ++ s` with `w` P2. -/
theorem gap_four_eq (p w s : List Bool) (hv : P2 (p ++ w ++ s)) (hw : P2 w) :
    mass p + mass s = 0 ∧
      moment p + moment s + p.length + ((w.length + p.length : Nat) : Int) * mass s = 0 := by
  obtain ⟨hvm, hvo⟩ := hv
  obtain ⟨hwm, hwo⟩ := hw
  simp only [mass_append, moment_append, List.length_append] at hvm hvo
  constructor
  · omega
  · rw [hwm, hwo] at hvo
    push_cast at hvo ⊢
    grind

/-- A P2 sub-window that starts right after an addition inside a P2 window of length at least 11
leaves a gap of at least 8. -/
theorem nested_gap (p w s : List Bool) (hv : P2 (p ++ w ++ s)) (hw : P2 w)
    (hA : p.getLast? = some true) (hL : 11 ≤ (p ++ w ++ s).length) :
    8 ≤ p.length + s.length := by
  -- lengths of P2 words are ≡ 3 (mod 4)
  have hcv := (p2_count_identities _ hv)
  have hcw := (p2_count_identities _ hw)
  have hp : p ≠ [] := by intro h; simp [h] at hA
  have hp1 : 1 ≤ p.length := by
    cases p with
    | nil => exact absurd rfl hp
    | cons _ _ => simp
  have hlen : (p ++ w ++ s).length = p.length + w.length + s.length := by simp; omega
  -- (L mod 4 = 3 and |w| mod 4 = 3) from the count identities
  have h4v : ((p ++ w ++ s).length : Int) % 4 = 3 := by
    obtain ⟨hl, -, hev⟩ := hcv
    omega
  have h4w : (w.length : Int) % 4 = 3 := by
    obtain ⟨hl, -, hev⟩ := hcw
    omega
  by_cases hge8 : 8 ≤ p.length + s.length
  · exact hge8
  exfalso
  have hgap : p.length + s.length = 4 := by
    rw [hlen] at h4v
    push_cast at h4v
    omega
  have hok := gapFour_table p (mem_wordsUpTo p 4 (by omega)) s (mem_wordsUpTo s 4 (by omega)) hgap hA
  obtain ⟨hm, hmo⟩ := gap_four_eq p w s hv hw
  simp only [gapFourOk, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hok
  have hwlen : 11 ≤ w.length + 4 := by rw [hlen] at hL; omega
  rcases hok with (h1 | ⟨h2, h3⟩) | ⟨h4, h5⟩
  · exact h1 hm
  · rw [h2] at hmo; simp at hmo; exact h3 (by omega)
  · -- |c| < (11 - |s|) |ms| ≤ (|w| + |p|) |ms| = |c|
    have hs4 : s.length ≤ 3 := by omega
    have hkey : (moment p + moment s + p.length) = -(((w.length + p.length : Nat) : Int) * mass s) := by
      omega
    have habs : (moment p + moment s + (p.length : Int)).natAbs
        = (w.length + p.length) * (mass s).natAbs := by
      rw [hkey, Int.natAbs_neg, Int.natAbs_mul, Int.natAbs_natCast]
    have hge : (11 - s.length) * (mass s).natAbs ≤ (w.length + p.length) * (mass s).natAbs :=
      Nat.mul_le_mul_right _ (by omega)
    omega

open LeadingRunSupply (past)

/-- A window splits into its newest `m` letters and the window of the clock `b - m`. -/
theorem past_add (e : Int → Bool) (b : Int) (m n : Nat) :
    past e b (m + n) = past e b m ++ past e (b - (m : Int)) n := by
  apply List.ext_getElem
  · simp [past]
  · intro i h1 h2
    have hm : (past e b m).length = m := by simp [past]
    rw [List.getElem_append]
    split
    · simp [past]
    · rename_i hi
      rw [hm] at hi
      simp only [past, List.getElem_map, List.getElem_range, List.length_map, List.length_range]
      congr 1
      push_cast
      omega

/-- Stream form: if `past e b L` is P2 with `L ≥ 11`, the clock `b - j` (`1 ≤ j`) is an addition and its
window `past e (b - j) d` lies inside (`j + d ≤ L`) and is P2, then `d + 8 ≤ L`. -/
theorem past_nested_gap (e : Int → Bool) (b : Int) (L j d : Nat)
    (hv : P2 (past e b L)) (hL : 11 ≤ L) (hj : 1 ≤ j) (hA : e (b - (j : Int)) = true)
    (hjd : j + d ≤ L) (hw : P2 (past e (b - (j : Int)) d)) :
    d + 8 ≤ L := by
  have hsplit : past e b L =
      past e b j ++ past e (b - (j : Int)) d ++ past e (b - (j : Int) - (d : Int)) (L - j - d) := by
    have h1 : L = j + (d + (L - j - d)) := by omega
    conv => lhs; rw [h1]
    rw [past_add, past_add, List.append_assoc]
  have hlast : (past e b j).getLast? = some true := by
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    rw [List.getLast?_eq_getElem?]
    simp [past]
    have : b - ((k + 1 : Nat) : Int) = b - (k : Int) - 1 := by push_cast; omega
    simpa [this] using hA
  have hv' : P2 (past e b j ++ past e (b - (j : Int)) d ++ past e (b - (j : Int) - (d : Int)) (L - j - d)) := by
    rw [← hsplit]; exact hv
  have hlen : 11 ≤ (past e b j ++ past e (b - (j : Int)) d ++
      past e (b - (j : Int) - (d : Int)) (L - j - d)).length := by
    simp [past]; omega
  have := nested_gap _ _ _ hv' hw hlast hlen
  simp [past] at this
  omega

/-! Part 2 (leading subtractions; the mirror of E-090 `LeadingRunSupply.leading_run_bound`). -/

/-- Lower bound on the position sum of the additions: they are placed first. -/
theorem positions_lower (w : List Bool) : ones w * (ones w + 1) ≤ 2 * positions w := by
  induction w with
  | nil => simp [ones, positions]
  | cons b w ih =>
    have hb := ones_bounds w
    cases b <;> simp [ones, positions] <;> grind

@[simp] theorem ones_replicate_S (m : Nat) : ones (List.replicate m false) = 0 := by
  induction m with
  | zero => simp [ones]
  | succ m ih => simp [List.replicate_succ, ones, ih]

@[simp] theorem positions_replicate_S (m : Nat) : positions (List.replicate m false) = 0 := by
  induction m with
  | zero => simp [positions]
  | succ m ih => simp [List.replicate_succ, positions, ih]

/-- A P2 word whose first `m` letters (newest first) are subtractions has length at least `4m + 3`.
No minimality and no upper lag bound are assumed. -/
theorem leading_S_run_bound (m : Nat) (tail : List Bool)
    (h : P2 (List.replicate m false ++ tail)) :
    4 * m + 3 ≤ (List.replicate m false ++ tail).length := by
  have hc := p2_count_identities _ h
  have hl := positions_lower tail
  simp only [ones_append, ones_replicate_S, positions_append, positions_replicate_S,
    List.length_append, List.length_replicate, Int.natCast_add] at hc
  obtain ⟨hlen, hpos, hev⟩ := hc
  have hlen' : (List.replicate m false ++ tail).length = m + tail.length := by simp
  -- 2 n^2 - n = 2 positions = 2 positions tail + 2 m n >= n (n+1) + 2 m n, with n = ones tail
  have hq : ones tail * ones tail - 2 * ones tail - 2 * (m : Int) * ones tail ≥ 0 := by grind
  have hn : 1 ≤ ones tail := by omega
  have hn2 : ones tail - 2 - 2 * (m : Int) ≥ 0 := by
    by_cases hneg : ones tail - 2 - 2 * (m : Int) ≥ 0
    · exact hneg
    · have hpos' : 0 < ones tail := by omega
      have : ones tail * (ones tail - 2 - 2 * (m : Int)) < 0 :=
        Int.mul_neg_of_pos_of_neg hpos' (by omega)
      grind
  omega

/-- Stream form: if the `m` newest clocks before `b` are subtractions and `past e b L` is P2, then
`L ≥ 4m + 3`. -/
theorem past_leading_S_run_bound (e : Int → Bool) (b : Int) (L m : Nat) (hm : m ≤ L)
    (hS : ∀ i, i < m → e (b - ((i+1 : Nat) : Int)) = false) (h : P2 (past e b L)) :
    4 * m + 3 ≤ L := by
  have hsplit : past e b L = List.replicate m false ++ past e (b - (m : Int)) (L - m) := by
    have h1 : L = m + (L - m) := by omega
    conv => lhs; rw [h1]
    rw [past_add]
    congr 1
    apply List.ext_getElem
    · simp [past]
    · intro i h1 h2
      have hi : i < m := by simpa [past] using h1
      simp only [past, List.getElem_map, List.getElem_range, List.getElem_replicate]
      exact hS i hi
  have := leading_S_run_bound m _ (hsplit ▸ h)
  simp [past] at this
  omega

/-! Part 3 (shifted windows). Two P2 windows that overlap except for at most 3 letters at each end,
with an addition at the newer window's boundary letter, cannot both exist when the newer one has
length at least 11. This gives the boundary lemmas of H-20261003-01: a newer member at most 3 clocks
after `b` has no window of the same length `L`, and a member at most 3 clocks before `b` has no window
reaching the start of `b`'s window with lag at most `L`. -/

/-- Finite certificate for shifted windows. -/
def shiftOk (p r : List Bool) : Bool :=
  let mp := mass p
  let mr := mass r
  let v := moment p - moment r + p.length
  decide (mp ≠ mr) ||
  (decide (mr = 0) && decide (v ≠ 0)) ||
  (decide (mr ≠ 0) && decide (v.natAbs < 11 * mr.natAbs))

theorem shift_table :
    ∀ p ∈ wordsUpTo 3, ∀ r ∈ wordsUpTo 3,
      1 ≤ p.length → r.length ≤ p.length → p.getLast? = some true → shiftOk p r = true := by
  decide

/-- Mass/moment identity of two overlapping P2 windows `p ++ c` and `c ++ r`. -/
theorem shift_eq (p c r : List Bool) (h1 : P2 (p ++ c)) (h2 : P2 (c ++ r)) :
    mass p = mass r ∧
      moment p - moment r + p.length = ((p.length + c.length : Nat) : Int) * mass r := by
  obtain ⟨h1m, h1o⟩ := h1
  obtain ⟨h2m, h2o⟩ := h2
  simp only [mass_append, moment_append] at h1m h1o h2m h2o
  constructor
  · omega
  · push_cast
    have hc : mass c = 1 - mass r := by omega
    have hp : mass p = mass r := by omega
    rw [hc] at h1o
    grind

/-- Shifted P2 windows: impossible when the newer window has length at least 11, its boundary letter
is an addition and the shifts are at most 3. -/
theorem shifted_p2 (p c r : List Bool) (h1 : P2 (p ++ c)) (h2 : P2 (c ++ r))
    (hA : p.getLast? = some true) (hp1 : 1 ≤ p.length) (hp3 : p.length ≤ 3)
    (hr : r.length ≤ p.length) (hL : 11 ≤ (p ++ c).length) : False := by
  have hok := shift_table p (mem_wordsUpTo p 3 hp3) r (mem_wordsUpTo r 3 (by omega)) hp1 hr hA
  obtain ⟨hm, hmo⟩ := shift_eq p c r h1 h2
  simp only [shiftOk, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hok
  have hlen : (p ++ c).length = p.length + c.length := by simp
  rcases hok with (h | ⟨h0, hv⟩) | ⟨hne, hlt⟩
  · exact h hm
  · rw [h0] at hmo; simp at hmo; exact hv (by omega)
  · have habs : (moment p - moment r + (p.length : Int)).natAbs
        = (p.length + c.length) * (mass r).natAbs := by
      rw [hmo, Int.natAbs_mul, Int.natAbs_natCast]
    have hge : 11 * (mass r).natAbs ≤ (p.length + c.length) * (mass r).natAbs :=
      Nat.mul_le_mul_right _ (by omega)
    omega

/-- Stream form, older side: if `past e b L` is P2 with `L ≥ 11`, the clock `b - j` (`1 ≤ j ≤ 3`) is
an addition, then its window cannot be P2 with a length `L'` that reaches the start of `b`'s window
without exceeding `L` (`L - j ≤ L' ≤ L`). -/
theorem past_older_crossing (e : Int → Bool) (b : Int) (L j L' : Nat)
    (hv : P2 (past e b L)) (hL : 11 ≤ L) (hj1 : 1 ≤ j) (hj3 : j ≤ 3)
    (hA : e (b - (j : Int)) = true) (hlo : L - j ≤ L') (hhi : L' ≤ L)
    (hw : P2 (past e (b - (j : Int)) L')) : False := by
  have hv' : past e b L = past e b j ++ past e (b - (j : Int)) (L - j) := by
    have h1 : L = j + (L - j) := by omega
    conv => lhs; rw [h1]
    rw [past_add]
  have hw' : past e (b - (j : Int)) L' =
      past e (b - (j : Int)) (L - j) ++ past e (b - (j : Int) - ((L - j : Nat) : Int)) (L' - (L - j)) := by
    have h1 : L' = (L - j) + (L' - (L - j)) := by omega
    conv => lhs; rw [h1]
    rw [past_add]
  have hlast : (past e b j).getLast? = some true := by
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    rw [List.getLast?_eq_getElem?]
    simp [past]
    have : b - ((k + 1 : Nat) : Int) = b - (k : Int) - 1 := by push_cast; omega
    simpa [this] using hA
  apply shifted_p2 (past e b j) (past e (b - (j : Int)) (L - j))
    (past e (b - (j : Int) - ((L - j : Nat) : Int)) (L' - (L - j)))
    (hv' ▸ hv) (hw' ▸ hw) hlast (by simp [past]; omega) (by simp [past]; omega)
    (by simp [past]; omega) (by simp [past]; omega)

/-- Stream form, newer side: if `b` is an addition with a P2 window `past e b L` (`L ≥ 11`), no clock
`b + u` with `1 ≤ u ≤ 3` has a P2 window of the same length `L`. -/
theorem past_newer_shift (e : Int → Bool) (b : Int) (L u : Nat)
    (hv : P2 (past e b L)) (hL : 11 ≤ L) (hb : e b = true) (hu1 : 1 ≤ u) (hu3 : u ≤ 3)
    (hw : P2 (past e (b + (u : Int)) L)) : False := by
  have hw' : past e (b + (u : Int)) L = past e (b + (u : Int)) u ++ past e b (L - u) := by
    have h1 : L = u + (L - u) := by omega
    conv => lhs; rw [h1]
    rw [past_add]
    congr 2
    omega
  have hv' : past e b L = past e b (L - u) ++ past e (b - ((L - u : Nat) : Int)) u := by
    have h1 : L = (L - u) + u := by omega
    conv => lhs; rw [h1]
    rw [past_add]
  have hlast : (past e (b + (u : Int)) u).getLast? = some true := by
    obtain ⟨k, rfl⟩ : ∃ k, u = k + 1 := ⟨u - 1, by omega⟩
    rw [List.getLast?_eq_getElem?]
    simp [past]
    have : b + ((k + 1 : Nat) : Int) - ((k + 1 : Nat) : Int) = b := by omega
    simpa [this] using hb
  apply shifted_p2 (past e (b + (u : Int)) u) (past e b (L - u)) (past e (b - ((L - u : Nat) : Int)) u)
    (hw' ▸ hw) (hv' ▸ hv) hlast (by simp [past]; omega) (by simp [past]; omega)
    (by simp [past]) (by simp [past]; omega)

end Recaman.P2WindowLengthBounds
