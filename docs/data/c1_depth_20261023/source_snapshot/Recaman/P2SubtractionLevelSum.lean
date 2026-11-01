import Recaman.LeadingRunSupply

namespace Recaman.P2SubtractionLevelSum

/-! Levels of the subtractions inside a P2 window, for every lag.

Words are newest-first, as in `LeadingRunSupply`: for a window `w = past e b L`, the letter
`w[i]` sits at clock `b - (i+1)`, and the walk height of that clock above the window start
`b - L` is the mass of the strictly older letters, `mass (w.drop (i+1))`. With
`F t = Σ_{c < t} sign (e c)` this height is `F (b - (i+1)) - F (b - L)`, and the member level is
`F (b - L) = F b - 1`; so the height of a subtraction is the top of that down-step measured from
the member level.

Main identity (`p2_sLevelSum`): in every P2 word of length `L` the heights of the subtractions add
up to `(L - 3) / 4`, and the heights of the additions add up to `-(L + 1) / 4`. No minimality and
no lag bound are assumed. Consequences: a P2 word always has a subtraction at height `≤ 0`
(`p2_exists_low_subtraction`), and a P2 word all of whose subtractions have height `≤ 0` is `AAS`
(`p2_eq_aas_of_low_subtractions`), so every P2 window of length at least 7 has a subtraction strictly
above the member level (`p2_exists_high_subtraction`).
-/

open ShortPeriodicSupply (sign)
open LeadingRunSupply (mass moment P2 ones mass_cons mass_eq p2_count_identities)

/-- Sum of the heights (mass of the older letters) of the subtractions of a newest-first word. -/
def sLevelSum : List Bool → Int
  | [] => 0
  | b :: w => (if b then 0 else mass w) + sLevelSum w

/-- Sum of the heights of the additions of a newest-first word. -/
def aLevelSum : List Bool → Int
  | [] => 0
  | b :: w => (if b then mass w else 0) + aLevelSum w

/-- Number of subtractions. -/
def sCount : List Bool → Int
  | [] => 0
  | b :: w => (if b then 0 else 1) + sCount w

/-- Area identity: the heights of all letters add up to `moment - mass`. -/
theorem level_sum_add (w : List Bool) :
    aLevelSum w + sLevelSum w = moment w - mass w := by
  induction w with
  | nil => simp [aLevelSum, sLevelSum, moment]
  | cons b w ih =>
    cases b <;> simp [aLevelSum, sLevelSum, moment, sign] <;> omega

/-- Telescoping identity `(H + σ)^2 - H^2 = 2 σ H + 1`, summed over the word. -/
theorem level_sum_sub (w : List Bool) :
    2 * (aLevelSum w - sLevelSum w) = mass w * mass w - w.length := by
  induction w with
  | nil => simp [aLevelSum, sLevelSum]
  | cons b w ih =>
    cases b <;> simp [aLevelSum, sLevelSum, sign, List.length_cons] <;> grind

/-- In a P2 word of length `L` the subtraction heights sum to `(L - 3) / 4`. -/
theorem p2_sLevelSum (w : List Bool) (h : P2 w) :
    4 * sLevelSum w = (w.length : Int) - 3 := by
  have h1 := level_sum_add w
  have h2 := level_sum_sub w
  obtain ⟨hm, hmo⟩ := h
  rw [hm, hmo] at h1
  rw [hm] at h2
  omega

/-- In a P2 word of length `L` the addition heights sum to `-(L + 1) / 4`. -/
theorem p2_aLevelSum (w : List Bool) (h : P2 w) :
    4 * aLevelSum w = -((w.length : Int) + 1) := by
  have h1 := level_sum_add w
  have h2 := level_sum_sub w
  obtain ⟨hm, hmo⟩ := h
  rw [hm, hmo] at h1
  rw [hm] at h2
  omega

theorem sCount_eq (w : List Bool) : sCount w = w.length - ones w := by
  induction w with
  | nil => simp [sCount, ones]
  | cons b w ih => cases b <;> simp [sCount, ones, List.length_cons, ih] <;> omega

/-- A P2 word of length `L` has `(L - 1) / 2` subtractions. -/
theorem p2_sCount (w : List Bool) (h : P2 w) : 2 * sCount w = (w.length : Int) - 1 := by
  have hc := (p2_count_identities w h).1
  have hs := sCount_eq w
  omega

/-- Heights of subtractions, as a list (newest first). -/
def sLevels : List Bool → List Int
  | [] => []
  | b :: w => if b then sLevels w else mass w :: sLevels w

theorem sLevels_sum (w : List Bool) : (sLevels w).sum = sLevelSum w := by
  induction w with
  | nil => simp [sLevels, sLevelSum]
  | cons b w ih => cases b <;> simp [sLevels, sLevelSum, ih]

theorem sLevels_length (w : List Bool) : ((sLevels w).length : Int) = sCount w := by
  induction w with
  | nil => simp [sLevels, sCount]
  | cons b w ih => cases b <;> simp [sLevels, sCount, ih] <;> omega

/-- `x ∈ sLevels w` iff some subtraction of `w` has height `x`. -/
theorem mem_sLevels (w : List Bool) (x : Int) :
    x ∈ sLevels w ↔ ∃ i, ∃ hi : i < w.length, w[i] = false ∧ mass (w.drop (i+1)) = x := by
  induction w with
  | nil => simp [sLevels]
  | cons b w ih =>
    constructor
    · intro hx
      cases b with
      | true =>
        simp only [sLevels, if_true] at hx
        obtain ⟨i, hi, hb, hm⟩ := ih.1 hx
        exact ⟨i+1, by simp; omega, by simpa using hb, by simpa using hm⟩
      | false =>
        simp only [sLevels, Bool.false_eq_true, if_false, List.mem_cons] at hx
        rcases hx with hx | hx
        · exact ⟨0, by simp, rfl, by simp [hx]⟩
        · obtain ⟨i, hi, hb, hm⟩ := ih.1 hx
          exact ⟨i+1, by simp; omega, by simpa using hb, by simpa using hm⟩
    · rintro ⟨i, hi, hb, hm⟩
      cases i with
      | zero =>
        simp at hb hm
        subst hb
        simp [sLevels, hm]
      | succ i =>
        have hi' : i < w.length := by simp at hi; omega
        have hrec : x ∈ sLevels w := ih.2 ⟨i, hi', by simpa using hb, by simpa using hm⟩
        cases b <;> simp [sLevels, hrec]

theorem sum_le_of_forall_le (l : List Int) (k : Int) (h : ∀ x ∈ l, x ≤ k) :
    l.sum ≤ k * l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at h
    have := ih h.2
    simp [List.length_cons]
    grind

theorem le_sum_of_forall_le (l : List Int) (k : Int) (h : ∀ x ∈ l, k ≤ x) :
    k * l.length ≤ l.sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at h
    have := ih h.2
    simp [List.length_cons]
    grind

/-- Every P2 word has a subtraction at height `≤ 0` (at or below the member level). -/
theorem p2_exists_low_subtraction (w : List Bool) (h : P2 w) :
    ∃ i, ∃ hi : i < w.length, w[i] = false ∧ mass (w.drop (i+1)) ≤ 0 := by
  by_cases hex : ∃ x ∈ sLevels w, x ≤ 0
  · obtain ⟨x, hx, hle⟩ := hex
    obtain ⟨i, hi, hb, hm⟩ := (mem_sLevels w x).1 hx
    exact ⟨i, hi, hb, by omega⟩
  · have hall : ∀ x ∈ sLevels w, 1 ≤ x := by
      intro x hx
      by_cases hle : x ≤ 0
      · exact False.elim (hex ⟨x, hx, hle⟩)
      · omega
    have hs := le_sum_of_forall_le _ 1 hall
    rw [sLevels_sum, sLevels_length] at hs
    have h1 := p2_sLevelSum w h
    have h2 := p2_sCount w h
    omega

/-- A P2 word all of whose subtractions are at height `≤ 0` has length 3. -/
theorem p2_length_three_of_low_subtractions (w : List Bool) (h : P2 w)
    (hlow : ∀ i, ∀ hi : i < w.length, w[i] = false → mass (w.drop (i+1)) ≤ 0) :
    w.length = 3 := by
  have hall : ∀ x ∈ sLevels w, x ≤ 0 := by
    intro x hx
    obtain ⟨i, hi, hb, hm⟩ := (mem_sLevels w x).1 hx
    have := hlow i hi hb
    omega
  have hs := sum_le_of_forall_le _ 0 hall
  rw [sLevels_sum] at hs
  have h1 := p2_sLevelSum w h
  have hc := (p2_count_identities w h).1
  have ho := LeadingRunSupply.ones_bounds w
  omega

theorem p2_length_three (w : List Bool) (h : P2 w) (hl : w.length = 3) :
    w = [true, true, false] := by
  match w, hl with
  | [a, b, c], _ =>
    obtain ⟨hm, hmo⟩ := h
    cases a <;> cases b <;> cases c <;> simp_all [mass, moment, sign]

/-- The only P2 word whose subtractions all lie at or below the member level is `AAS`. -/
theorem p2_eq_aas_of_low_subtractions (w : List Bool) (h : P2 w)
    (hlow : ∀ i, ∀ hi : i < w.length, w[i] = false → mass (w.drop (i+1)) ≤ 0) :
    w = [true, true, false] :=
  p2_length_three w h (p2_length_three_of_low_subtractions w h hlow)

/-- Every P2 word other than `AAS` (in particular every P2 window of lag at least 7) has a
subtraction strictly above the member level. -/
theorem p2_exists_high_subtraction (w : List Bool) (h : P2 w) (hne : w ≠ [true, true, false]) :
    ∃ i, ∃ hi : i < w.length, w[i] = false ∧ 1 ≤ mass (w.drop (i+1)) := by
  by_cases hex : ∃ i, ∃ hi : i < w.length, w[i] = false ∧ 1 ≤ mass (w.drop (i+1))
  · exact hex
  · apply False.elim
    apply hne
    apply p2_eq_aas_of_low_subtractions w h
    intro i hi hb
    by_cases hle : mass (w.drop (i+1)) ≤ 0
    · exact hle
    · exact False.elim (hex ⟨i, hi, hb, by omega⟩)

open LeadingRunSupply (past)

/-- Dropping the `i+1` newest letters of a window leaves the window of the clock `b - (i+1)`. -/
theorem past_drop (e : Int → Bool) (b : Int) (L i : Nat) :
    (past e b L).drop (i+1) = past e (b - ((i+1 : Nat) : Int)) (L - (i+1)) := by
  apply List.ext_getElem
  · simp [past]
  · intro j h1 h2
    simp [past]
    congr 1
    omega

/-- Stream form: a P2 window `past e b L` of length at least 4 (so not `AAS`) contains a
subtraction clock `c = b - (i+1)` whose height above the window start is at least 1, i.e.
`F c ≥ F (b - L) + 1 = F b`: the subtraction lies strictly above the member level. -/
theorem past_exists_high_subtraction (e : Int → Bool) (b : Int) (L : Nat)
    (h : P2 (past e b L)) (hL : 4 ≤ L) :
    ∃ i, i < L ∧ e (b - ((i+1 : Nat) : Int)) = false ∧
      1 ≤ mass (past e (b - ((i+1 : Nat) : Int)) (L - (i+1))) := by
  have hne : past e b L ≠ [true, true, false] := by
    intro heq
    have := congrArg List.length heq
    simp [past] at this
    omega
  obtain ⟨i, hi, hb, hm⟩ := p2_exists_high_subtraction _ h hne
  have hiL : i < L := by simpa [past] using hi
  refine ⟨i, hiL, ?_, ?_⟩
  · simpa [past] using hb
  · rw [← past_drop]; exact hm

/-- Stream form of the level sum: the subtraction clocks of a P2 window `past e b L` have heights
above the window start summing to `(L - 3) / 4`. -/
theorem past_sLevelSum (e : Int → Bool) (b : Int) (L : Nat) (h : P2 (past e b L)) :
    4 * sLevelSum (past e b L) = (L : Int) - 3 := by
  have := p2_sLevelSum _ h
  simpa [past] using this

/-- Stream form of the AAS characterisation: if no subtraction clock `c = b - (i+1)` of the P2 window
`past e b L` lies above the member level (its height `F c - F (b - L)` is `≤ 0`), the window is `AAS`.
In a finite closed component whose walk maximum is attained only at the newest member `b` (so
every window clock has `F c ≤ F b - 1`), this makes the newest window `AAS`. -/
theorem past_eq_aas_of_low_subtractions (e : Int → Bool) (b : Int) (L : Nat)
    (h : P2 (past e b L))
    (hlow : ∀ i, i < L → e (b - ((i+1 : Nat) : Int)) = false →
      mass (past e (b - ((i+1 : Nat) : Int)) (L - (i+1))) ≤ 0) :
    past e b L = [true, true, false] := by
  apply p2_eq_aas_of_low_subtractions _ h
  intro i hi hb
  have hiL : i < L := by simpa [past] using hi
  rw [past_drop]
  exact hlow i hiL (by simpa [past] using hb)

end Recaman.P2SubtractionLevelSum
