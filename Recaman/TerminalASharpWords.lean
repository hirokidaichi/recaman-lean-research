import Recaman.OneSSMultiplicity

namespace Recaman.TerminalASharpWords

open LeadingRunSupply SSFreeSupply OneSSMultiplicity
open ShortPeriodicSupply (sign)

/-! The explicit all-q construction is independent of the terminal-A upper
bound. Minimality is proved by classifying every proper mass-one prefix. -/

def body (q n : Nat) : List Bool :=
  ([true, true, true, false] ++ alt false n) ++
    (List.replicate q false ++ List.replicate (q - 1) true)

def pairCount (q : Nat) : Nat := q * q - 2 * q - 2

def word (q : Nat) : List Bool :=
  if 3 ≤ q then body q (pairCount q) else
    match q with
    | 0 => [true, true, false]
    | 1 => [false, true, true, true, true, false, false]
    | _ => [true, true, true, false, false, false, true, false, true, false, true]

theorem mass_replicate_S (q : Nat) : mass (List.replicate q false) = -(q : Int) := by
  induction q with
  | zero => simp
  | succ q ih => simp [List.replicate_succ, sign, ih]; omega

theorem twice_moment_replicate_S (q : Nat) :
    2 * moment (List.replicate q false) = -(q : Int) * (q + 1) := by
  induction q with
  | zero => simp [moment]
  | succ q ih =>
    simp only [List.replicate_succ, moment, mass_replicate_S, sign,
      Bool.false_eq_true, ↓reduceIte, Int.natCast_add, Int.cast_ofNat_Int]
    grind

theorem alt_S_negative_prefix (n d : Nat) (hd : d ≤ 2 * n)
    (hm : mass ((alt false n).take d) = -1) :
    ∃ i, 1 ≤ i ∧ i ≤ n ∧ d + 1 = 2 * i ∧
      moment ((alt false n).take d) = -(i : Int) := by
  induction n generalizing d with
  | zero =>
    have hz : d = 0 := by omega
    subst d
    simp [alt] at hm
  | succ n ih =>
    cases d with
    | zero => simp at hm
    | succ d =>
      cases d with
      | zero => exact ⟨1, by omega, by omega, rfl, by simp [alt, moment, sign]⟩
      | succ d =>
        have hm' : mass ((alt false n).take d) = -1 := by
          simp [alt, mass_cons, sign] at hm
          omega
        obtain ⟨i, hi, hin, hid, him⟩ := ih d (by omega) hm'
        refine ⟨i + 1, by omega, by omega, by omega, ?_⟩
        simp only [alt, Bool.not_false, List.take_succ_cons, moment, mass_cons,
          sign, Bool.false_eq_true, ↓reduceIte, hm', him, Int.natCast_add,
          Int.cast_ofNat_Int]
        omega

theorem head_mass : mass [true, true, true, false] = 2 := by decide
theorem head_moment : moment [true, true, true, false] = 2 := by decide

theorem core_mass (n : Nat) : mass ([true, true, true, false] ++ alt false n) = 2 := by
  rw [mass_append, head_mass, alt_mass]; omega

theorem core_moment (n : Nat) :
    moment ([true, true, true, false] ++ alt false n) = (n : Int) + 2 := by
  rw [moment_append, head_moment, alt_S_moment, alt_mass]; simp; omega

theorem body_length (q n : Nat) : (body q n).length = 4 + 2 * n + q + (q - 1) := by
  simp [body, alt_length]; omega

theorem body_mass (q n : Nat) (hq : 1 ≤ q) : mass (body q n) = 1 := by
  have ht : ((q - 1 : Nat) : Int) = (q : Int) - 1 := by omega
  rw [body, mass_append, core_mass, mass_append, mass_replicate_S, mass_replicate_A, ht]
  omega

theorem body_twice_moment (q n : Nat) (hq : 1 ≤ q) :
    2 * moment (body q n) = 2 * ((q : Int) * q - 2 * q - 2 - n) := by
  have ht : ((q - 1 : Nat) : Int) = (q : Int) - 1 := by omega
  have hs := twice_moment_replicate_S q
  have ha := twice_moment_replicate_A (q - 1)
  rw [body, moment_append, core_moment, moment_append]
  simp only [mass_append,
    mass_replicate_S, mass_replicate_A, List.length_append,
    List.length_cons, List.length_nil, alt_length, List.length_replicate,
    Int.natCast_add, Int.natCast_mul, Int.cast_ofNat_Int, ht]
  rw [ht] at ha
  grind

theorem take_body_alt (q n j : Nat) (hj : 4 ≤ j) (hlen : j ≤ 4 + 2 * n) :
    (body q n).take j = [true, true, true, false] ++ (alt false n).take (j - 4) := by
  rw [body, List.take_append_of_le_length (by simp [alt_length]; omega),
    List.take_append, List.take_of_length_le (by simp; omega)]
  rfl

theorem take_body_S (q n j : Nat) (hj : 4 + 2 * n ≤ j)
    (hlen : j ≤ 4 + 2 * n + q) :
    (body q n).take j = ([true, true, true, false] ++ alt false n) ++
      List.replicate (j - (4 + 2 * n)) false := by
  rw [body, List.take_append, List.take_of_length_le (by simp [alt_length]; omega)]
  simp only [List.length_append, List.length_cons, List.length_nil, alt_length]
  rw [List.take_append_of_le_length (by simp; omega), List.take_replicate]
  rw [Nat.min_eq_left (by omega)]

theorem take_body_A (q n j : Nat) (hj : 4 + 2 * n + q ≤ j)
    (hlen : j ≤ (body q n).length) :
    (body q n).take j = (([true, true, true, false] ++ alt false n) ++
      List.replicate q false) ++ List.replicate (j - (4 + 2 * n + q)) true := by
  rw [body, ← List.append_assoc, List.take_append,
    List.take_of_length_le (by simp [alt_length]; omega)]
  simp only [List.length_append, List.length_cons, List.length_nil,
    alt_length, List.length_replicate]
  rw [List.take_replicate, Nat.min_eq_left (by rw [body_length] at hlen; omega)]

/-- Complete classification, including the exact nonzero moments. -/
theorem proper_mass_one_prefix (q n j : Nat) (hq : 3 ≤ q)
    (hj : 0 < j) (hlen : j < (body q n).length)
    (hm : mass ((body q n).take j) = 1) :
    (j = 1 ∧ moment ((body q n).take j) = 1) ∨
    (∃ i, 1 ≤ i ∧ i ≤ n ∧ j = 2 * i + 3 ∧
      moment ((body q n).take j) = -(i : Int) - 2) ∨
    (j = 2 * n + 5 ∧ moment ((body q n).take j) = -(n : Int) - 3) := by
  by_cases hhead : j ≤ 4
  · have hc : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
    rcases hc with rfl | rfl | rfl | rfl
    · exact Or.inl ⟨rfl, by simp [body, List.take, moment, sign]⟩
    all_goals simp [body, List.take, mass_cons, sign] at hm
  · by_cases halt : j ≤ 4 + 2 * n
    · have he := take_body_alt q n j (by omega) halt
      rw [he, mass_append, head_mass] at hm
      have hminus : mass ((alt false n).take (j - 4)) = -1 := by omega
      obtain ⟨i, hi, hin, hid, him⟩ := alt_S_negative_prefix n (j - 4) (by omega) hminus
      refine Or.inr (Or.inl ⟨i, hi, hin, by omega, ?_⟩)
      rw [he, moment_append, head_moment, him, hminus]
      simp; omega
    · by_cases hs : j ≤ 4 + 2 * n + q
      · have he := take_body_S q n j (by omega) hs
        rw [he, mass_append, core_mass, mass_replicate_S] at hm
        have hd : j - (4 + 2 * n) = 1 := by omega
        refine Or.inr (Or.inr ⟨by omega, ?_⟩)
        rw [he, hd, moment_append, core_moment]
        simp [moment, alt_length, sign]
        omega
      · have he := take_body_A q n j (by omega) (by omega)
        rw [he, mass_append, mass_append, core_mass, mass_replicate_S,
          mass_replicate_A] at hm
        rw [body_length] at hlen
        omega

theorem body_minimal (q n : Nat) (hq : 3 ≤ q) :
    ∀ j, 0 < j → j < (body q n).length → ¬ P2 ((body q n).take j) := by
  intro j hj hlen hp
  rcases proper_mass_one_prefix q n j hq hj hlen hp.1 with h | h | h
  · have := hp.2; omega
  · obtain ⟨i, _, _, _, hi⟩ := h; have := hp.2; omega
  · have := hp.2; omega

theorem alt_S_prefix_at_pair (n i : Nat) (hi : 1 ≤ i) (hin : i ≤ n) :
    mass ((alt false n).take (2 * i - 1)) = -1 ∧
      moment ((alt false n).take (2 * i - 1)) = -(i : Int) := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    cases i with
    | zero => omega
    | succ i =>
      cases i with
      | zero => simp [alt, moment, mass_cons, sign]
      | succ i =>
        have ht : 2 * (i + 1 + 1) - 1 = (2 * (i + 1) - 1) + 2 := by omega
        have hh := ih (i + 1) (by omega) (by omega)
        rw [ht]
        simp only [alt, Bool.not_false, List.take_succ_cons, moment, mass_cons,
          sign, Bool.false_eq_true, ↓reduceIte, hh.1, hh.2,
          Int.natCast_add, Int.cast_ofNat_Int]
        constructor <;> omega

/-- The classified positions are also realized: no extra candidate positions
were introduced in the forward classification. -/
theorem proper_mass_one_positions_iff (q n j : Nat) (hq : 3 ≤ q)
    (hj : 0 < j) (hlen : j < (body q n).length) :
    mass ((body q n).take j) = 1 ↔
      j = 1 ∨ (∃ i, 1 ≤ i ∧ i ≤ n ∧ j = 2 * i + 3) ∨ j = 2 * n + 5 := by
  constructor
  · intro hm
    rcases proper_mass_one_prefix q n j hq hj hlen hm with h | h | h
    · exact Or.inl h.1
    · obtain ⟨i, hi, hin, he, _⟩ := h
      exact Or.inr (Or.inl ⟨i, hi, hin, he⟩)
    · exact Or.inr (Or.inr h.1)
  · intro hp
    rcases hp with rfl | h | rfl
    · simp [body, List.take, mass_cons, sign]
    · obtain ⟨i, hi, hin, rfl⟩ := h
      rw [take_body_alt q n (2 * i + 3) (by omega) (by omega), mass_append, head_mass]
      have he : 2 * i + 3 - 4 = 2 * i - 1 := by omega
      rw [he, (alt_S_prefix_at_pair n i hi hin).1]
      omega
    · rw [take_body_S q n (2 * n + 5) (by omega) (by omega), mass_append,
        core_mass, mass_replicate_S]
      have he : 2 * n + 5 - (4 + 2 * n) = 1 := by omega
      rw [he]
      omega

theorem square_ge_twice_add_three (q : Nat) (hq : 3 ≤ q) : 2 * q + 3 ≤ q * q := by
  have he : q = (q - 3) + 3 := by omega
  rw [he]
  simp only [Nat.add_mul, Nat.mul_add]
  omega

theorem pairCount_equation (q : Nat) (hq : 3 ≤ q) :
    1 ≤ pairCount q ∧ pairCount q + 2 * q + 2 = q * q := by
  have hs := square_ge_twice_add_three q hq
  simp only [pairCount]
  omega

theorem pairCount_int (q : Nat) (hq : 3 ≤ q) :
    (pairCount q : Int) = (q : Int) * q - 2 * q - 2 := by
  have he := congrArg (fun k : Nat => (k : Int)) (pairCount_equation q hq).2
  simp only [Int.natCast_add, Int.natCast_mul, Int.cast_ofNat_Int] at he
  omega

theorem body_P2 (q : Nat) (hq : 3 ≤ q) : P2 (body q (pairCount q)) := by
  refine ⟨body_mass q _ (by omega), ?_⟩
  have h := body_twice_moment q (pairCount q) (by omega)
  rw [pairCount_int q hq] at h
  omega

theorem body_sharp_length (q : Nat) (hq : 3 ≤ q) :
    (body q (pairCount q)).length = 2 * q * q - 2 * q - 1 := by
  have he := (pairCount_equation q hq).2
  rw [body_length, Nat.mul_assoc]
  omega

theorem ssCount_replicate_A (t : Nat) : ssCount (List.replicate t true) = 0 := by
  induction t with
  | zero => rfl
  | succ t ih => simp [List.replicate_succ, ssCount, ih]

theorem ssCount_S_then_A (q t : Nat) :
    ssCount (List.replicate q false ++ List.replicate t true) = q - 1 := by
  induction q with
  | zero => simp [ssCount_replicate_A]
  | succ q ih =>
    cases q with
    | zero =>
      cases t with
      | zero => rfl
      | succ t => simp [List.replicate_succ, ssCount, ssCount_replicate_A]
    | succ q =>
      change 1 + ssCount (List.replicate (q + 1) false ++ List.replicate t true) = q + 1
      rw [ih]
      omega

theorem body_ssCount (q n : Nat) (hq : 1 ≤ q) (hn : 1 ≤ n) : ssCount (body q n) = q := by
  have he : n = (n - 1) + 1 := by omega
  rw [body, he]
  simp only [alt, Bool.not_false, List.cons_append, List.nil_append,
    ssCount, List.head?_cons, Bool.true_eq_false,
    false_and, and_true, ↓reduceIte, Nat.zero_add]
  rw [ssCount_pre_alt, ssCount_S_then_A]
  simp
  omega

theorem terminal_S_A_length (v : List Bool) (q t : Nat) (hq : 1 ≤ q) :
    ((v ++ (List.replicate q false ++ List.replicate t true)).reverse.takeWhile id).length = t := by
  have he : q = (q - 1) + 1 := by omega
  simp only [List.reverse_append, List.reverse_replicate]
  rw [he, List.replicate_succ]
  simp [List.takeWhile]

theorem body_terminal_length (q n : Nat) (hq : 1 ≤ q) :
    ((body q n).reverse.takeWhile id).length = q - 1 := by
  exact terminal_S_A_length _ q (q - 1) hq

local instance (w : List Bool) : Decidable (P2 w) :=
  inferInstanceAs (Decidable (mass w = 1 ∧ moment w = 0))

theorem small_word_properties (q : Nat) (hq : q < 3) :
    P2 (word q) ∧ ssCount (word q) = q ∧
      ((word q).reverse.takeWhile id).length = q - 1 ∧
      (∀ j, 0 < j → j < (word q).length → ¬ P2 ((word q).take j)) := by
  have hcases : q = 0 ∨ q = 1 ∨ q = 2 := by omega
  have hfinite : ((List.range (word q).length).all
      fun j => decide (j = 0 ∨ ¬ P2 ((word q).take j))) = true := by
    rcases hcases with rfl | rfl | rfl <;> decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · rcases hcases with rfl | rfl | rfl <;> decide
  · rcases hcases with rfl | rfl | rfl <;> decide
  · rcases hcases with rfl | rfl | rfl <;> decide
  · intro j hj hlen
    have hmem : j ∈ List.range (word q).length := by simpa using hlen
    have hx := of_decide_eq_true (List.all_eq_true.mp hfinite j hmem)
    exact hx.resolve_left (by omega)

/-- The fixed explicit construction satisfies every requirement for all q. -/
theorem word_properties (q : Nat) :
    P2 (word q) ∧ ssCount (word q) = q ∧
      ((word q).reverse.takeWhile id).length = q - 1 ∧
      (∀ j, 0 < j → j < (word q).length → ¬ P2 ((word q).take j)) := by
  by_cases hq : 3 ≤ q
  · have hn := (pairCount_equation q hq).1
    simp only [word, if_pos hq]
    exact ⟨body_P2 q hq, body_ssCount q _ (by omega) hn,
      body_terminal_length q _ (by omega), body_minimal q _ hq⟩
  · exact small_word_properties q (by omega)

theorem exists_minimal_p2_with_terminal_length (q : Nat) :
    ∃ w : List Bool, P2 w ∧ ssCount w = q ∧
      (w.reverse.takeWhile id).length = q - 1 ∧
      (∀ j, 0 < j → j < w.length → ¬ P2 (w.take j)) := by
  exact ⟨word q, word_properties q⟩

/-- Arbitrarily long terminal runs already occur among abstract minimal P2
words; this does not assert realization in any Recaman orbit. -/
theorem exists_minimal_p2_terminal_run (t : Nat) :
    ∃ w : List Bool, P2 w ∧ ssCount w = t + 1 ∧
      (w.reverse.takeWhile id).length = t ∧
      (∀ j, 0 < j → j < w.length → ¬ P2 (w.take j)) := by
  obtain ⟨w, hp, hss, ht, hmin⟩ := exists_minimal_p2_with_terminal_length (t + 1)
  exact ⟨w, hp, hss, by simpa using ht, hmin⟩

end Recaman.TerminalASharpWords
