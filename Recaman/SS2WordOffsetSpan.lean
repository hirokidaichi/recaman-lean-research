import Recaman.OneSSMultiplicity
import Recaman.LagSevenDonorCoverage

/-!
# Fixed-SS2 minimal words with unbounded marked-to-oldest S span

For every k, the newest-first word (SA)^k SAAASSAAASS (AS)^(3k) is
minimal P2, has exactly two overlapping SS pairs, and remains NoSAAS
after adjoining the current A. Its first and last bits are S and its
length is 8k+11. The marked first S is a word position, not an owner in
a tight Hall family. No periodicity, orbit realization or capacity claim
is made. The alternating padding lemmas are reused from E-122.
-/

namespace Recaman.SS2WordOffsetSpan

open LeadingRunSupply SSFreeSupply
open OneSSMultiplicity (ssCount alt_length alt_append alt_A_moment
  ssCount_pre_alt ssCount_post_alt alt_S_prefix_nonpositive saasCount
  saasCount_pre_alt saasCount_post_alt saas_occurrence_positive)
open LagSevenDonorCoverage (oldestOffset)

def core : List Bool :=
  [false, true, true, true, false, false, true, true, true, false, false]

def word (k : Nat) : List Bool := alt false k ++ core ++ alt true (3*k)

theorem core_mass : mass core = 1 := by decide
theorem core_moment : moment core = 0 := by decide
theorem core_length : core.length = 11 := by decide

theorem word_length (k : Nat) : (word k).length = 8*k+11 := by
  simp [word, core_length, alt_length]
  omega

theorem word_P2 (k : Nat) : P2 (word k) := by
  constructor
  · simp [word, mass_append, alt_mass, core_mass]
  · simp only [word, moment_append, alt_mass, core_mass, core_moment,
      alt_S_moment, alt_A_moment, List.length_append, alt_length,
      Int.mul_zero, Int.add_zero, Int.mul_one, Int.natCast_mul, Int.cast_ofNat_Int]
    omega

/-- A mass-zero prefix of an AS block consists of whole pairs. -/
theorem alt_A_zero_prefix (n d : Nat) (hd : d ≤ 2*n)
    (hm : mass ((alt true n).take d) = 0) :
    ∃ i, i ≤ n ∧ d = 2*i ∧ (alt true n).take d = alt true i := by
  induction n generalizing d with
  | zero =>
    have : d = 0 := by omega
    subst d
    exact ⟨0, by omega, rfl, rfl⟩
  | succ n ih =>
    cases d with
    | zero => exact ⟨0, by omega, rfl, rfl⟩
    | succ d =>
      cases d with
      | zero => simp [alt, ShortPeriodicSupply.sign] at hm
      | succ d =>
        have hm' : mass ((alt true n).take d) = 0 := by
          simp [alt, ShortPeriodicSupply.sign] at hm
          omega
        obtain ⟨i, hi, heq, ht⟩ := ih d (by omega) hm'
        refine ⟨i+1, by omega, by omega, ?_⟩
        simpa [alt] using congrArg (fun w => true :: false :: w) ht

theorem alt_take_pairs (b : Bool) (n i : Nat) (hi : i ≤ n) :
    (alt b n).take (2*i) = alt b i := by
  have hn : n = i+(n-i) := by omega
  rw [hn, alt_append]
  have ht := List.take_append_of_le_length (l₁ := alt b i) (l₂ := alt b (n-i))
    (i := 2*i) (by simp only [alt_length]; omega)
  rw [ht, List.take_of_length_le (by simp only [alt_length]; omega)]

/-- Complete table for the fixed core, including its final prefix. -/
theorem core_mass_one_prefix (r : Nat) (hr : r ≤ 11)
    (hm : mass (core.take r) = 1) :
    (r = 3 ∧ moment (core.take r) = 4) ∨
    (r = 5 ∧ moment (core.take r) = 3) ∨
    (r = 7 ∧ moment (core.take r) = 4) ∨
    (r = 11 ∧ moment (core.take r) = 0) := by
  have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨
      r=7 ∨ r=8 ∨ r=9 ∨ r=10 ∨ r=11 := by omega
  rcases hc with h | h | h | h | h | h | h | h | h | h | h | h
  all_goals subst r
  all_goals simp [core, mass_cons, moment, ShortPeriodicSupply.sign] at hm ⊢

/-- All proper mass-one prefixes and their moments; no bound on k or d. -/
theorem proper_mass_one_prefix (k d : Nat) (hd : d < (word k).length)
    (hm : mass ((word k).take d) = 1) :
    (d = 2*k+3 ∧ moment ((word k).take d) = 3*(k : Int)+4) ∨
    (d = 2*k+5 ∧ moment ((word k).take d) = 3*(k : Int)+3) ∨
    (d = 2*k+7 ∧ moment ((word k).take d) = 3*(k : Int)+4) ∨
    (∃ i, i < 3*k ∧ d = 2*k+11+2*i ∧
      moment ((word k).take d) = 3*(k : Int)-(i : Int)) := by
  by_cases hshort : d ≤ 2*k
  · have heq : (word k).take d = (alt false k).take d := by
      rw [word, List.append_assoc,
        List.take_append_of_le_length (by rw [alt_length]; exact hshort)]
    rw [heq] at hm
    have hbound := alt_S_prefix_nonpositive k d
    omega
  · let r := d-2*k
    have hdeq : d = 2*k+r := by dsimp [r]; omega
    have heq : (word k).take d = alt false k ++ (core ++ alt true (3*k)).take r := by
      rw [word, List.append_assoc, List.take_append,
        List.take_of_length_le (by rw [alt_length]; omega), alt_length]
    by_cases hr : r ≤ 11
    · have ht : (core ++ alt true (3*k)).take r = core.take r :=
        List.take_append_of_le_length (by rw [core_length]; exact hr)
      have hmcore : mass (core.take r) = 1 := by
        simpa [heq, ht, mass_append, alt_mass] using hm
      have hM : moment ((word k).take d) = 3*(k : Int)+moment (core.take r) := by
        simp only [heq, ht, moment_append, alt_S_moment, alt_length, hmcore,
          Int.mul_one, Int.natCast_mul, Int.cast_ofNat_Int]
        omega
      rcases core_mass_one_prefix r hr hmcore with h | h | h | h
      · exact Or.inl ⟨by omega, by omega⟩
      · exact Or.inr (Or.inl ⟨by omega, by omega⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))
      · refine Or.inr (Or.inr (Or.inr ⟨0, ?_, by omega, by simpa using hM.trans (by rw [h.2]; omega)⟩))
        rw [word_length] at hd
        omega
    · have ht : (core ++ alt true (3*k)).take r = core ++ (alt true (3*k)).take (r-11) := by
        rw [List.take_append, List.take_of_length_le (by rw [core_length]; omega), core_length]
      have hm0 : mass ((alt true (3*k)).take (r-11)) = 0 := by
        simp only [heq, ht, mass_append, alt_mass, core_mass] at hm
        omega
      have hlen : r-11 ≤ 2*(3*k) := by rw [word_length] at hd; omega
      obtain ⟨i, hi, hir, htake⟩ := alt_A_zero_prefix (3*k) (r-11) hlen hm0
      refine Or.inr (Or.inr (Or.inr ⟨i, ?_, by omega, ?_⟩))
      · rw [word_length] at hd
        omega
      · simp only [heq, ht, htake, moment_append, mass_append, alt_mass,
          core_mass, core_moment, alt_S_moment, alt_A_moment, alt_length,
          Int.mul_zero, Int.add_zero, Int.mul_one, Int.natCast_mul, Int.cast_ofNat_Int]
        omega

/-- Conversely, every listed position really is a proper mass-one prefix. -/
theorem proper_mass_one_positions_iff (k d : Nat) :
    (d < (word k).length ∧ mass ((word k).take d) = 1) ↔
    d = 2*k+3 ∨ d = 2*k+5 ∨ d = 2*k+7 ∨
      ∃ i, i < 3*k ∧ d = 2*k+11+2*i := by
  constructor
  · rintro ⟨hd, hm⟩
    rcases proper_mass_one_prefix k d hd hm with h | h | h | ⟨i, hi, h, _⟩
    · exact Or.inl h.1
    · exact Or.inr (Or.inl h.1)
    · exact Or.inr (Or.inr (Or.inl h.1))
    · exact Or.inr (Or.inr (Or.inr ⟨i, hi, h⟩))
  · intro h
    have hc (r : Nat) (hr : r ≤ 11) :
        (word k).take (2*k+r) = alt false k ++ core.take r := by
      rw [word, List.append_assoc, List.take_append,
        List.take_of_length_le (by rw [alt_length]; omega), alt_length]
      have hs : 2*k+r-2*k = r := by omega
      rw [hs, List.take_append_of_le_length (by rw [core_length]; exact hr)]
    rcases h with h | h | h | ⟨i, hi, h⟩
    · subst d
      exact ⟨by rw [word_length]; omega, by rw [hc 3 (by omega)]; simp [mass_append, alt_mass]; decide⟩
    · subst d
      exact ⟨by rw [word_length]; omega, by rw [hc 5 (by omega)]; simp [mass_append, alt_mass]; decide⟩
    · subst d
      exact ⟨by rw [word_length]; omega, by rw [hc 7 (by omega)]; simp [mass_append, alt_mass]; decide⟩
    · subst d
      constructor
      · rw [word_length]; omega
      · have ht : (word k).take (2*k+11+2*i) = (alt false k ++ core) ++ alt true i := by
          rw [word, List.take_append, List.take_of_length_le (by simp [alt_length, core_length])]
          have hs : 2*k+11+2*i-(alt false k ++ core).length = 2*i := by
            simp [alt_length, core_length]
          rw [hs, alt_take_pairs true (3*k) i (by omega)]
        simp [ht, mass_append, alt_mass, core_mass]

theorem word_minimum (k d : Nat) (hd : d < (word k).length) :
    ¬ P2 ((word k).take d) := by
  intro hP
  rcases proper_mass_one_prefix k d hd hP.1 with h | h | h | ⟨i, hi, _, hM⟩
  all_goals have hz := hP.2
  all_goals omega

theorem word_ssCount (k : Nat) : ssCount (word k) = 2 := by
  rw [word, ssCount_post_alt, ssCount_pre_alt]
  decide

theorem word_saasCount_zero (k : Nat) : saasCount (word k) = 0 := by
  have hpost := saasCount_post_alt (3*k)
    (alt false k ++ [false, true, true, true, false, false, true, true, true, false])
  have hpre := saasCount_pre_alt k [true, true, true, false, false, true, true, true, false, false]
  have hc : saasCount core = 0 := by decide
  have hpost' : saasCount (word k) = saasCount (alt false k ++ core) := by
    simpa [word, core, List.append_assoc] using hpost
  exact hpost'.trans (hpre.trans hc)

theorem word_noSAAS (k : Nat) : NoSAAS (word k) := by
  intro u v heq
  have hpos := saas_occurrence_positive u v
  rw [← heq, word_saasCount_zero] at hpos
  omega

theorem history_noSAAS (k : Nat) : NoSAAS (true :: word k) := by
  intro u v heq
  cases u with
  | nil => simp at heq
  | cons b u => exact word_noSAAS k u v (List.cons.inj heq).2

theorem word_newest_S (k : Nat) : (word k)[0]? = some false := by
  cases k <;> rfl

theorem word_ends_S (k : Nat) : ∃ u, word k = u ++ [false] := by
  cases k with
  | zero => exact ⟨[false, true, true, true, false, false, true, true, true, false], rfl⟩
  | succ k =>
    refine ⟨(alt false (k+1) ++ core) ++ alt true (3*k+2) ++ [true], ?_⟩
    have heq : 3*(k+1) = (3*k+2)+1 := by omega
    rw [word, heq, alt_append true (3*k+2) 1]
    simp [alt, List.append_assoc]

/-- The recursive oldest-offset function selects the final S, not a marker. -/
theorem oldestOffset_append_S (u : List Bool) :
    oldestOffset (u ++ [false]) = u.length+1 := by
  induction u with
  | nil => rfl
  | cons b u ih => simp [oldestOffset, ih, Nat.add_assoc]

theorem word_oldestOffset (k : Nat) : oldestOffset (word k) = 8*k+11 := by
  obtain ⟨u, hu⟩ := word_ends_S k
  have hl := word_length k
  rw [hu, List.length_append] at hl
  rw [hu, oldestOffset_append_S]
  simpa using hl

/-- The selected offset holds S, and there are no older positions in the word. -/
theorem word_true_oldest_S (k : Nat) :
    (word k)[oldestOffset (word k)-1]? = some false ∧
      ∀ j, oldestOffset (word k) ≤ j → (word k)[j]? = none := by
  obtain ⟨u, hu⟩ := word_ends_S k
  constructor
  · rw [hu, oldestOffset_append_S]
    simp
  · intro j hj
    rw [word_oldestOffset] at hj
    apply List.getElem?_eq_none
    rw [word_length]
    exact hj

theorem word_terminal_length (k : Nat) :
    ((word k).reverse.takeWhile id).length = 0 := by
  obtain ⟨u, hu⟩ := word_ends_S k
  simp [hu, List.reverse_append]

theorem word_span (k : Nat) : oldestOffset (word k)-1 = 8*k+10 := by
  rw [word_oldestOffset]
  omega

/-- An explicit witness for every constant, retaining all word premises.
The newest S at offset 1 is not asserted to be an owner. -/
theorem exists_unbounded_span (C0 : Nat) : ∃ k : Nat,
    P2 (word k) ∧
    (∀ d, 0 < d → d < (word k).length → ¬ P2 ((word k).take d)) ∧
    ssCount (word k) = 2 ∧ NoSAAS (true :: word k) ∧
    (word k).length = 8*k+11 ∧ (word k)[0]? = some false ∧
    oldestOffset (word k) = 8*k+11 ∧
    (word k)[oldestOffset (word k)-1]? = some false ∧
    ((word k).reverse.takeWhile id).length = 0 ∧
    oldestOffset (word k)-1 = 8*k+10 ∧ C0 < oldestOffset (word k)-1 := by
  refine ⟨C0, word_P2 C0, fun d _ hd => word_minimum C0 d hd,
    word_ssCount C0, history_noSAAS C0, word_length C0, word_newest_S C0,
    word_oldestOffset C0, (word_true_oldest_S C0).1, word_terminal_length C0,
    word_span C0, ?_⟩
  rw [word_span]
  omega

end Recaman.SS2WordOffsetSpan
