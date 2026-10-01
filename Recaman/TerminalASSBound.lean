import Recaman.LowSSEndpoint
import Recaman.FirstP2EndingS

namespace Recaman.TerminalASSBound

open LeadingRunSupply OneSSMultiplicity LowSSEndpoint
open ShortPeriodicSupply (sign)

/-! All-length terminal-A bounds for P2 words. The terminal decomposition
contains an S, so its A suffix is maximal. SS pairs are counted with overlap.
The prefix ceiling used by FirstP2EndingS is derived, not assumed. -/

theorem all_A_of_no_S (w : List Bool) (h : false ∉ w) :
    w = List.replicate w.length true := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    cases b with
    | false => simp at h
    | true =>
      simp at h
      rw [List.length_cons, List.replicate_succ]
      exact congrArg (List.cons true) (ih h)

theorem exists_terminal_decomposition_of_S (w : List Bool) (h : false ∈ w) :
    ∃ u t, w = (u ++ [false]) ++ List.replicate t true := by
  rcases List.eq_nil_or_concat w with hw | ⟨u, b, hw⟩
  · simp [hw] at h
  · simp only [List.concat_eq_append] at hw
    subst w
    cases b with
    | false => exact ⟨u, 0, by simp⟩
    | true =>
      have hu : false ∈ u := by simpa using h
      obtain ⟨v, t, hv⟩ := exists_terminal_decomposition_of_S u hu
      exact ⟨v, t + 1, by simp [hv, List.replicate_succ', List.append_assoc]⟩
termination_by w.length
decreasing_by all_goals simp_all

/-- No P2 word is excluded by the terminal-S/A representation. -/
theorem p2_terminal_decomposition (w : List Bool) (hp : P2 w) :
    ∃ u t, w = (u ++ [false]) ++ List.replicate t true := by
  apply exists_terminal_decomposition_of_S
  by_cases hs : false ∈ w
  · exact hs
  · have hw := all_A_of_no_S w hs
    exact False.elim (not_p2_all_A w.length (hw ▸ hp))

/-- Reverse/takeWhile counts exactly the maximal terminal run, in both
representations; therefore the decomposition does not choose a shorter suffix. -/
theorem terminal_run_length (u : List Bool) (t : Nat) :
    (((u ++ [false]) ++ List.replicate t true).reverse.takeWhile id).length = t := by
  simp only [List.reverse_append, List.reverse_replicate, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.singleton_append]
  induction t with
  | zero => simp
  | succ t _ => simp [List.replicate_succ, List.takeWhile]

theorem terminal_length_unique (u v : List Bool) (t s : Nat)
    (he : (u ++ [false]) ++ List.replicate t true =
      (v ++ [false]) ++ List.replicate s true) : t = s := by
  have ht := terminal_run_length u t
  have hs := terminal_run_length v s
  rw [he] at ht
  omega

theorem ssCount_post_As (w : List Bool) (t : Nat) :
    ssCount (w ++ List.replicate t true) = ssCount w := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [List.replicate_succ', ← List.append_assoc, ssCount_post_A, ih]

theorem mass_ge_neg_ss_sub_one (w : List Bool) :
    -(ssCount w : Int) - 1 ≤ mass w := by
  have h := mass_ending_A w
  simp only [ssCount_post_A, mass_append, mass_cons, mass_nil, sign,
    ↓reduceIte] at h
  omega

/-- Uniform suffix bound: before the terminal run use the SS budget;
inside the run use nonnegativity. `c≤0` includes the empty suffix. -/
theorem terminal_suffix_mass_lower (u : List Bool) (t q : Nat) (c : Int)
    (hc : c ≤ 0) (hct : c ≤ (t : Int) - q - 1)
    (hss : ssCount ((u ++ [false]) ++ List.replicate t true) ≤ q) :
    ∀ j, c ≤ mass (((u ++ [false]) ++ List.replicate t true).drop j) := by
  induction u with
  | nil =>
    intro j
    cases j with
    | zero => simp [mass_cons, mass_replicate_A, sign]; omega
    | succ j =>
      simp only [List.nil_append, List.singleton_append, List.drop_succ_cons]
      rw [List.drop_replicate, mass_replicate_A]
      omega
  | cons b u ih =>
    have htail := ssCount_tail_le b ((u ++ [false]) ++ List.replicate t true)
    have hsmall : ssCount ((u ++ [false]) ++ List.replicate t true) ≤ q := by
      simpa only [List.cons_append] using Nat.le_trans htail hss
    intro j
    cases j with
    | zero =>
      have hm := mass_ge_neg_ss_sub_one ((b :: u) ++ [false])
      have hq : ssCount ((b :: u) ++ [false]) ≤ q := by
        simpa only [ssCount_post_As] using hss
      rw [List.drop_zero, mass_append, mass_replicate_A]
      omega
    | succ j =>
      simpa only [List.cons_append, List.drop_succ_cons] using ih hsmall j

theorem moment_nonneg_of_suffix_mass (w : List Bool)
    (h : ∀ j, 0 ≤ mass (w.drop j)) : 0 ≤ moment w := by
  induction w with
  | nil => simp [moment]
  | cons b w ih =>
    have ht : ∀ j, 0 ≤ mass (w.drop j) := by
      intro j
      simpa only [List.drop_succ_cons] using h (j + 1)
    have hi := ih ht
    have hm := h 0
    simp only [List.drop_zero, mass_cons] at hm
    simp only [moment]
    omega

theorem mass_le_moment_of_suffix_mass (w : List Bool)
    (h : ∀ j, 0 ≤ mass (w.drop j)) : mass w ≤ moment w := by
  cases w with
  | nil => simp [mass, moment]
  | cons b w =>
    have ht : ∀ j, 0 ≤ mass (w.drop j) := by
      intro j
      simpa only [List.drop_succ_cons] using h (j + 1)
    have hi := moment_nonneg_of_suffix_mass w ht
    simp only [mass_cons, moment]
    omega

/-- P2 alone gives the non-strict bound, with no minimality premise. -/
theorem p2_terminal_A_le_ss (u : List Bool) (t : Nat)
    (hp : P2 ((u ++ [false]) ++ List.replicate t true)) :
    t ≤ ssCount ((u ++ [false]) ++ List.replicate t true) := by
  apply Decidable.byContradiction
  intro hn
  have hb : 0 ≤ (t : Int) - ssCount ((u ++ [false]) ++ List.replicate t true) - 1 := by
    omega
  have h := terminal_suffix_mass_lower u t _ 0 (by omega) hb (by omega)
  have hm := mass_le_moment_of_suffix_mass _ h
  have hmass := hp.1
  have hmom := hp.2
  omega

/-- The ceiling is an output from the SS budget, not an assumption. -/
theorem prefix_ceiling_of_ss_le_terminal_A (u : List Bool) (t : Nat)
    (hm : mass ((u ++ [false]) ++ List.replicate t true) = 1)
    (ht : ssCount ((u ++ [false]) ++ List.replicate t true) ≤ t) :
    ∀ j, j ≤ ((u ++ [false]) ++ List.replicate t true).length →
      mass (((u ++ [false]) ++ List.replicate t true).take j) ≤ 2 := by
  have hb : -1 ≤ (t : Int) - ssCount ((u ++ [false]) ++ List.replicate t true) - 1 := by
    omega
  have h := terminal_suffix_mass_lower u t _ (-1) (by omega) hb (by omega)
  intro j _
  have hs := h j
  have he := mass_append
    (((u ++ [false]) ++ List.replicate t true).take j)
    (((u ++ [false]) ++ List.replicate t true).drop j)
  rw [List.take_append_drop] at he
  omega

theorem minimal_p2_terminal_A_lt_ss (u : List Bool) (t : Nat)
    (hp : P2 ((u ++ [false]) ++ List.replicate t true))
    (hmin : ∀ j, 0 < j → j < ((u ++ [false]) ++ List.replicate t true).length →
      ¬ P2 (((u ++ [false]) ++ List.replicate t true).take j))
    (ht : 0 < t) :
    t < ssCount ((u ++ [false]) ++ List.replicate t true) := by
  apply Decidable.byContradiction
  intro hn
  have hc := prefix_ceiling_of_ss_le_terminal_A u t hp.1 (by omega)
  obtain ⟨v, hv⟩ := FirstP2EndingS.minimal_p2_ends_S _ hp hmin hc
  cases t with
  | zero => omega
  | succ t =>
    have hr := congrArg List.reverse hv
    simp [List.replicate_succ', List.reverse_append] at hr

theorem minimal_p2_terminal_A_le_ss_sub_one (u : List Bool) (t : Nat)
    (hp : P2 ((u ++ [false]) ++ List.replicate t true))
    (hmin : ∀ j, 0 < j → j < ((u ++ [false]) ++ List.replicate t true).length →
      ¬ P2 (((u ++ [false]) ++ List.replicate t true).take j)) :
    t ≤ ssCount ((u ++ [false]) ++ List.replicate t true) - 1 := by
  by_cases ht : 0 < t
  · have h := minimal_p2_terminal_A_lt_ss u t hp hmin ht
    omega
  · omega

theorem minimal_p2_ss_two_terminal_A_le_one (u : List Bool) (t : Nat)
    (hp : P2 ((u ++ [false]) ++ List.replicate t true))
    (hmin : ∀ j, 0 < j → j < ((u ++ [false]) ++ List.replicate t true).length →
      ¬ P2 (((u ++ [false]) ++ List.replicate t true).take j))
    (hss : ssCount ((u ++ [false]) ++ List.replicate t true) = 2) : t ≤ 1 := by
  have h := minimal_p2_terminal_A_le_ss_sub_one u t hp hmin
  omega

/-- A statement over all minimal P2 words, including the maximality witness. -/
theorem minimal_p2_terminal_bound (w : List Bool) (hp : P2 w)
    (hmin : ∀ j, 0 < j → j < w.length → ¬ P2 (w.take j)) :
    ∃ u t, w = (u ++ [false]) ++ List.replicate t true ∧
      (w.reverse.takeWhile id).length = t ∧ t ≤ ssCount w - 1 := by
  obtain ⟨u, t, hw⟩ := p2_terminal_decomposition w hp
  subst w
  exact ⟨u, t, rfl, terminal_run_length u t,
    minimal_p2_terminal_A_le_ss_sub_one u t hp hmin⟩

end Recaman.TerminalASSBound
