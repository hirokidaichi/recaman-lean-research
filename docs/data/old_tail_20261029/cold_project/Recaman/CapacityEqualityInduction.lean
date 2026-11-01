import Recaman.LineCapacityPeriodic
import Recaman.LeadingRunSupply

namespace Recaman.CapacityEqualityInduction

open Recaman.LeadingRunSupply
open Recaman.LineCapacityPeriodic
open Recaman.ShortPeriodicSupply (sign)

/-! # Capacity by induction from the equality class

`hcap_step`: if line capacity holds on every proper prefix `[p, p+m)` of
`[p, p+n)`, and every equality-case prefix ending at an endable clock is a
block word, then line capacity holds on `[p, p+n)`.
-/

/-- Signs on the clocks `[p, p+n)`, oldest first. -/
def segment (e : Int → Bool) (p : Int) (n : Nat) : List Bool :=
  (List.range n).map fun (i : Nat) => e (p + (i : Int))

inductive BlockWord : List Bool → Prop
  | nil : BlockWord []
  | free {w} : BlockWord w → BlockWord (w ++ [true])
  | aas {w} : BlockWord w → BlockWord (w ++ [false, true, true, true])
  | triple {w} : BlockWord w →
      BlockWord (w ++ [false, false, true, true, true, true, false, true, true, true])

def HCap (e : Int → Bool) (p : Int) (n : Nat) : Prop :=
  endableCount e p n ≤ subtractionCount e p n

def EqClassW (e : Int → Bool) (p : Int) (n : Nat) : Prop :=
  0 < n → endableCount e p n = subtractionCount e p n → Endable e p (p + n - 1) →
    BlockWord (segment e p n)

/-! ## Counting subtractions in a word -/

def cntF : List Bool → Nat
  | [] => 0
  | b :: w => (if b then 0 else 1) + cntF w

theorem cntF_append (u v : List Bool) : cntF (u ++ v) = cntF u + cntF v := by
  induction u with
  | nil => simp [cntF]
  | cons b u ih => simp [cntF, ih, Nat.add_assoc]

theorem cntF_reverse (u : List Bool) : cntF u.reverse = cntF u := by
  induction u with
  | nil => rfl
  | cons b u ih => rw [List.reverse_cons, cntF_append, ih]; cases b <;> simp [cntF] <;> omega

theorem mass_cntF (u : List Bool) : mass u = (u.length : Int) - 2 * (cntF u : Int) := by
  induction u with
  | nil => simp [cntF]
  | cons b u ih => cases b <;> simp [cntF, sign, ih] <;> omega

/-! ## Density of block words -/

/-- Every suffix has at most 3/10 of its letters equal to `false`. -/
def Dense (l : List Bool) : Prop :=
  ∀ u v : List Bool, u ++ v = l → 10 * cntF v ≤ 3 * v.length

theorem dense_nil : Dense [] := by
  intro u v h
  have : v = [] := (List.append_eq_nil_iff.mp h).2
  subst this; simp [cntF]

theorem dense_append (w B : List Bool) (hw : Dense w) (hB : Dense B) : Dense (w ++ B) := by
  intro u v h
  rcases List.append_eq_append_iff.mp h with ⟨a', h1, h2⟩ | ⟨c', h1, h2⟩
  · subst h2
    have ha := hw u a' h1.symm
    have hb := hB [] B rfl
    rw [cntF_append, List.length_append]; omega
  · exact hB c' v h2.symm

theorem dense_of_drops (B : List Bool)
    (h : ∀ k, k < B.length + 1 → 10 * cntF (B.drop k) ≤ 3 * (B.drop k).length) : Dense B := by
  intro u v huv
  have hv : v = B.drop u.length := by rw [← huv, List.drop_left]
  have hk : u.length < B.length + 1 := by rw [← huv, List.length_append]; omega
  rw [hv]; exact h _ hk

theorem dense_free : Dense [true] := dense_of_drops _ (by decide)
theorem dense_aas : Dense [false, true, true, true] := dense_of_drops _ (by decide)
theorem dense_triple :
    Dense [false, false, true, true, true, true, false, true, true, true] :=
  dense_of_drops _ (by decide)

theorem dense_of_block {w : List Bool} (h : BlockWord w) : Dense w := by
  induction h with
  | nil => exact dense_nil
  | free _ ih => exact dense_append _ _ ih dense_free
  | aas _ ih => exact dense_append _ _ ih dense_aas
  | triple _ ih => exact dense_append _ _ ih dense_triple

theorem dense_pad {w : List Bool} (h : BlockWord w) :
    ∀ j : Nat, Dense (w ++ List.replicate j true)
  | 0 => by rw [List.replicate_zero, List.append_nil]; exact dense_of_block h
  | j+1 => by
      rw [List.replicate_succ', ← List.append_assoc]
      exact dense_append _ _ (dense_pad h j) dense_free

/-! ## Segments and windows -/

theorem segment_succ (e : Int → Bool) (p : Int) (n : Nat) :
    segment e p (n+1) = segment e p n ++ [e (p + n)] := by
  simp [segment, List.range_succ]

theorem segment_add (e : Int → Bool) (p : Int) (n : Nat) :
    ∀ k : Nat, segment e p (n + k) = segment e p n ++ segment e (p + n) k
  | 0 => by simp [segment]
  | k+1 => by
      rw [← Nat.add_assoc, segment_succ, segment_add e p n k, segment_succ, List.append_assoc]
      have h : p + ((n + k : Nat) : Int) = p + (n : Int) + (k : Int) := by omega
      rw [h]

theorem segment_one (e : Int → Bool) (q : Int) : segment e q 1 = [e q] := by
  simp [segment]

theorem past_succ (e : Int → Bool) (t : Int) (d : Nat) :
    past e t (d+1) = past e t d ++ [e (t - ((d+1 : Nat) : Int))] := by
  simp [past, List.range_succ]

theorem past_reverse (e : Int → Bool) (t : Int) :
    ∀ d : Nat, (past e t d).reverse = segment e (t - d) d
  | 0 => rfl
  | d+1 => by
      rw [past_succ, List.reverse_append, past_reverse e t d, Nat.add_comm d 1, segment_add,
        segment_one]
      have h1 : t - ((1 + d : Nat) : Int) = t - ((d + 1 : Nat) : Int) := by omega
      have h2 : t - ((1 + d : Nat) : Int) + ((1 : Nat) : Int) = t - (d : Int) := by omega
      rw [h2, h1]
      rfl

theorem segment_true (e : Int → Bool) (q : Int) :
    ∀ n : Nat, (∀ i : Nat, i < n → e (q + i) = true) → segment e q n = List.replicate n true
  | 0, _ => rfl
  | n+1, h => by
      rw [segment_succ, segment_true e q n (fun i hi => h i (by omega)), h n (by omega),
        List.replicate_succ']

/-! ## Counting lemmas -/

theorem countP_eq_zero_of (P : Int → Prop) [DecidablePred P] (q : Int) :
    ∀ n : Nat, (∀ i : Nat, i < n → ¬ P (q + i)) → countP P q n = 0
  | 0, _ => rfl
  | n+1, h => by
      show countP P q n + (if P (q + (n : Int)) then 1 else 0) = 0
      rw [countP_eq_zero_of P q n (fun i hi => h i (by omega)), if_neg (h n (by omega))]

theorem not_of_countP_eq_zero (P : Int → Prop) [DecidablePred P] (q : Int) :
    ∀ n : Nat, countP P q n = 0 → ∀ i : Nat, i < n → ¬ P (q + i)
  | 0, _, i, hi => absurd hi (Nat.not_lt_zero _)
  | n+1, h, i, hi => by
      have h' : countP P q n + (if P (q + (n : Int)) then 1 else 0) = 0 := h
      by_cases hp : P (q + (n : Int))
      · rw [if_pos hp] at h'; omega
      · rw [if_neg hp] at h'
        by_cases hin : i < n
        · exact not_of_countP_eq_zero P q n (by omega) i hin
        · have : i = n := by omega
          subst this; exact hp

theorem countP_succ_le (P : Int → Prop) [DecidablePred P] (q : Int) (n : Nat) :
    countP P q (n+1) ≤ countP P q n + 1 := by
  show countP P q n + (if P (q + (n : Int)) then 1 else 0) ≤ countP P q n + 1
  by_cases hp : P (q + (n : Int))
  · rw [if_pos hp]; exact Nat.le_refl _
  · rw [if_neg hp]; omega

theorem countP_le_succ (P : Int → Prop) [DecidablePred P] (q : Int) (n : Nat) :
    countP P q n ≤ countP P q (n+1) := by
  show countP P q n ≤ countP P q n + (if P (q + (n : Int)) then 1 else 0)
  exact Nat.le_add_right _ _

/-- The last marked clock before `p + m` (or `p` itself if there is none). -/
theorem last_mark (P : Int → Prop) (p : Int) : ∀ m : Nat, ∃ m' : Nat, m' ≤ m ∧
    (m' = 0 ∨ P (p + m' - 1)) ∧ ∀ i : Nat, m' ≤ i → i < m → ¬ P (p + i)
  | 0 => ⟨0, Nat.le_refl 0, Or.inl rfl, fun i h1 h2 => absurd h2 (by omega)⟩
  | m+1 => by
      by_cases hp : P (p + m)
      · refine ⟨m+1, Nat.le_refl _, Or.inr ?_, fun i h1 h2 => absurd h2 (by omega)⟩
        have : p + ((m+1 : Nat) : Int) - 1 = p + m := by omega
        rw [this]; exact hp
      · obtain ⟨m', h1, h2, h3⟩ := last_mark P p m
        refine ⟨m', by omega, h2, fun i hi1 hi2 => ?_⟩
        by_cases hi : i < m
        · exact h3 i hi1 hi
        · have : i = m := by omega
          subst this; exact hp

/-! ## No P2 window ends right after a padded block word -/

theorem no_p2_suffix (e : Int → Bool) (p : Int) (m : Nat) (hD : Dense (segment e p m))
    (d : Nat) (hd : 0 < d) (hdm : d ≤ m) (hP : P2 (past e (p + m) d)) : False := by
  have hsplit := segment_add e p (m - d) d
  rw [Nat.sub_add_cancel hdm] at hsplit
  have hq : p + ((m - d : Nat) : Int) = p + (m : Int) - d := by omega
  rw [hq] at hsplit
  have hden := hD _ _ hsplit.symm
  rw [← past_reverse, cntF_reverse, List.length_reverse] at hden
  obtain ⟨hmass, hmom⟩ := hP
  rw [mass_cntF] at hmass
  have hlen : (past e (p + m) d).length = d := by simp [past]
  rw [hlen] at hmass hden
  have hd1 : d = 1 := by omega
  subst hd1
  have hm1 : moment (past e (p + m) 1) = sign (e (p + (m : Int) - ((0 + 1 : Nat) : Int))) := by
    simp [past, moment]
  rw [hm1] at hmom
  cases h : e (p + (m : Int) - ((0 + 1 : Nat) : Int)) <;> rw [h] at hmom <;> simp [sign] at hmom

/-! ## The induction step -/

theorem hcap_step (e : Int → Bool) (p : Int) (n : Nat)
    (hH : ∀ m, m < n → HCap e p m) (hE : ∀ m, m < n → EqClassW e p m) : HCap e p n := by
  cases n with
  | zero => exact Nat.le_refl 0
  | succ m =>
  apply Classical.byContradiction
  intro hneg
  have hneg' : subtractionCount e p (m+1) < endableCount e p (m+1) := Nat.lt_of_not_le hneg
  have hm : endableCount e p m ≤ subtractionCount e p m := hH m (Nat.lt_succ_self m)
  have hEs : endableCount e p (m+1) ≤ endableCount e p m + 1 :=
    @countP_succ_le (Endable e p) (classDec _) p m
  have hSs : subtractionCount e p m ≤ subtractionCount e p (m+1) :=
    countP_le_succ _ p m
  have hc : Endable e p (p + m) := by
    apply Classical.byContradiction
    intro hc
    have h1 : endableCount e p (m+1) = endableCount e p m := by
      show @countP (Endable e p) (classDec _) p m +
        @ite _ (Endable e p (p + ((m : Nat) : Int))) (classDec _ _) 1 0 = _
      rw [if_neg hc]; rfl
    omega
  obtain ⟨m', hm'le, hm'mark, hm'none⟩ := last_mark (Endable e p) p m
  have hEq : endableCount e p m = endableCount e p m' := by
    have h := @countP_add (Endable e p) (classDec _) p m' (m - m')
    rw [Nat.add_sub_cancel' hm'le] at h
    have h0 : @countP (Endable e p) (classDec _) (p + m') (m - m') = 0 := by
      apply @countP_eq_zero_of (Endable e p) (classDec _)
      intro i hi
      have := hm'none (m' + i) (by omega) (by omega)
      rwa [show p + ((m' + i : Nat) : Int) = p + (m' : Int) + (i : Int) by omega] at this
    show @countP (Endable e p) (classDec _) p m = @countP (Endable e p) (classDec _) p m'
    rw [h, h0, Nat.add_zero]
  have hSadd : subtractionCount e p m =
      subtractionCount e p m' + subtractionCount e (p + m') (m - m') := by
    have h := countP_add (fun c => e c = false) p m' (m - m')
    rw [Nat.add_sub_cancel' hm'le] at h
    exact h
  have hHm' : endableCount e p m' ≤ subtractionCount e p m' := hH m' (by omega)
  have htail0 : subtractionCount e (p + m') (m - m') = 0 := by omega
  have hall := not_of_countP_eq_zero _ (p + m') (m - m') htail0
  have hseg : segment e p m = segment e p m' ++ List.replicate (m - m') true := by
    rw [← segment_true e (p + m') (m - m') (fun i hi => by
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
      · exact hE m' (by omega) (by omega) (by omega) hmk
  have hD := dense_pad hBW (m - m')
  rw [← hseg] at hD
  obtain ⟨_, d, hd, hpd, hP2⟩ := hc
  exact no_p2_suffix e p m hD d hd (by omega) hP2

theorem hcap_of_eqclassW (e : Int → Bool) (p : Int) (hE : ∀ m, EqClassW e p m) :
    ∀ n, HCap e p n := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih => exact hcap_step e p n ih (fun m _ => hE m)

end Recaman.CapacityEqualityInduction
