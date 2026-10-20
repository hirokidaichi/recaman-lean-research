import Recaman.LeadingRunSupply

namespace Recaman.LineCapacityPeriodic

open Recaman.LeadingRunSupply

/-! # Line capacity implies periodic capacity (a reduction)

`LineCapacity e` is the open **Conjecture H**: on every finite clock interval
`[q, q+n)`, the clocks that end a P2 window lying entirely inside the interval
(at or after `q`) are no more numerous than the subtractions in the interval.
It has been verified computationally for sign strings of length at most 34,
but it is NOT proved here; it appears below only as a hypothesis.

The main theorem `periodic_capacity_of_line` shows that Conjecture H, for a
periodic sign word, implies that in one period the additions having a P2
supplier at ANY lag are at most the subtractions. This is a reduction, not a
proof of E-070.
-/

/-- Classical decidability of an arbitrary predicate on clocks. -/
@[instance_reducible]
noncomputable def classDec (P : Int → Prop) : DecidablePred P :=
  fun x => Classical.propDecidable (P x)

/-- Number of clocks `c ∈ [q, q+n)` satisfying `P`. -/
def countP (P : Int → Prop) [DecidablePred P] (q : Int) : Nat → Nat
  | 0 => 0
  | n+1 => countP P q n + (if P (q + (n : Int)) then 1 else 0)

/-- `b` ends a P2 window lying entirely at or after clock `q`. -/
def Endable (e : Int → Bool) (q b : Int) : Prop :=
  e b = true ∧ ∃ d : Nat, 0 < d ∧ q ≤ b - d ∧ P2 (past e b d)

noncomputable def endableCount (e : Int → Bool) (q : Int) (n : Nat) : Nat :=
  @countP (Endable e q) (classDec _) q n

def subtractionCount (e : Int → Bool) (q : Int) (n : Nat) : Nat :=
  countP (fun c => e c = false) q n

/-- Conjecture H (open). Used only as a hypothesis. -/
def LineCapacity (e : Int → Bool) : Prop :=
  ∀ (q : Int) (n : Nat), endableCount e q n ≤ subtractionCount e q n

/-- An addition with a P2 supplier at some (unbounded) lag. -/
def Supplied (e : Int → Bool) (x : Int) : Prop :=
  e x = true ∧ ∃ d : Nat, 0 < d ∧ P2 (past e x d)

noncomputable def suppliedPhases (e : Int → Bool) (t : Int) (p : Nat) : Nat :=
  ((List.range p).filter
    (fun (i : Nat) => @decide (Supplied e (t + (i : Int))) (Classical.propDecidable _))).length

def subtractionPhases (e : Int → Bool) (t : Int) (p : Nat) : Nat :=
  ((List.range p).filter (fun (i : Nat) => e (t + (i : Int)) = false)).length

/-! ## Generic counting lemmas -/

theorem countP_add (P : Int → Prop) [DecidablePred P] (q : Int) (n : Nat) :
    ∀ m : Nat, countP P q (n + m) = countP P q n + countP P (q + (n : Int)) m
  | 0 => rfl
  | m+1 => by
      show countP P q (n + m) + (if P (q + ((n + m : Nat) : Int)) then 1 else 0) =
        countP P q n + (countP P (q + (n : Int)) m +
          (if P (q + (n : Int) + (m : Int)) then 1 else 0))
      rw [countP_add P q n m]
      have h : q + ((n + m : Nat) : Int) = q + (n : Int) + (m : Int) := by omega
      rw [h, Nat.add_assoc]

theorem countP_le_of_range (P Q : Int → Prop) [DecidablePred P] [DecidablePred Q]
    (q : Int) : ∀ n : Nat,
    (∀ i : Nat, i < n → P (q + (i : Int)) → Q (q + (i : Int))) →
      countP P q n ≤ countP Q q n
  | 0, _ => Nat.le_refl 0
  | n+1, h => by
      have ih := countP_le_of_range P Q q n (fun i hi => h i (by omega))
      show countP P q n + (if P (q + (n : Int)) then 1 else 0) ≤
        countP Q q n + (if Q (q + (n : Int)) then 1 else 0)
      by_cases hp : P (q + (n : Int))
      · have hq := h n (by omega) hp
        rw [if_pos hp, if_pos hq]
        exact Nat.add_le_add_right ih 1
      · rw [if_neg hp]
        exact Nat.add_le_add ih (Nat.zero_le _)

theorem countP_shift (P : Int → Prop) [DecidablePred P] (s q : Int)
    (hs : ∀ x, P (x + s) ↔ P x) : ∀ n : Nat, countP P (q + s) n = countP P q n
  | 0 => rfl
  | n+1 => by
      show countP P (q + s) n + (if P (q + s + (n : Int)) then 1 else 0) =
        countP P q n + (if P (q + (n : Int)) then 1 else 0)
      rw [countP_shift P s q hs n]
      have h : P (q + s + (n : Int)) ↔ P (q + (n : Int)) := by
        have e1 : q + s + (n : Int) = (q + (n : Int)) + s := by omega
        rw [e1]; exact hs _
      by_cases hp : P (q + (n : Int))
      · rw [if_pos hp, if_pos (h.mpr hp)]
      · rw [if_neg hp, if_neg (fun hh => hp (h.mp hh))]

theorem countP_mul (P : Int → Prop) [DecidablePred P] (p : Nat) (q : Int)
    (hP : ∀ (x : Int) (k : Nat), P (x + ((k * p : Nat) : Int)) ↔ P x) :
    ∀ k : Nat, countP P q (k * p) = k * countP P q p
  | 0 => by rw [Nat.zero_mul, Nat.zero_mul]; rfl
  | k+1 => by
      rw [Nat.succ_mul, countP_add, countP_mul P p q hP k,
        countP_shift P _ q (fun x => hP x k), Nat.succ_mul]

theorem countP_eq_filter (P : Int → Prop) [DecidablePred P] (q : Int) :
    ∀ n : Nat, countP P q n =
      ((List.range n).filter (fun (i : Nat) => decide (P (q + (i : Int))))).length
  | 0 => rfl
  | n+1 => by
      rw [List.range_succ, List.filter_append, List.length_append,
        ← countP_eq_filter P q n]
      show countP P q n + (if P (q + (n : Int)) then 1 else 0) = _
      by_cases hp : P (q + (n : Int)) <;> simp [hp]

/-! ## Periodicity -/

theorem e_shift (e : Int → Bool) (p : Nat) (hp : ∀ x : Int, e (x + p) = e x) :
    ∀ (x : Int) (k : Nat), e (x + ((k * p : Nat) : Int)) = e x
  | x, 0 => by simp
  | x, k+1 => by
      have h : x + (((k+1) * p : Nat) : Int) = (x + ((k * p : Nat) : Int)) + (p : Int) := by
        rw [Nat.succ_mul]; omega
      rw [h, hp, e_shift e p hp x k]

theorem past_shift (e : Int → Bool) (p : Nat) (hp : ∀ x : Int, e (x + p) = e x)
    (x : Int) (k d : Nat) : past e (x + ((k * p : Nat) : Int)) d = past e x d := by
  unfold past
  have hf : (fun i : Nat => e (x + ((k * p : Nat) : Int) - ((i+1 : Nat) : Int))) =
      (fun i : Nat => e (x - ((i+1 : Nat) : Int))) := by
    funext i
    have h : x + ((k * p : Nat) : Int) - ((i+1 : Nat) : Int) =
        (x - ((i+1 : Nat) : Int)) + ((k * p : Nat) : Int) := by omega
    rw [h, e_shift e p hp]
  rw [hf]

theorem supplied_shift (e : Int → Bool) (p : Nat) (hp : ∀ x : Int, e (x + p) = e x)
    (x : Int) (k : Nat) : Supplied e (x + ((k * p : Nat) : Int)) ↔ Supplied e x := by
  unfold Supplied
  rw [e_shift e p hp x k]
  constructor
  · rintro ⟨h1, d, hd, h2⟩
    exact ⟨h1, d, hd, by rw [past_shift e p hp] at h2; exact h2⟩
  · rintro ⟨h1, d, hd, h2⟩
    exact ⟨h1, d, hd, by rw [past_shift e p hp]; exact h2⟩

/-- A uniform lag bound for the supplied phases among the first `n`. -/
theorem lag_bound (e : Int → Bool) (t : Int) : ∀ n : Nat, ∃ Dm : Nat,
    ∀ i : Nat, i < n → Supplied e (t + (i : Int)) →
      ∃ d : Nat, 0 < d ∧ d ≤ Dm ∧ P2 (past e (t + (i : Int)) d)
  | 0 => ⟨0, fun i hi _ => absurd hi (Nat.not_lt_zero _)⟩
  | n+1 => by
      obtain ⟨Dm, hDm⟩ := lag_bound e t n
      by_cases hs : Supplied e (t + (n : Int))
      · obtain ⟨_, d, hd, hP⟩ := hs
        refine ⟨max Dm d, fun i hi hsi => ?_⟩
        by_cases hin : i < n
        · obtain ⟨d', h1, h2, h3⟩ := hDm i hin hsi
          exact ⟨d', h1, Nat.le_trans h2 (Nat.le_max_left _ _), h3⟩
        · have hi' : i = n := by omega
          rw [hi']
          exact ⟨d, hd, Nat.le_max_right _ _, hP⟩
      · refine ⟨Dm, fun i hi hsi => ?_⟩
        by_cases hin : i < n
        · exact hDm i hin hsi
        · have hi' : i = n := by omega
          rw [hi'] at hsi
          exact absurd hsi hs

/-! ## Main reduction -/

/-- Conjecture H (hypothesis `hH`) implies, for every periodic sign word, that
the additions of one period with a P2 supplier at any lag are at most the
subtractions of that period. -/
theorem periodic_capacity_of_line (e : Int → Bool) (p : Nat) (hp0 : 0 < p)
    (hp : ∀ x : Int, e (x + p) = e x) (t : Int) (hH : LineCapacity e) :
    suppliedPhases e t p ≤ subtractionPhases e t p := by
  -- per-period counts as countP
  have hU : suppliedPhases e t p = @countP (Supplied e) (classDec _) t p :=
    (@countP_eq_filter (Supplied e) (classDec _) t p).symm
  have hD : subtractionPhases e t p = countP (fun c => e c = false) t p :=
    (countP_eq_filter (fun c => e c = false) t p).symm
  obtain ⟨Dm, hDm⟩ := lag_bound e t p
  -- each block at index j ≥ Dm contains at least U endable clocks
  have hblock : ∀ j : Nat, Dm ≤ j →
      suppliedPhases e t p ≤
        @countP (Endable e t) (classDec _) (t + ((j * p : Nat) : Int)) p := by
    intro j hj
    rw [hU, ← @countP_shift (Supplied e) (classDec _) ((j * p : Nat) : Int) t
      (fun x => supplied_shift e p hp x j) p]
    apply @countP_le_of_range _ _ (classDec _) (classDec _)
    intro i hi hs
    have hs' : Supplied e (t + (i : Int)) := by
      have h : t + ((j * p : Nat) : Int) + (i : Int) = t + (i : Int) + ((j * p : Nat) : Int) := by
        omega
      rw [h, supplied_shift e p hp] at hs
      exact hs
    obtain ⟨d, hd0, hdD, hP⟩ := hDm i hi hs'
    have hjp : j ≤ j * p := by
      have := Nat.mul_le_mul (Nat.le_refl j) hp0
      rw [Nat.mul_one] at this
      exact this
    refine ⟨hs.1, d, hd0, ?_, ?_⟩
    · generalize j * p = m at hjp
      omega
    · have h : t + ((j * p : Nat) : Int) + (i : Int) = t + (i : Int) + ((j * p : Nat) : Int) := by
        omega
      rw [h, past_shift e p hp]
      exact hP
  -- N blocks starting at block Dm give at least N * U endable clocks
  have hlow : ∀ N : Nat, N * suppliedPhases e t p ≤
      @countP (Endable e t) (classDec _) (t + ((Dm * p : Nat) : Int)) (N * p) := by
    intro N
    induction N with
    | zero => rw [Nat.zero_mul]; exact Nat.zero_le _
    | succ N ih =>
      rw [Nat.succ_mul, Nat.succ_mul, countP_add]
      have h : t + ((Dm * p : Nat) : Int) + ((N * p : Nat) : Int) =
          t + (((Dm + N) * p : Nat) : Int) := by
        rw [Nat.add_mul]; omega
      rw [h]
      exact Nat.add_le_add ih (hblock (Dm + N) (Nat.le_add_right _ _))
  -- the capacity inequality for each N
  have hineq : ∀ N : Nat, N * suppliedPhases e t p ≤ (Dm + N) * subtractionPhases e t p := by
    intro N
    have h1 := hH t ((Dm + N) * p)
    have h2 : endableCount e t ((Dm + N) * p) =
        endableCount e t (Dm * p) +
          @countP (Endable e t) (classDec _) (t + ((Dm * p : Nat) : Int)) (N * p) := by
      unfold endableCount
      rw [Nat.add_mul, countP_add]
    have h3 : subtractionCount e t ((Dm + N) * p) = (Dm + N) * subtractionPhases e t p := by
      unfold subtractionCount
      rw [hD, countP_mul (fun c => e c = false) p t
        (fun x k => by rw [e_shift e p hp x k])]
    have := hlow N
    omega
  -- conclude
  apply Classical.byContradiction
  intro hlt
  have hlt' : subtractionPhases e t p + 1 ≤ suppliedPhases e t p := by omega
  obtain ⟨N, hN⟩ : ∃ N, N = Dm * subtractionPhases e t p + 1 := ⟨_, rfl⟩
  have h1 := hineq N
  have h2 : N * (subtractionPhases e t p + 1) ≤ N * suppliedPhases e t p :=
    Nat.mul_le_mul (Nat.le_refl N) hlt'
  rw [Nat.mul_succ] at h2
  rw [Nat.add_mul] at h1
  generalize Dm * subtractionPhases e t p = A at hN h1
  generalize N * subtractionPhases e t p = B at h1 h2
  generalize N * suppliedPhases e t p = C at h1 h2
  omega

end Recaman.LineCapacityPeriodic
