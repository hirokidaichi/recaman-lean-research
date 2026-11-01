import Recaman.CapacityEqualityInduction

namespace Recaman.SingleWindowEquality

open Recaman.LeadingRunSupply
open Recaman.LineCapacityPeriodic
open Recaman.CapacityEqualityInduction
open Recaman.ShortPeriodicSupply (sign)

/-! # A single tight window is the block `S A A A`

Pure walk setting: `f : Nat → Bool` is the sign string (clock `i` of the
interval), `Fw f` the level walk and `Ar f t k` the area of the window of
length `k` starting at `t`.
-/

/-! ## Walk, area, windows -/

def Fw (f : Nat → Bool) : Nat → Int
  | 0 => 0
  | k+1 => Fw f k + sign (f k)

def Ar (f : Nat → Bool) (t : Nat) : Nat → Int
  | 0 => 0
  | k+1 => Ar f t k + (Fw f (t+k+1) - Fw f t)

def Win (f : Nat → Bool) (t k : Nat) : Prop :=
  0 < k ∧ Fw f (t+k) = Fw f t + 1 ∧ Ar f t k = 0

def EndN (f : Nat → Bool) (s b : Nat) : Prop :=
  f b = true ∧ ∃ t k, s ≤ t ∧ t + k = b ∧ Win f t k

def seg (f : Nat → Bool) (s m : Nat) : List Bool :=
  (List.range m).map fun i => f (s + i)

open Classical in
noncomputable def cN (P : Nat → Prop) (s : Nat) : Nat → Nat
  | 0 => 0
  | m+1 => cN P s m + (if P (s+m) then 1 else 0)

theorem Fw_succ (f : Nat → Bool) (k : Nat) : Fw f (k+1) = Fw f k + sign (f k) := rfl

theorem fw_cases (f : Nat → Bool) (k : Nat) :
    (Fw f (k+1) = Fw f k + 1 ∧ f k = true) ∨ (Fw f (k+1) = Fw f k - 1 ∧ f k = false) := by
  rw [Fw_succ]
  cases h : f k
  · right; exact ⟨by simp [sign]; omega, rfl⟩
  · left; exact ⟨by simp [sign], rfl⟩

theorem Fw_bound (f : Nat → Bool) : ∀ k : Nat, -(k : Int) ≤ Fw f k ∧ Fw f k ≤ k
  | 0 => by simp [Fw]
  | k+1 => by
      have := Fw_bound f k
      rcases fw_cases f k with ⟨h, _⟩ | ⟨h, _⟩ <;> omega

theorem Ar_succ (f : Nat → Bool) (t k : Nat) :
    Ar f t (k+1) = Ar f t k + (Fw f (t+k+1) - Fw f t) := rfl

theorem Ar2 (f : Nat → Bool) (t : Nat) :
    Ar f t 2 = (Fw f (t+1) - Fw f t) + (Fw f (t+2) - Fw f t) := by
  show Ar f t 0 + (Fw f (t+0+1) - Fw f t) + (Fw f (t+1+1) - Fw f t) = _
  simp [Ar]

theorem Ar3 (f : Nat → Bool) (t : Nat) :
    Ar f t 3 = (Fw f (t+1) - Fw f t) + (Fw f (t+2) - Fw f t) + (Fw f (t+3) - Fw f t) := by
  show Ar f t 2 + (Fw f (t+2+1) - Fw f t) = _
  rw [Ar2]

theorem Ar4 (f : Nat → Bool) (t : Nat) :
    Ar f t 4 = (Fw f (t+1) - Fw f t) + (Fw f (t+2) - Fw f t) + (Fw f (t+3) - Fw f t)
      + (Fw f (t+4) - Fw f t) := by
  show Ar f t 3 + (Fw f (t+3+1) - Fw f t) = _
  rw [Ar3]

/-! ## Bridge to `past` -/

theorem past_cons (e : Int → Bool) (c : Int) (k : Nat) :
    past e c (k+1) = e (c - 1) :: past e (c - 1) k := by
  rw [Nat.add_comm k 1, past_append]
  have h1 : past e c 1 = [e (c - 1)] := by
    simp only [past, List.range_one, List.map_cons, List.map_nil]
    rfl
  rw [h1]
  rfl

theorem past_bridge (e : Int → Bool) (p : Int) (t : Nat) :
    ∀ k : Nat, mass (past e (p + ((t + k : Nat) : Int)) k) =
        Fw (fun i => e (p + (i : Int))) (t + k) - Fw (fun i => e (p + (i : Int))) t ∧
      moment (past e (p + ((t + k : Nat) : Int)) k) = Ar (fun i => e (p + (i : Int))) t k
  | 0 => by simp [past, moment, Ar]
  | k+1 => by
      obtain ⟨h1, h2⟩ := past_bridge e p t k
      have hc : p + ((t + (k+1) : Nat) : Int) - 1 = p + ((t + k : Nat) : Int) := by omega
      rw [past_cons, hc]
      have hF : Fw (fun i => e (p + (i : Int))) (t + (k+1)) =
          Fw (fun i => e (p + (i : Int))) (t + k) + sign (e (p + ((t + k : Nat) : Int))) := rfl
      constructor
      · rw [mass_cons, h1, hF]; omega
      · show sign _ + mass _ + moment _ = _
        rw [h1, h2, Ar_succ]
        have : t + k + 1 = t + (k+1) := rfl
        rw [this, hF]; omega

/-! ## Counting on `Nat` intervals -/

section counting
variable (P Q : Nat → Prop) (s : Nat)

theorem cN_succ_pos (m : Nat) (h : P (s+m)) : cN P s (m+1) = cN P s m + 1 := by
  show cN P s m + @ite _ _ (Classical.propDecidable _) 1 0 = _
  rw [if_pos h]

theorem cN_succ_neg (m : Nat) (h : ¬ P (s+m)) : cN P s (m+1) = cN P s m := by
  show cN P s m + @ite _ _ (Classical.propDecidable _) 1 0 = _
  rw [if_neg h]; rfl

theorem cN_succ_le (m : Nat) : cN P s (m+1) ≤ cN P s m + 1 := by
  by_cases h : P (s+m)
  · rw [cN_succ_pos P s m h]; exact Nat.le_refl _
  · rw [cN_succ_neg P s m h]; omega

theorem cN_add (a : Nat) : ∀ b : Nat, cN P s (a + b) = cN P s a + cN P (s + a) b
  | 0 => rfl
  | b+1 => by
      have ih := cN_add a b
      have e1 : s + (a + b) = s + a + b := by omega
      by_cases h : P (s + (a + b))
      · rw [show a + (b+1) = a + b + 1 from rfl, cN_succ_pos P s _ h, ih,
          cN_succ_pos P (s+a) b (by rw [← e1]; exact h)]; omega
      · rw [show a + (b+1) = a + b + 1 from rfl, cN_succ_neg P s _ h, ih,
          cN_succ_neg P (s+a) b (by rw [← e1]; exact h)]

theorem cN_congr : ∀ m : Nat, (∀ i, s ≤ i → i < s + m → (P i ↔ Q i)) → cN P s m = cN Q s m
  | 0, _ => rfl
  | m+1, h => by
      have ih := cN_congr m (fun i h1 h2 => h i h1 (by omega))
      by_cases hp : P (s+m)
      · rw [cN_succ_pos P s m hp, cN_succ_pos Q s m ((h (s+m) (by omega) (by omega)).mp hp), ih]
      · rw [cN_succ_neg P s m hp,
          cN_succ_neg Q s m (fun hq => hp ((h (s+m) (by omega) (by omega)).mpr hq)), ih]

theorem cN_mono : ∀ m : Nat, (∀ i, s ≤ i → i < s + m → P i → Q i) → cN P s m ≤ cN Q s m
  | 0, _ => Nat.le_refl 0
  | m+1, h => by
      have ih := cN_mono m (fun i h1 h2 => h i h1 (by omega))
      by_cases hp : P (s+m)
      · rw [cN_succ_pos P s m hp, cN_succ_pos Q s m (h (s+m) (by omega) (by omega) hp)]; omega
      · rw [cN_succ_neg P s m hp]
        exact Nat.le_trans ih (by
          by_cases hq : Q (s+m)
          · rw [cN_succ_pos Q s m hq]; omega
          · rw [cN_succ_neg Q s m hq]; exact Nat.le_refl _)

theorem cN_zero_of : ∀ m : Nat, (∀ i, s ≤ i → i < s + m → ¬ P i) → cN P s m = 0
  | 0, _ => rfl
  | m+1, h => by
      rw [cN_succ_neg P s m (h (s+m) (by omega) (by omega))]
      exact cN_zero_of m (fun i h1 h2 => h i h1 (by omega))

theorem not_of_cN_zero : ∀ m : Nat, cN P s m = 0 → ∀ i, s ≤ i → i < s + m → ¬ P i
  | 0, _, i, h1, h2 => absurd h2 (by omega)
  | m+1, h, i, h1, h2 => by
      by_cases hp : P (s+m)
      · rw [cN_succ_pos P s m hp] at h; omega
      · rw [cN_succ_neg P s m hp] at h
        by_cases hi : i < s + m
        · exact not_of_cN_zero m h i h1 hi
        · have : i = s + m := by omega
          rw [this]; exact hp

theorem cN_split : ∀ m : Nat,
    cN P s m = cN (fun i => P i ∧ Q i) s m + cN (fun i => P i ∧ ¬ Q i) s m
  | 0 => rfl
  | m+1 => by
      have ih := cN_split m
      by_cases hp : P (s+m)
      · by_cases hq : Q (s+m)
        · rw [cN_succ_pos P s m hp, cN_succ_pos (fun i => P i ∧ Q i) s m ⟨hp, hq⟩,
            cN_succ_neg (fun i => P i ∧ ¬ Q i) s m (fun h => h.2 hq)]; omega
        · rw [cN_succ_pos P s m hp, cN_succ_neg (fun i => P i ∧ Q i) s m (fun h => hq h.2),
            cN_succ_pos (fun i => P i ∧ ¬ Q i) s m ⟨hp, hq⟩]; omega
      · rw [cN_succ_neg P s m hp, cN_succ_neg (fun i => P i ∧ Q i) s m (fun h => hp h.1),
          cN_succ_neg (fun i => P i ∧ ¬ Q i) s m (fun h => hp h.1)]; omega

end counting

theorem cN_walk (f : Nat → Bool) (s : Nat) : ∀ m : Nat,
    Fw f (s+m) = Fw f s + (cN (fun i => f i = true) s m : Int)
      - (cN (fun i => f i = false) s m : Int) ∧
    cN (fun i => f i = true) s m + cN (fun i => f i = false) s m = m
  | 0 => by simp [cN]
  | m+1 => by
      obtain ⟨h1, h2⟩ := cN_walk f s m
      have hs : s + (m+1) = s + m + 1 := rfl
      rcases fw_cases f (s+m) with ⟨hF, hb⟩ | ⟨hF, hb⟩
      · rw [cN_succ_pos (fun i => f i = true) s m hb,
          cN_succ_neg (fun i => f i = false) s m (by simp [hb]), hs, hF]
        constructor
        · push_cast; omega
        · omega
      · rw [cN_succ_neg (fun i => f i = true) s m (by simp [hb]),
          cN_succ_pos (fun i => f i = false) s m hb, hs, hF]
        constructor
        · push_cast; omega
        · omega

/-! ## First and last marks -/

theorem first_mark (P : Nat → Prop) : ∀ k : Nat, (∃ i, i ≤ k ∧ P i) →
    ∃ b, b ≤ k ∧ P b ∧ ∀ i, i < b → ¬ P i
  | 0, ⟨i, hi, hp⟩ => by
      have : i = 0 := by omega
      subst this
      exact ⟨0, Nat.le_refl 0, hp, fun i h => absurd h (by omega)⟩
  | k+1, ⟨i, hi, hp⟩ => by
      by_cases hex : ∃ i, i ≤ k ∧ P i
      · obtain ⟨b, hb, hpb, hmin⟩ := first_mark P k hex
        exact ⟨b, by omega, hpb, hmin⟩
      · have hik : i = k+1 := by
          apply Classical.byContradiction
          intro hne
          exact hex ⟨i, by omega, hp⟩
        subst hik
        exact ⟨k+1, Nat.le_refl _, hp, fun i h hpi => hex ⟨i, by omega, hpi⟩⟩

theorem last_markN (P : Nat → Prop) (s : Nat) : ∀ m : Nat, ∃ m', m' ≤ m ∧
    (m' = 0 ∨ P (s + m' - 1)) ∧ ∀ i, m' ≤ i → i < m → ¬ P (s + i)
  | 0 => ⟨0, Nat.le_refl 0, Or.inl rfl, fun i h1 h2 => absurd h2 (by omega)⟩
  | m+1 => by
      by_cases hp : P (s + m)
      · refine ⟨m+1, Nat.le_refl _, Or.inr ?_, fun i h1 h2 => absurd h2 (by omega)⟩
        rw [show s + (m+1) - 1 = s + m by omega]; exact hp
      · obtain ⟨m', h1, h2, h3⟩ := last_markN P s m
        refine ⟨m', by omega, h2, fun i hi1 hi2 => ?_⟩
        by_cases hi : i < m
        · exact h3 i hi1 hi
        · have : i = m := by omega
          subst this; exact hp

/-! ## Walk lemmas -/

section walk
variable (f : Nat → Bool)

theorem first_hit : ∀ k : Nat, (∀ u, u ≤ k → Fw f u ≤ 0) ∨
    (∃ q, q ≤ k ∧ Fw f q = 1 ∧ ∀ u, u < q → Fw f u ≤ 0)
  | 0 => Or.inl (fun u hu => by
      have : u = 0 := by omega
      subst this; simp [Fw])
  | k+1 => by
      rcases first_hit k with h | ⟨q, hq, h1, h2⟩
      · have hk := h k (Nat.le_refl k)
        have hs := fw_cases f k
        by_cases h1 : Fw f (k+1) = 1
        · exact Or.inr ⟨k+1, Nat.le_refl _, h1, fun u hu => h u (by omega)⟩
        · left
          intro u hu
          by_cases hu' : u ≤ k
          · exact h u hu'
          · have : u = k+1 := by omega
            subst this; omega
      · exact Or.inr ⟨q, by omega, h1, h2⟩

/-- Discrete intermediate value: an up-crossing from level `c-1` to `c`. -/
theorem ivt (n : Nat) (c : Int) (hn : c ≤ Fw f n) : ∀ k u : Nat, u + k = n →
    Fw f u ≤ c - 1 → ∃ u', u ≤ u' ∧ u' < n ∧ Fw f u' = c - 1 ∧ f u' = true
  | 0, u, h, hu => by
      have : u = n := by omega
      subst this; omega
  | k+1, u, h, hu => by
      rcases fw_cases f u with ⟨hF, hb⟩ | ⟨hF, hb⟩
      · by_cases hc : Fw f u = c - 1
        · exact ⟨u, Nat.le_refl u, by omega, hc, hb⟩
        · obtain ⟨u', h1, h2, h3, h4⟩ := ivt n c hn k (u+1) (by omega) (by omega)
          exact ⟨u', by omega, h2, h3, h4⟩
      · obtain ⟨u', h1, h2, h3, h4⟩ := ivt n c hn k (u+1) (by omega) (by omega)
        exact ⟨u', by omega, h2, h3, h4⟩

theorem floor_lemma (a n : Nat) (c : Int) (hn : c ≤ Fw f n)
    (hno : ∀ u, a ≤ u → u < n → Fw f u = c - 1 → f u = true → False) :
    ∀ u, a ≤ u → u ≤ n → c ≤ Fw f u := by
  intro u h1 h2
  apply Classical.byContradiction
  intro hlt
  obtain ⟨u', h3, h4, h5, h6⟩ := ivt f n c hn (n - u) u (by omega) (by omega)
  exact hno u' (by omega) h4 h5 h6

theorem floor_induct (a n : Nat) (c0 : Int) (hn : c0 ≤ Fw f n)
    (hstep : ∀ c, c < c0 → (∀ u, a ≤ u → u ≤ n → c ≤ Fw f u) →
      ∀ u, a ≤ u → u < n → Fw f u = c → f u = true → False) :
    ∀ u, a ≤ u → u ≤ n → c0 ≤ Fw f u := by
  have key : ∀ k : Nat, -(n : Int) + k ≤ c0 → ∀ u, a ≤ u → u ≤ n → -(n : Int) + k ≤ Fw f u := by
    intro k
    induction k with
    | zero =>
      intro _ u _ hu
      have := (Fw_bound f u).1
      omega
    | succ k ih =>
      intro hk
      have ih' := ih (by omega)
      have := floor_lemma f a n (-(n : Int) + k + 1) (by omega)
        (fun u h1 h2 h3 h4 => hstep (-(n : Int) + k) (by omega) ih' u h1 h2 (by omega) h4)
      intro u h1 h2
      have := this u h1 h2
      push_cast; omega
  by_cases hc : 0 ≤ c0 + n
  · obtain ⟨k, hk⟩ : ∃ k : Nat, (k : Int) = c0 + n := ⟨(c0 + n).toNat, Int.toNat_of_nonneg hc⟩
    intro u h1 h2
    have := key k (by omega) u h1 h2
    omega
  · intro u h1 h2
    have := (Fw_bound f u).1
    omega

/-- The dip lemma: a positive-mass window with zero area dips below its base. -/
theorem area_ge (t : Nat) : ∀ k : Nat, (∀ i, 1 ≤ i → i ≤ k → Fw f t ≤ Fw f (t+i)) →
    Fw f (t+k) - Fw f t ≤ Ar f t k
  | 0, _ => by simp [Ar]
  | k+1, h => by
      have ih := area_ge t k (fun i h1 h2 => h i h1 (by omega))
      have hk : Fw f t ≤ Fw f (t+k) := by
        by_cases hk0 : k = 0
        · subst hk0; simp
        · exact h k (by omega) (by omega)
      rw [Ar_succ]
      show Fw f (t+k+1) - Fw f t ≤ _
      omega

theorem dip (t k : Nat) (hw : Win f t k) : ∃ i, 1 ≤ i ∧ i ≤ k ∧ Fw f (t+i) < Fw f t := by
  apply Classical.byContradiction
  intro hno
  have h : ∀ i, 1 ≤ i → i ≤ k → Fw f t ≤ Fw f (t+i) := by
    intro i h1 h2
    apply Classical.byContradiction
    intro hlt
    exact hno ⟨i, h1, h2, by omega⟩
  have := area_ge f t k h
  obtain ⟨_, h1, h2⟩ := hw
  omega

theorem area_lower1 (t k1 : Nat) : ∀ k2 : Nat,
    (∀ i, k1 < i → i ≤ k1 + k2 → Fw f t + 1 ≤ Fw f (t+i)) →
    Ar f t k1 + k2 ≤ Ar f t (k1 + k2)
  | 0, _ => by simp
  | k2+1, h => by
      have ih := area_lower1 t k1 k2 (fun i h1 h2 => h i h1 (by omega))
      have hi := h (k1 + k2 + 1) (by omega) (by omega)
      rw [show k1 + (k2+1) = k1 + k2 + 1 from rfl, Ar_succ,
        show t + (k1 + k2) + 1 = t + (k1 + k2 + 1) by omega]
      push_cast; omega

theorem area_upper2 (t k1 : Nat) : ∀ k2 : Nat,
    (∀ i, k1 < i → i ≤ k1 + k2 → Fw f (t+i) ≤ Fw f t + 2) →
    Ar f t (k1 + k2) ≤ Ar f t k1 + 2 * k2
  | 0, _ => by simp
  | k2+1, h => by
      have ih := area_upper2 t k1 k2 (fun i h1 h2 => h i h1 (by omega))
      have hi := h (k1 + k2 + 1) (by omega) (by omega)
      rw [show k1 + (k2+1) = k1 + k2 + 1 from rfl, Ar_succ,
        show t + (k1 + k2) + 1 = t + (k1 + k2 + 1) by omega]
      push_cast; omega

theorem win_ge3 (t k : Nat) (hw : Win f t k) : 3 ≤ k := by
  obtain ⟨hk, h1, h2⟩ := hw
  apply Classical.byContradiction
  intro hlt
  rcases (show k = 1 ∨ k = 2 by omega) with rfl | rfl
  · have : Ar f t 1 = Fw f (t+1) - Fw f t := by simp [Ar]
    omega
  · have a := fw_cases f t
    have b := fw_cases f (t+1)
    rw [show t + 1 + 1 = t + 2 from rfl] at b
    rcases a with ⟨a, _⟩ | ⟨a, _⟩ <;> rcases b with ⟨b, _⟩ | ⟨b, _⟩ <;> omega

theorem win3 (t : Nat) (hw : Win f t 3) :
    f t = false ∧ f (t+1) = true ∧ f (t+2) = true := by
  obtain ⟨_, h1, h2⟩ := hw
  rw [Ar3] at h2
  have a := fw_cases f t
  have b := fw_cases f (t+1)
  have c := fw_cases f (t+2)
  rw [show t + 1 + 1 = t + 2 from rfl] at b
  rw [show t + 2 + 1 = t + 3 from rfl] at c
  rcases a with ⟨a, ha⟩ | ⟨a, ha⟩ <;> rcases b with ⟨b, hb⟩ | ⟨b, hb⟩ <;>
    rcases c with ⟨c, hc⟩ | ⟨c, hc⟩ <;>
    first
    | exact ⟨ha, hb, hc⟩
    | (exfalso; omega)

end walk

/-! ## Segments of the pure word -/

theorem seg_succ (f : Nat → Bool) (s m : Nat) : seg f s (m+1) = seg f s m ++ [f (s+m)] := by
  simp [seg, List.range_succ]

theorem seg_length (f : Nat → Bool) (s m : Nat) : (seg f s m).length = m := by
  simp [seg]

theorem seg_add (f : Nat → Bool) (s a : Nat) : ∀ b : Nat, seg f s (a+b) = seg f s a ++ seg f (s+a) b
  | 0 => by simp [seg]
  | b+1 => by
      rw [show a + (b+1) = a + b + 1 from rfl, seg_succ, seg_add f s a b, seg_succ,
        List.append_assoc, show s + (a + b) = s + a + b by omega]

theorem seg_get (f : Nat → Bool) (s m i : Nat) (h : i < m) : (seg f s m)[i]? = some (f (s+i)) := by
  simp [seg, h]

theorem seg_mass (f : Nat → Bool) (s : Nat) : ∀ m : Nat, mass (seg f s m) = Fw f (s+m) - Fw f s
  | 0 => by simp [seg]
  | m+1 => by
      rw [seg_succ, mass_append, seg_mass f s m, show s + (m+1) = s + m + 1 from rfl, Fw_succ]
      simp [mass]
      omega

/-! ## Block words -/

def aasW : List Bool := [false, true, true, true]
def tripW : List Bool := [false, false, true, true, true, true, false, true, true, true]

theorem block_first {w : List Bool} (h : BlockWord w) : w = [] ∨ ∃ v, BlockWord v ∧
    (w = [true] ++ v ∨ w = aasW ++ v ∨ w = tripW ++ v) := by
  induction h with
  | nil => exact Or.inl rfl
  | @free w hw ih =>
    right
    rcases ih with rfl | ⟨v, hv, h | h | h⟩
    · exact ⟨[], BlockWord.nil, Or.inl rfl⟩
    · exact ⟨v ++ [true], BlockWord.free hv, Or.inl (by rw [h, List.append_assoc])⟩
    · exact ⟨v ++ [true], BlockWord.free hv, Or.inr (Or.inl (by rw [h, List.append_assoc]))⟩
    · exact ⟨v ++ [true], BlockWord.free hv, Or.inr (Or.inr (by rw [h, List.append_assoc]))⟩
  | @aas w hw ih =>
    right
    rcases ih with rfl | ⟨v, hv, h | h | h⟩
    · exact ⟨[], BlockWord.nil, Or.inr (Or.inl rfl)⟩
    · exact ⟨v ++ aasW, BlockWord.aas hv, Or.inl (by rw [h, List.append_assoc]; rfl)⟩
    · exact ⟨v ++ aasW, BlockWord.aas hv, Or.inr (Or.inl (by rw [h, List.append_assoc]; rfl))⟩
    · exact ⟨v ++ aasW, BlockWord.aas hv, Or.inr (Or.inr (by rw [h, List.append_assoc]; rfl))⟩
  | @triple w hw ih =>
    right
    rcases ih with rfl | ⟨v, hv, h | h | h⟩
    · exact ⟨[], BlockWord.nil, Or.inr (Or.inr rfl)⟩
    · exact ⟨v ++ tripW, BlockWord.triple hv, Or.inl (by rw [h, List.append_assoc]; rfl)⟩
    · exact ⟨v ++ tripW, BlockWord.triple hv, Or.inr (Or.inl (by rw [h, List.append_assoc]; rfl))⟩
    · exact ⟨v ++ tripW, BlockWord.triple hv, Or.inr (Or.inr (by rw [h, List.append_assoc]; rfl))⟩

theorem block_mass {w : List Bool} (h : BlockWord w) : w = [] ∨ 1 ≤ mass w := by
  induction h with
  | nil => exact Or.inl rfl
  | @free w hw ih =>
    right; rw [mass_append]
    have : mass [true] = 1 := by decide
    rcases ih with rfl | ih <;> simp_all <;> omega
  | @aas w hw ih =>
    right; rw [mass_append]
    have : mass [false, true, true, true] = 2 := by decide
    rcases ih with rfl | ih <;> simp_all <;> omega
  | @triple w hw ih =>
    right; rw [mass_append]
    have : mass [false, false, true, true, true, true, false, true, true, true] = 4 := by decide
    rcases ih with rfl | ih <;> simp_all <;> omega

theorem block_mass2 {w : List Bool} (h : BlockWord w) (hm : mass w = 2)
    (h0 : w[0]? = some false) : w = aasW := by
  rcases block_first h with rfl | ⟨v, hv, hw | hw | hw⟩
  · simp at h0
  · subst hw; simp at h0
  · subst hw
    rw [mass_append] at hm
    have : mass aasW = 2 := by decide
    rcases block_mass hv with rfl | hv'
    · rfl
    · omega
  · subst hw
    rw [mass_append] at hm
    have : mass tripW = 4 := by decide
    rcases block_mass hv with rfl | hv'
    · simp at hm; omega
    · omega

theorem block_SS {w : List Bool} (h : BlockWord w)
    (h0 : w[0]? = some false) (h1 : w[1]? = some false) : ∃ v, w = tripW ++ v := by
  rcases block_first h with rfl | ⟨v, hv, hw | hw | hw⟩
  · simp at h0
  · subst hw; simp at h0
  · subst hw; simp [aasW] at h1
  · exact ⟨v, hw⟩

theorem block_SSS {w : List Bool} (h : BlockWord w)
    (h0 : w[0]? = some false) (h1 : w[1]? = some false) (h2 : w[2]? = some false) : False := by
  obtain ⟨v, rfl⟩ := block_SS h h0 h1
  simp [tripW] at h2

theorem cN_sub (P : Nat → Prop) (s a m : Nat) (h : a ≤ m) :
    cN P s m = cN P s a + cN P (s + a) (m - a) := by
  have := cN_add P s a (m - a)
  rw [Nat.add_sub_cancel' h] at this
  exact this

theorem cN_sub0 (P : Nat → Prop) (a m : Nat) (h : a ≤ m) :
    cN P 0 m = cN P 0 a + cN P a (m - a) := by
  have := cN_sub P 0 a m h
  rw [Nat.zero_add] at this
  exact this

/-! ## Step 1: the shape `S^j A A A` -/

theorem step1 (f : Nat → Bool) (L : Nat) (hwin : Win f 0 L) (hA : f L = true)
    (htight : cN (EndN f 0) 0 (L+1) = cN (fun i => f i = false) 0 (L+1)) :
    ∃ j, 1 ≤ j ∧ j + 2 ≤ L ∧ (∀ i, i < j → f i = false) ∧
      f j = true ∧ f (j+1) = true ∧ f (j+2) = true ∧
      ¬ EndN f 0 j ∧ ¬ EndN f 0 (j+1) ∧
      (∀ i, j + 2 ≤ i → i ≤ L → f i = true → EndN f 0 i) := by
  have hEL : EndN f 0 L := ⟨hA, 0, L, Nat.le_refl 0, Nat.zero_add L, hwin⟩
  have hEL' : EndN f 0 (0 + L) := by rw [Nat.zero_add]; exact hEL
  have hAL' : f (0 + L) = true := by rw [Nat.zero_add]; exact hA
  have hFL : Fw f L = 1 := by
    have := hwin.2.1; rw [Nat.zero_add] at this; simpa [Fw] using this
  obtain ⟨w1, w2⟩ := cN_walk f 0 (L+1)
  rw [Nat.zero_add, Fw_succ, hFL, hA] at w1
  have hE1 := cN_succ_pos (EndN f 0) 0 L hEL'
  have hA1 := cN_succ_pos (fun i => f i = true) 0 L hAL'
  have hS1 := cN_succ_neg (fun i => f i = false) 0 L (by rw [hAL']; simp)
  let N : Nat → Prop := fun i => f i = true ∧ ¬ EndN f 0 i
  have hsplit := cN_split (fun i => f i = true) (EndN f 0) 0 L
  have hcongr : cN (fun i => f i = true ∧ EndN f 0 i) 0 L = cN (EndN f 0) 0 L :=
    cN_congr _ _ 0 L (fun i _ _ => ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩)
  have hNL : cN N 0 L = 2 := by
    have : cN N 0 L = cN (fun i => f i = true ∧ ¬ EndN f 0 i) 0 L := rfl
    have hs : sign true = 1 := rfl
    have hF0 : Fw f 0 = 0 := rfl
    rw [hs, hF0] at w1
    omega
  obtain ⟨b1, hb1L, hEb1, hfirst⟩ := first_mark (EndN f 0) L ⟨L, Nat.le_refl L, hEL⟩
  obtain ⟨hAb1, t, k, -, htk, hwk⟩ := hEb1
  have hNA : cN N t k = cN (fun i => f i = true) t k :=
    cN_congr _ _ t k (fun i _ h2 => ⟨fun h => h.1, fun h => ⟨h, hfirst i (by omega)⟩⟩)
  obtain ⟨v1, v2⟩ := cN_walk f t k
  have hk3 := win_ge3 f t k hwk
  have hs1 := cN_sub0 N t L (by omega)
  have hs2 := cN_sub N t k (L - t) (by omega)
  have hFk := hwk.2.1
  have hk : k = 3 := by omega
  subst hk
  have hN0 : cN N 0 t = 0 := by omega
  have hN3 : cN N (t+3) (L - t - 3) = 0 := by
    rw [show L - t - 3 = L - t - 3 from rfl] at hs2; omega
  obtain ⟨p1, p2, p3⟩ := win3 f t hwk
  refine ⟨t+1, by omega, by omega, ?_, p2, by rw [show t + 1 + 1 = t + 2 from rfl]; exact p3,
    by rw [show t + 1 + 2 = b1 by omega]; exact hAb1,
    hfirst (t+1) (by omega), hfirst (t+1+1) (by omega), ?_⟩
  · intro i hi
    by_cases hit : i = t
    · rw [hit]; exact p1
    · have hn := not_of_cN_zero N 0 t hN0 i (Nat.zero_le _) (by omega)
      have he := hfirst i (by omega)
      cases h : f i
      · rfl
      · exact absurd ⟨h, he⟩ hn
  · intro i h1 h2 h3
    by_cases hiL : i = L
    · rw [hiL]; exact hEL
    · have hn := not_of_cN_zero N (t+3) (L - t - 3) hN3 i (by omega) (by omega)
      apply Classical.byContradiction
      intro he
      exact hn ⟨h3, he⟩

/-! ## Levels and counts after step 1 -/

theorem levels_prefix (f : Nat → Bool) (j : Nat) (hS : ∀ i, i < j → f i = false) :
    ∀ i, i ≤ j → Fw f i = -(i : Int)
  | 0, _ => rfl
  | i+1, h => by
      have ih := levels_prefix f j hS i (by omega)
      rw [Fw_succ, hS i (by omega), ih]
      simp [sign]; omega

theorem levels_top (f : Nat → Bool) (j : Nat) (hS : ∀ i, i < j → f i = false)
    (hAj : f j = true) (hAj1 : f (j+1) = true) (hAj2 : f (j+2) = true) :
    Fw f (j+1) = -(j : Int) + 1 ∧ Fw f (j+2) = -(j : Int) + 2 ∧ Fw f (j+3) = -(j : Int) + 3 := by
  have h0 := levels_prefix f j hS j (Nat.le_refl j)
  have h1 : Fw f (j+1) = -(j : Int) + 1 := by rw [Fw_succ, hAj, h0]; rfl
  have h2 : Fw f (j+2) = -(j : Int) + 2 := by
    rw [show j + 2 = j + 1 + 1 from rfl, Fw_succ, hAj1, h1]; simp [sign]; omega
  have h3 : Fw f (j+3) = -(j : Int) + 3 := by
    rw [show j + 3 = j + 2 + 1 from rfl, Fw_succ, hAj2, h2]; simp [sign]; omega
  exact ⟨h1, h2, h3⟩

theorem count_end (f : Nat → Bool) (L j s q : Nat) (hS : ∀ i, i < j → f i = false)
    (hAj : f j = true) (hAj1 : f (j+1) = true)
    (hNj : ¬ EndN f 0 j) (hNj1 : ¬ EndN f 0 (j+1))
    (hI5 : ∀ i, j + 2 ≤ i → i ≤ L → f i = true → EndN f 0 i)
    (hs : s ≤ j) (hq1 : j + 2 ≤ q) (hq2 : q ≤ L + 1) :
    cN (EndN f 0) s (q - s) + 2 = cN (fun i => f i = true) s (q - s) := by
  have hE := cN_sub (EndN f 0) s (j + 2 - s) (q - s) (by omega)
  have hA := cN_sub (fun i => f i = true) s (j + 2 - s) (q - s) (by omega)
  rw [show s + (j + 2 - s) = j + 2 by omega, show q - s - (j + 2 - s) = q - (j+2) by omega] at hE hA
  have hE0 : cN (EndN f 0) s (j + 2 - s) = 0 := by
    apply cN_zero_of
    intro i h1 h2 hi
    by_cases hij : i < j
    · have := hi.1; rw [hS i hij] at this; exact absurd this (by decide)
    · by_cases hij' : i = j
      · rw [hij'] at hi; exact hNj hi
      · have : i = j + 1 := by omega
        rw [this] at hi; exact hNj1 hi
  have hA2 : cN (fun i => f i = true) s (j + 2 - s) = 2 := by
    have h := cN_sub (fun i => f i = true) s (j - s) (j + 2 - s) (by omega)
    rw [show s + (j - s) = j by omega, show j + 2 - s - (j - s) = 2 by omega] at h
    have hz : cN (fun i => f i = true) s (j - s) = 0 := by
      apply cN_zero_of
      intro i h1 h2 hi
      have := hS i (by omega)
      rw [this] at hi; exact absurd hi (by decide)
    have h1 : cN (fun i => f i = true) j 1 = 1 :=
      cN_succ_pos (fun i => f i = true) j 0 (by simpa using hAj)
    have h2 : cN (fun i => f i = true) j 2 = 2 := by
      rw [show (2 : Nat) = 1 + 1 from rfl, cN_succ_pos (fun i => f i = true) j 1 hAj1, h1]
    omega
  have hc : cN (EndN f 0) (j+2) (q - (j+2)) = cN (fun i => f i = true) (j+2) (q - (j+2)) :=
    cN_congr _ _ _ _ (fun i h1 h2 => ⟨fun h => h.1, fun h => hI5 i h1 (by omega) h⟩)
  omega

/-! ## Step 2 and step 3: level caps -/

theorem step2 (f : Nat → Bool) (L j : Nat) (hj1 : 1 ≤ j) (hS : ∀ i, i < j → f i = false)
    (hAj : f j = true) (hAj1 : f (j+1) = true) (hAj2 : f (j+2) = true)
    (hNj : ¬ EndN f 0 j) (hNj1 : ¬ EndN f 0 (j+1))
    (hI5 : ∀ i, j + 2 ≤ i → i ≤ L → f i = true → EndN f 0 i)
    (hH0 : ∀ m, m < L + 1 → cN (EndN f 0) 0 m ≤ cN (fun i => f i = false) 0 m) :
    ∀ q, q ≤ L → Fw f q ≤ 2 := by
  intro q hq
  have hpre := levels_prefix f j hS
  obtain ⟨t1, t2, t3⟩ := levels_top f j hS hAj hAj1 hAj2
  by_cases hqj : j + 2 ≤ q
  · have hc := count_end f L j 0 q hS hAj hAj1 hNj hNj1 hI5 (Nat.zero_le _) hqj (by omega)
    rw [Nat.sub_zero] at hc
    have hh := hH0 q (by omega)
    obtain ⟨w1, w2⟩ := cN_walk f 0 q
    rw [Nat.zero_add] at w1
    have hF0 : Fw f 0 = 0 := rfl
    omega
  · by_cases hqj' : q ≤ j
    · have := hpre q hqj'; omega
    · have : q = j + 1 := by omega
      subst this; omega

theorem step3 (f : Nat → Bool) (L j : Nat) (hj2 : 2 ≤ j) (hS : ∀ i, i < j → f i = false)
    (hAj : f j = true) (hAj1 : f (j+1) = true) (hAj2 : f (j+2) = true)
    (hNj : ¬ EndN f 0 j) (hNj1 : ¬ EndN f 0 (j+1))
    (hI5 : ∀ i, j + 2 ≤ i → i ≤ L → f i = true → EndN f 0 i)
    (hH0 : ∀ m, m < L + 1 → cN (EndN f 0) 0 m ≤ cN (fun i => f i = false) 0 m)
    (hE0 : ∀ m, 0 < m → m < L + 1 → cN (EndN f 0) 0 m = cN (fun i => f i = false) 0 m →
      EndN f 0 (m - 1) → BlockWord (seg f 0 m)) :
    ∀ q, q ≤ L → Fw f q ≤ 1 := by
  have h2 := step2 f L j (by omega) hS hAj hAj1 hAj2 hNj hNj1 hI5 hH0
  have hpre := levels_prefix f j hS
  obtain ⟨t1, t2, t3⟩ := levels_top f j hS hAj hAj1 hAj2
  intro q hq
  apply Classical.byContradiction
  intro hlt
  have hq2 : Fw f q = 2 := by have := h2 q hq; omega
  have hqj : j + 3 ≤ q := by
    apply Classical.byContradiction
    intro hne
    by_cases hqj' : q ≤ j
    · have := hpre q hqj'; omega
    · rcases (show q = j + 1 ∨ q = j + 2 by omega) with rfl | rfl <;> omega
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  have hr : Fw f r = 1 ∧ f r = true := by
    rcases fw_cases f r with ⟨a, b⟩ | ⟨a, b⟩
    · exact ⟨by omega, b⟩
    · have := h2 r (by omega); omega
  have hEr := hI5 r (by omega) (by omega) hr.2
  have hc := count_end f L j 0 (r+1) hS hAj hAj1 hNj hNj1 hI5 (Nat.zero_le _) (by omega) (by omega)
  rw [Nat.sub_zero] at hc
  obtain ⟨w1, w2⟩ := cN_walk f 0 (r+1)
  rw [Nat.zero_add] at w1
  have hF0 : Fw f 0 = 0 := rfl
  have hBW := hE0 (r+1) (by omega) (by omega) (by omega) (by simpa using hEr)
  have hm : mass (seg f 0 (r+1)) = 2 := by rw [seg_mass, Nat.zero_add]; omega
  have h0 : (seg f 0 (r+1))[0]? = some false := by
    rw [seg_get f 0 (r+1) 0 (by omega)]; simp [hS 0 (by omega)]
  have haas := block_mass2 hBW hm h0
  have h1 := seg_get f 0 (r+1) 1 (by omega)
  rw [haas, hS (0+1) (by omega)] at h1
  simp [aasW] at h1

/-! ## Steps 4 and 5: level floors -/

theorem end_level (f : Nat → Bool) (u : Nat) (h : EndN f 0 u) :
    ∃ t k, t + k = u ∧ 0 < k ∧ Fw f u = Fw f t + 1 ∧ Win f t k := by
  obtain ⟨_, t, k, -, htk, hw⟩ := h
  refine ⟨t, k, htk, hw.1, ?_, hw⟩
  rw [← htk]; exact hw.2.1

theorem step4 (f : Nat → Bool) (L j : Nat) (hj1 : 1 ≤ j) (hS : ∀ i, i < j → f i = false)
    (hAj : f j = true) (hAj1 : f (j+1) = true) (hAj2 : f (j+2) = true)
    (hI5 : ∀ i, j + 2 ≤ i → i ≤ L → f i = true → EndN f 0 i) (hFn : Fw f (L+1) = 2) :
    ∀ u, j + 1 ≤ u → u ≤ L + 1 → -(j : Int) + 1 ≤ Fw f u := by
  have hpre := levels_prefix f j hS
  obtain ⟨t1, t2, t3⟩ := levels_top f j hS hAj hAj1 hAj2
  apply floor_induct f (j+1) (L+1) (-(j : Int) + 1) (by omega)
  intro c hc hfl u h1 h2 hFu hfu
  have hu : j + 2 ≤ u := by
    apply Classical.byContradiction
    intro hne
    have : u = j + 1 := by omega
    subst this; omega
  obtain ⟨t, k, htk, hk, hF, -⟩ := end_level f u (hI5 u hu (by omega) hfu)
  by_cases ht : t ≤ j
  · have := hpre t ht; omega
  · have := hfl t (by omega) (by omega); omega

theorem step5a (f : Nat → Bool) (L j : Nat) (hj1 : 1 ≤ j) (hS : ∀ i, i < j → f i = false)
    (hAj : f j = true) (hAj1 : f (j+1) = true) (hAj2 : f (j+2) = true)
    (hI5 : ∀ i, j + 2 ≤ i → i ≤ L → f i = true → EndN f 0 i) (hFn : Fw f (L+1) = 2)
    (h4 : ∀ u, j + 1 ≤ u → u ≤ L + 1 → -(j : Int) + 1 ≤ Fw f u) :
    ∀ u, j + 2 ≤ u → u ≤ L + 1 → -(j : Int) + 2 ≤ Fw f u := by
  have hpre := levels_prefix f j hS
  apply floor_lemma f (j+2) (L+1) (-(j : Int) + 2) (by omega)
  intro u h1 h2 hFu hfu
  obtain ⟨t, k, htk, hk, hF, hw⟩ := end_level f u (hI5 u h1 (by omega) hfu)
  by_cases ht : t ≤ j
  · have := hpre t ht
    have htj : t = j := by omega
    subst htj
    obtain ⟨i, hi1, hi2, hi3⟩ := dip f t k hw
    have := h4 (t+i) (by omega) (by omega)
    have := hpre t (Nat.le_refl t)
    omega
  · have := h4 t (by omega) (by omega); omega

theorem step5b (f : Nat → Bool) (L j : Nat) (hj1 : 1 ≤ j) (hS : ∀ i, i < j → f i = false)
    (hAj : f j = true) (hAj1 : f (j+1) = true) (hAj2 : f (j+2) = true)
    (hI5 : ∀ i, j + 2 ≤ i → i ≤ L → f i = true → EndN f 0 i) (hFn : Fw f (L+1) = 2)
    (h5 : ∀ u, j + 2 ≤ u → u ≤ L + 1 → -(j : Int) + 2 ≤ Fw f u) :
    ∀ u, j + 3 ≤ u → u ≤ L + 1 → -(j : Int) + 3 ≤ Fw f u := by
  have hpre := levels_prefix f j hS
  obtain ⟨t1, t2, t3⟩ := levels_top f j hS hAj hAj1 hAj2
  apply floor_lemma f (j+3) (L+1) (-(j : Int) + 3) (by omega)
  intro u h1 h2 hFu hfu
  obtain ⟨t, k, htk, hk, hF, hw⟩ := end_level f u (hI5 u (by omega) (by omega) hfu)
  by_cases ht : t ≤ j
  · have := hpre t ht
    have htj : t + 1 = j := by omega
    have a1 : Fw f (t+1) = -(j : Int) := by rw [htj]; exact hpre j (Nat.le_refl j)
    have a2 : Fw f (t+2) = -(j : Int) + 1 := by rw [show t + 2 = j + 1 by omega]; exact t1
    have hA2 : Ar f t 2 = -1 := by rw [Ar2]; omega
    have hlow := area_lower1 f t 2 (k - 2) (fun i h1 h2 => by
      have := h5 (t+i) (by omega) (by omega); omega)
    rw [show 2 + (k - 2) = k by omega] at hlow
    have := hw.2.2
    omega
  · by_cases ht1 : t = j + 1
    · subst ht1
      obtain ⟨i, hi1, hi2, hi3⟩ := dip f (j+1) k hw
      have := h5 (j+1+i) (by omega) (by omega)
      omega
    · have := h5 t (by omega) (by omega); omega

/-! ## Step 6, case `j ≥ 4`: the restart at clock 2 -/

theorem end_mono (f : Nat → Bool) (s s' b : Nat) (hs : s ≤ s') (h : EndN f s' b) : EndN f s b := by
  obtain ⟨h1, t, k, h2, h3, h4⟩ := h
  exact ⟨h1, t, k, by omega, h3, h4⟩

theorem case_big (f : Nat → Bool) (L j : Nat) (hj4 : 4 ≤ j) (hS : ∀ i, i < j → f i = false)
    (hAj : f j = true) (hAj1 : f (j+1) = true) (hAj2 : f (j+2) = true)
    (hNj : ¬ EndN f 0 j) (hNj1 : ¬ EndN f 0 (j+1))
    (hI5 : ∀ i, j + 2 ≤ i → i ≤ L → f i = true → EndN f 0 i) (hFL : Fw f L = 1)
    (hH2 : ∀ m, 2 + m ≤ L + 1 → m < L + 1 →
      cN (EndN f 2) 2 m ≤ cN (fun i => f i = false) 2 m)
    (hE2 : ∀ m, 0 < m → 2 + m ≤ L + 1 → m < L + 1 →
      cN (EndN f 2) 2 m = cN (fun i => f i = false) 2 m →
      EndN f 2 (2 + m - 1) → BlockWord (seg f 2 m)) : False := by
  have hpre := levels_prefix f j hS
  obtain ⟨t1, t2, t3⟩ := levels_top f j hS hAj hAj1 hAj2
  have hF0 : Fw f 0 = 0 := rfl
  have hF1 : Fw f 1 = -1 := hpre 1 (by omega)
  have hF2 : Fw f 2 = -2 := hpre 2 (by omega)
  obtain ⟨q, hqL, hFq, hbelow⟩ : ∃ q, q ≤ L ∧ Fw f q = 1 ∧ ∀ u, u < q → Fw f u ≤ 0 := by
    rcases first_hit f L with h | h
    · have := h L (Nat.le_refl L); omega
    · exact h
  have hqj : j + 4 ≤ q := by
    apply Classical.byContradiction
    intro hne
    by_cases hqj' : q ≤ j
    · have := hpre q hqj'; omega
    · rcases (show q = j + 1 ∨ q = j + 2 ∨ q = j + 3 by omega) with rfl | rfl | rfl <;> omega
  -- counting on [2, q)
  have hc := count_end f L j 2 q hS hAj hAj1 hNj hNj1 hI5 (by omega) (by omega) (by omega)
  have hsp := cN_split (EndN f 0) (EndN f 2) 2 (q - 2)
  have hcg : cN (fun i => EndN f 0 i ∧ EndN f 2 i) 2 (q - 2) = cN (EndN f 2) 2 (q - 2) :=
    cN_congr _ _ _ _ (fun i _ _ => ⟨fun h => h.2, fun h => ⟨end_mono f 0 2 i (by omega) h, h⟩⟩)
  have hY : cN (fun i => EndN f 0 i ∧ ¬ EndN f 2 i) 2 (q - 2) ≤ 1 := by
    have hz : cN (fun i => EndN f 0 i ∧ ¬ EndN f 2 i) 2 (q - 3) = 0 := by
      apply cN_zero_of
      intro i h1 h2 ⟨hE0, hnE2⟩
      obtain ⟨hfi, t, k, -, htk, hw⟩ := hE0
      have hFi : Fw f i = Fw f t + 1 := by rw [← htk]; exact hw.2.1
      by_cases ht2 : 2 ≤ t
      · exact hnE2 ⟨hfi, t, k, ht2, htk, hw⟩
      · rcases (show t = 0 ∨ t = 1 by omega) with rfl | rfl
        · have := hbelow i (by omega); omega
        · have hup : Fw f (i+1) = Fw f i + 1 := by rw [Fw_succ, hfi]; rfl
          have := hbelow (i+1) (by omega); omega
    have := cN_succ_le (fun i => EndN f 0 i ∧ ¬ EndN f 2 i) 2 (q - 3)
    rw [show q - 3 + 1 = q - 2 by omega] at this
    omega
  obtain ⟨w1, w2⟩ := cN_walk f 2 (q - 2)
  rw [show 2 + (q - 2) = q by omega] at w1
  have hcap := hH2 (q - 2) (by omega) (by omega)
  have htight : cN (EndN f 2) 2 (q - 2) = cN (fun i => f i = false) 2 (q - 2) := by omega
  -- the clock j+2 is endable from 2
  have hEj2 : EndN f 2 (j+2) := by
    refine ⟨hAj2, j - 1, 3, by omega, by omega, by omega, ?_, ?_⟩
    · have := hpre (j-1) (by omega)
      rw [show j - 1 + 3 = j + 2 by omega, t2, this]; omega
    · have := hpre (j-1) (by omega)
      rw [Ar3, show j - 1 + 1 = j by omega, show j - 1 + 2 = j + 1 by omega,
        show j - 1 + 3 = j + 2 by omega, t1, t2, this, hpre j (Nat.le_refl j)]
      omega
  obtain ⟨m', hm'le, hm'mark, hm'none⟩ := last_markN (EndN f 2) 2 (q - 2)
  have hm'j : j < m' := by
    apply Classical.byContradiction
    intro hne
    have := hm'none j (by omega) (by omega)
    rw [Nat.add_comm] at this
    exact this hEj2
  have hmk : EndN f 2 (2 + m' - 1) := by
    rcases hm'mark with h | h
    · omega
    · exact h
  have hEsub := cN_sub (EndN f 2) 2 m' (q - 2) hm'le
  have hEtail : cN (EndN f 2) (2 + m') (q - 2 - m') = 0 := by
    apply cN_zero_of
    intro i h1 h2
    have := hm'none (i - 2) (by omega) (by omega)
    rwa [show 2 + (i - 2) = i by omega] at this
  have hSsub := cN_sub (fun i => f i = false) 2 m' (q - 2) hm'le
  have hcap' := hH2 m' (by omega) (by omega)
  have hBW := hE2 m' (by omega) (by omega) (by omega) (by omega) hmk
  have g0 : (seg f 2 m')[0]? = some false := by
    rw [seg_get f 2 m' 0 (by omega), hS (2+0) (by omega)]
  have g1 : (seg f 2 m')[1]? = some false := by
    rw [seg_get f 2 m' 1 (by omega), hS (2+1) (by omega)]
  by_cases hj5 : 5 ≤ j
  · have g2 : (seg f 2 m')[2]? = some false := by
      rw [seg_get f 2 m' 2 (by omega), hS (2+2) (by omega)]
    exact block_SSS hBW g0 g1 g2
  · obtain ⟨v, hv⟩ := block_SS hBW g0 g1
    have hlen := congrArg List.length hv
    rw [seg_length, List.length_append, show tripW.length = 10 from rfl] at hlen
    have hsplit := seg_add f 2 10 (m' - 10)
    rw [show 10 + (m' - 10) = m' by omega, hv] at hsplit
    have h10 : seg f 2 10 = tripW :=
      List.append_inj_left hsplit.symm (by rw [seg_length]; rfl)
    have hm := seg_mass f 2 10
    rw [h10, show mass tripW = 4 by decide, show 2 + 10 = 12 from rfl, hF2] at hm
    by_cases h12 : 12 < q
    · have := hbelow 12 h12; omega
    · have : q = 12 := by omega
      subst this; omega

/-! ## The pure theorem -/

theorem pure_main (f : Nat → Bool) (L : Nat) (hL4 : L % 4 = 3)
    (hwin : Win f 0 L) (hA : f L = true)
    (htight : cN (EndN f 0) 0 (L+1) = cN (fun i => f i = false) 0 (L+1))
    (hH0 : ∀ m, m < L + 1 → cN (EndN f 0) 0 m ≤ cN (fun i => f i = false) 0 m)
    (hE0 : ∀ m, 0 < m → m < L + 1 → cN (EndN f 0) 0 m = cN (fun i => f i = false) 0 m →
      EndN f 0 (m - 1) → BlockWord (seg f 0 m))
    (hH2 : ∀ m, 2 + m ≤ L + 1 → m < L + 1 →
      cN (EndN f 2) 2 m ≤ cN (fun i => f i = false) 2 m)
    (hE2 : ∀ m, 0 < m → 2 + m ≤ L + 1 → m < L + 1 →
      cN (EndN f 2) 2 m = cN (fun i => f i = false) 2 m →
      EndN f 2 (2 + m - 1) → BlockWord (seg f 2 m)) :
    seg f 0 (L+1) = aasW := by
  obtain ⟨j, hj1, hjL, hS, hAj, hAj1, hAj2, hNj, hNj1, hI5⟩ := step1 f L hwin hA htight
  have hFL : Fw f L = 1 := by
    have := hwin.2.1; rw [Nat.zero_add] at this; simpa [Fw] using this
  have hFn : Fw f (L+1) = 2 := by rw [Fw_succ, hA, hFL]; rfl
  have hpre := levels_prefix f j hS
  obtain ⟨t1, t2, t3⟩ := levels_top f j hS hAj hAj1 hAj2
  have h4 := step4 f L j hj1 hS hAj hAj1 hAj2 hI5 hFn
  have h5a := step5a f L j hj1 hS hAj hAj1 hAj2 hI5 hFn h4
  have h5b := step5b f L j hj1 hS hAj hAj1 hAj2 hI5 hFn h5a
  -- for `j ≥ 2` the walk stays at most one, so the clock `L-1` is an addition at level zero
  have hlow : 2 ≤ j → Fw f (L-1) = 0 ∧ f (L-1) = true ∧ ∀ q, q ≤ L → Fw f q ≤ 1 := by
    intro hj2
    have h3 := step3 f L j hj2 hS hAj hAj1 hAj2 hNj hNj1 hI5 hH0 hE0
    have hc := fw_cases f (L-1)
    rw [show L - 1 + 1 = L by omega, hFL] at hc
    rcases hc with ⟨a, b⟩ | ⟨a, b⟩
    · exact ⟨by omega, b, h3⟩
    · have := h3 (L-1) (by omega); omega
  by_cases hj4 : 4 ≤ j
  · exact (case_big f L j hj4 hS hAj hAj1 hAj2 hNj hNj1 hI5 hFL hH2 hE2).elim
  rcases (show j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl
  · -- j = 1: the walk stays at least two from clock 4 on
    have hL3 : L = 3 := by
      apply Classical.byContradiction
      intro hne
      have := h5b L (by omega) (by omega)
      omega
    subst hL3
    have a0 : f 0 = false := hS 0 (by omega)
    have a2 : f 2 = true := hAj1
    have a3 : f 3 = true := hAj2
    simp [seg, List.range_succ, aasW, a0, hAj, a2, a3]
  · -- j = 2
    obtain ⟨hz, -, -⟩ := hlow (by omega)
    have := h5b (L-1) (by omega) (by omega)
    omega
  · -- j = 3
    obtain ⟨hz, hfa, h3⟩ := hlow (by omega)
    obtain ⟨t, k, htk, hk, hF, hw⟩ := end_level f (L-1) (hI5 (L-1) (by omega) (by omega) hfa)
    by_cases ht : t ≤ 3
    · have := hpre t ht
      have ht1 : t = 1 := by omega
      subst ht1
      have e1 : Fw f 1 = -1 := hpre 1 (by omega)
      have e2 : Fw f (1+1) = -2 := hpre 2 (by omega)
      have e3 : Fw f (1+2) = -3 := hpre 3 (by omega)
      have e4 : Fw f (1+3) = -2 := by have := t1; exact this
      have e5 : Fw f (1+4) = -1 := by have := t2; exact this
      have hA4 : Ar f 1 4 = -4 := by rw [Ar4, e1, e2, e3, e4, e5]; rfl
      have hlo := area_lower1 f 1 4 (k - 4) (fun i h1 h2 => by
        have := h5b (1+i) (by omega) (by omega); omega)
      have hup := area_upper2 f 1 4 (k - 4) (fun i h1 h2 => by
        have := h3 (1+i) (by omega); omega)
      rw [show 4 + (k - 4) = k by omega] at hlo hup
      have := hw.2.2
      omega
    · by_cases ht4 : t = 4
      · subst ht4
        have : Fw f 4 = -2 := t1
        omega
      · by_cases ht5 : t = 5
        · subst ht5
          obtain ⟨i, hi1, hi2, hi3⟩ := dip f 5 k hw
          have := h5b (5+i) (by omega) (by omega)
          have : Fw f 5 = -1 := t2
          omega
        · have := h5b t (by omega) (by omega)
          omega

/-! ## Bridges from integer clocks to the pure word -/

theorem countP_cN (P : Int → Prop) [DecidablePred P] (p q : Int) (s : Nat) (hq : q = p + s) :
    ∀ m : Nat, countP P q m = cN (fun i => P (p + (i : Int))) s m
  | 0 => rfl
  | m+1 => by
      have ih := countP_cN P p q s hq m
      show countP P q m + (if P (q + (m : Int)) then 1 else 0) = _
      have hc : q + (m : Int) = p + ((s + m : Nat) : Int) := by rw [hq]; omega
      rw [ih, hc]
      by_cases h : P (p + ((s + m : Nat) : Int))
      · rw [if_pos h, cN_succ_pos (fun i => P (p + (i : Int))) s m h]
      · rw [if_neg h, cN_succ_neg (fun i => P (p + (i : Int))) s m h]; rfl

theorem endable_iff (e : Int → Bool) (p q c : Int) (s b : Nat) (hq : q = p + s) (hc : c = p + b) :
    Endable e q c ↔ EndN (fun i => e (p + (i : Int))) s b := by
  constructor
  · rintro ⟨h1, d, hd, hle, hP⟩
    have hdb : s + d ≤ b := by omega
    have hb : c = p + ((b - d + d : Nat) : Int) := by rw [hc]; congr 2; omega
    obtain ⟨m1, m2⟩ := past_bridge e p (b - d) d
    rw [← hb] at m1 m2
    refine ⟨by rw [hc] at h1; exact h1, b - d, d, by omega, by omega, hd, ?_, ?_⟩
    · have := hP.1; omega
    · rw [← m2]; exact hP.2
  · rintro ⟨h1, t, k, hst, htk, hw⟩
    have hb : c = p + ((t + k : Nat) : Int) := by rw [hc, htk]
    obtain ⟨m1, m2⟩ := past_bridge e p t k
    rw [← hb] at m1 m2
    refine ⟨by rw [hc]; exact h1, k, hw.1, by omega, ?_, ?_⟩
    · rw [m1]; have := hw.2.1; omega
    · rw [m2]; exact hw.2.2

theorem endableCount_cN (e : Int → Bool) (p q : Int) (s : Nat) (hq : q = p + s) (m : Nat) :
    endableCount e q m = cN (EndN (fun i => e (p + (i : Int))) s) s m := by
  unfold endableCount
  rw [@countP_cN (Endable e q) (classDec _) p q s hq m]
  exact cN_congr _ _ _ _ (fun i _ _ => endable_iff e p q (p + (i : Int)) s i hq rfl)

theorem subtractionCount_cN (e : Int → Bool) (p q : Int) (s : Nat) (hq : q = p + s) (m : Nat) :
    subtractionCount e q m = cN (fun i => (fun i => e (p + (i : Int))) i = false) s m := by
  unfold subtractionCount
  exact countP_cN (fun c => e c = false) p q s hq m

theorem segment_seg (e : Int → Bool) (p q : Int) (s : Nat) (hq : q = p + s) (m : Nat) :
    segment e q m = seg (fun i => e (p + (i : Int))) s m := by
  unfold segment seg
  apply List.map_congr_left
  intro i _
  show e (q + (i : Int)) = e (p + ((s + i : Nat) : Int))
  congr 1
  rw [hq]; omega

/-! ## Theorem B -/

/-- **Single window equality.** On `[p, p+n)`, assume line capacity and the
equality-class property on every proper subinterval (starts `p` and `p+2`
suffice), the interval itself is tight, and its last clock is an addition
ending a P2 window that starts at `p`. Then the interval is exactly `S A A A`. -/
theorem single_window_equality (e : Int → Bool) (p : Int) (n : Nat)
    (hH : ∀ (q : Int) (m : Nat), p ≤ q → q + m ≤ p + n → m < n → HCap e q m)
    (hE : ∀ (q : Int) (m : Nat), p ≤ q → q + m ≤ p + n → m < n → EqClassW e q m)
    (htight : endableCount e p n = subtractionCount e p n)
    (hA : e (p + n - 1) = true)
    (hwin : P2 (past e (p + n - 1) (n - 1))) :
    segment e p n = [false, true, true, true] := by
  have hlen : (past e (p + n - 1) (n - 1)).length = n - 1 := by simp [past]
  have h3 := p2_length_ge_three _ hwin
  have hid := p2_count_identities _ hwin
  rw [hlen] at h3 hid
  obtain ⟨L, rfl⟩ : ∃ L, n = L + 1 := ⟨n - 1, by omega⟩
  rw [show L + 1 - 1 = L by omega] at hwin hid
  have hL4 : L % 4 = 3 := by
    obtain ⟨i1, -, i3⟩ := hid
    omega
  let f : Nat → Bool := fun i => e (p + (i : Int))
  have hp0 : p = p + ((0 : Nat) : Int) := by simp
  have hp2 : p + 2 = p + ((2 : Nat) : Int) := by simp
  -- the window
  have hwin' : Win f 0 L := by
    obtain ⟨m1, m2⟩ := past_bridge e p 0 L
    have hc : p + ((L + 1 : Nat) : Int) - 1 = p + ((0 + L : Nat) : Int) := by omega
    rw [hc] at hwin
    refine ⟨by omega, ?_, ?_⟩
    · have := hwin.1
      rw [m1] at this
      show Fw (fun i => e (p + (i : Int))) (0 + L) = Fw (fun i => e (p + (i : Int))) 0 + 1
      omega
    · rw [← m2]; exact hwin.2
  have hA' : f L = true := by
    show e (p + (L : Int)) = true
    rw [show p + (L : Int) = p + ((L + 1 : Nat) : Int) - 1 by omega]; exact hA
  have htight' : cN (EndN f 0) 0 (L+1) = cN (fun i => f i = false) 0 (L+1) := by
    rw [← endableCount_cN e p p 0 hp0, ← subtractionCount_cN e p p 0 hp0]; exact htight
  have hH0 : ∀ m, m < L + 1 → cN (EndN f 0) 0 m ≤ cN (fun i => f i = false) 0 m := by
    intro m hm
    rw [← endableCount_cN e p p 0 hp0, ← subtractionCount_cN e p p 0 hp0]
    exact hH p m (Int.le_refl p) (by omega) hm
  have hE0 : ∀ m, 0 < m → m < L + 1 → cN (EndN f 0) 0 m = cN (fun i => f i = false) 0 m →
      EndN f 0 (m - 1) → BlockWord (seg f 0 m) := by
    intro m hm0 hm heq hend
    rw [← segment_seg e p p 0 hp0]
    apply hE p m (Int.le_refl p) (by omega) hm hm0
    · rw [endableCount_cN e p p 0 hp0, subtractionCount_cN e p p 0 hp0]; exact heq
    · exact (endable_iff e p p (p + (m : Int) - 1) 0 (m - 1) hp0 (by omega)).mpr hend
  have hH2 : ∀ m, 2 + m ≤ L + 1 → m < L + 1 →
      cN (EndN f 2) 2 m ≤ cN (fun i => f i = false) 2 m := by
    intro m hm1 hm
    rw [← endableCount_cN e p (p + 2) 2 hp2, ← subtractionCount_cN e p (p + 2) 2 hp2]
    exact hH (p + 2) m (by omega) (by omega) hm
  have hE2 : ∀ m, 0 < m → 2 + m ≤ L + 1 → m < L + 1 →
      cN (EndN f 2) 2 m = cN (fun i => f i = false) 2 m →
      EndN f 2 (2 + m - 1) → BlockWord (seg f 2 m) := by
    intro m hm0 hm1 hm heq hend
    rw [← segment_seg e p (p + 2) 2 hp2]
    apply hE (p + 2) m (by omega) (by omega) hm hm0
    · rw [endableCount_cN e p (p + 2) 2 hp2, subtractionCount_cN e p (p + 2) 2 hp2]; exact heq
    · exact (endable_iff e p (p + 2) (p + 2 + (m : Int) - 1) 2 (2 + m - 1) hp2 (by omega)).mpr hend
  rw [segment_seg e p p 0 hp0]
  exact pure_main f L hL4 hwin' hA' htight' hH0 hE0 hH2 hE2

end Recaman.SingleWindowEquality
