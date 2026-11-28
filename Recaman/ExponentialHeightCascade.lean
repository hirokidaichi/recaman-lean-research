import Recaman.CrossBlockReuseUnbounded

namespace Recaman.ExponentialHeightCascade

open Recaman.CrossBlockReuseUnbounded Recaman.SingleWindowEquality Recaman.AdditionRankSlack
open Recaman.ShortPeriodicSupply (sign)

/-! # Exponential-in-`H` recursive actual-`EndN` cascade (`E-786`)

For every height `H ≥ 2` and every rational precision parameter `N : Nat`, we
construct an explicit balanced word `w : List Bool` (`Fw(w) = 0`) confined to the
relative height strip `[0, H + 1]` such that for **every** sign function `f : Nat → Bool`
and **every** arbitrary prehistory length `s : Nat` with `MatchesAt f s w`:

  `12 * 5 ^ H * N * (free f s w.length + exclusiveOldCount f s w.length) ≤`
    `25 * 3 ^ H * (N + 1) * additions f s w.length`.

At `N = 5` (`exponential_actual_endn_lower_bound`):
  `2 * 5 ^ (H - 1) * (free f s w.length + exclusiveOldCount f s w.length) ≤`
    `3 ^ H * additions f s w.length`.

And (`no_subexponential_five_thirds_bound`): for every rational base `P / Q < 5 / 3`
(`3 * P < 5 * Q`) and every constant `C : Nat`, there exists `H ≥ 2` and a balanced
word `w` confined to `[0, H + 1]` satisfying
  `C * P ^ H * (free f s w.length + exclusiveOldCount f s w.length) <`
    `Q ^ H * additions f s w.length`
for every `f` and every arbitrary prehistory length `s`.
-/

/-! ## Word constructors and basic matching helpers -/

def saRep : Nat → List Bool
  | 0 => []
  | m + 1 => [false, true] ++ saRep m

@[simp] theorem saRep_length (m : Nat) : (saRep m).length = 2 * m := by
  induction m with
  | zero => rfl
  | succ m ih => simp [saRep, ih]; omega

def padH (H : Nat) : Nat := if H % 3 = 1 then 2 else 0

def bankWord (H a : Nat) : List Bool :=
  List.replicate (H - 1) true ++ saRep (3 * a) ++ [true] ++ asRep a ++ List.replicate H false

def cycleWord (H : Nat) (B : List Bool) (m a : Nat) : List Bool :=
  asRep (padH H) ++ repeatWord (3 * m) B ++ List.replicate H true ++ asRep a ++ List.replicate H false

def liftWord (H : Nat) (B : List Bool) (m a R : Nat) : List Bool :=
  bankWord H a ++ repeatWord R (cycleWord H B m a)

theorem bankWord_length (H a : Nat) (hH : 2 ≤ H) :
    (bankWord H a).length = 2 * H + 8 * a := by
  unfold bankWord
  simp only [List.length_append, List.length_replicate, saRep_length, asRep_length,
    List.length_singleton]
  omega

theorem cycleWord_length (H : Nat) (B : List Bool) (m a : Nat) :
    (cycleWord H B m a).length = 2 * padH H + 3 * m * B.length + 2 * H + 2 * a := by
  unfold cycleWord
  simp only [List.length_append, List.length_replicate, asRep_length, repeatWord_length]
  omega

theorem liftWord_length (H : Nat) (B : List Bool) (m a R : Nat) (hH : 2 ≤ H) :
    (liftWord H B m a R).length =
      (2 * H + 8 * a) + R * (2 * padH H + 3 * m * B.length + 2 * H + 2 * a) := by
  unfold liftWord
  rw [List.length_append, bankWord_length H a hH, repeatWord_length, cycleWord_length]

private theorem matchesAt_append {f : Nat → Bool} {s : Nat} {u v : List Bool}
    (h : MatchesAt f s (u ++ v)) :
    MatchesAt f s u ∧ MatchesAt f (s + u.length) v := by
  constructor
  · intro i hi
    have h' := h i (by simp; omega)
    have hget : (u ++ v)[i]! = u[i]! := by
      simp [List.getElem!_eq_getElem?_getD, List.getElem?_append_left hi]
    rw [hget] at h'
    exact h'
  · intro i hi
    have h' := h (u.length + i) (by simp; omega)
    have hget : (u ++ v)[u.length + i]! = v[i]! := by
      simp [List.getElem!_eq_getElem?_getD, List.getElem?_append_right (Nat.le_add_right u.length i)]
    rw [hget] at h'
    simpa [Nat.add_assoc] using h'

private theorem matchesAt_replicate {f : Nat → Bool} {s p : Nat} {b : Bool}
    (h : MatchesAt f s (List.replicate p b)) :
    ∀ i, i < p → f (s + i) = b := by
  intro i hi
  have h' := h i (by simp [hi])
  have hget : (List.replicate p b)[i]! = b := by simp [hi]
  rw [hget] at h'
  exact h'

private theorem matchesAt_asRep {f : Nat → Bool} {s m : Nat}
    (h : MatchesAt f s (asRep m)) :
    ∀ i, i < m → f (s + 2 * i) = true ∧ f (s + 2 * i + 1) = false := by
  induction m generalizing s with
  | zero => intro i hi; omega
  | succ m ih =>
      have h' : MatchesAt f s ([true, false] ++ asRep m) := h
      obtain ⟨h1, h2⟩ := matchesAt_append h'
      intro i hi
      cases i with
      | zero =>
          exact ⟨by simpa using h1 0 (by decide), by simpa using h1 1 (by decide)⟩
      | succ i =>
          have ih' := ih h2 i (by omega)
          simpa [show s + 2 + 2 * i = s + 2 * (i + 1) by omega,
                 show s + 2 + 2 * i + 1 = s + 2 * (i + 1) + 1 by omega] using ih'

private theorem matchesAt_saRep {f : Nat → Bool} {s m : Nat}
    (h : MatchesAt f s (saRep m)) :
    ∀ i, i < m → f (s + 2 * i) = false ∧ f (s + 2 * i + 1) = true := by
  induction m generalizing s with
  | zero => intro i hi; omega
  | succ m ih =>
      have h' : MatchesAt f s ([false, true] ++ saRep m) := h
      obtain ⟨h1, h2⟩ := matchesAt_append h'
      intro i hi
      cases i with
      | zero =>
          exact ⟨by simpa using h1 0 (by decide), by simpa using h1 1 (by decide)⟩
      | succ i =>
          have ih' := ih h2 i (by omega)
          simpa [show s + 2 + 2 * i = s + 2 * (i + 1) by omega,
                 show s + 2 + 2 * i + 1 = s + 2 * (i + 1) + 1 by omega] using ih'

private theorem matchesAt_singleton {f : Nat → Bool} {s : Nat} {b : Bool}
    (h : MatchesAt f s [b]) : f s = b := by
  simpa using h 0 (by simp)

/-! ## Walk, area, height confinement, and counting lemmas -/

private theorem fw_ar_allA (f : Nat → Bool) (t : Nat) :
    ∀ p : Nat, (∀ i, i < p → f (t + i) = true) →
      Fw f (t + p) = Fw f t + (p : Int) ∧
      2 * Ar f t p = (p : Int) * ((p : Int) + 1) ∧
      (∀ i, i ≤ p → Fw f (t + i) = Fw f t + (i : Int))
  | 0, _ => by
      refine ⟨by simp, by simp [Ar], ?_⟩
      intro i hi
      have hi0 : i = 0 := by omega
      rw [hi0]; simp
  | p + 1, h => by
      obtain ⟨hF, hA, hB⟩ := fw_ar_allA f t p (fun i hi => h i (by omega))
      have hp : f (t + p) = true := h p (by omega)
      have hFp1 : Fw f (t + (p + 1)) = Fw f t + ((p + 1 : Nat) : Int) := by
        rw [show t + (p + 1) = t + p + 1 from rfl, Fw_succ, hp, hF]
        simp [sign]; omega
      refine ⟨hFp1, ?_, ?_⟩
      · rw [Ar_succ, show t + p + 1 = t + (p + 1) from rfl, hFp1]
        simp only [Int.natCast_add, Int.natCast_one] at hA ⊢
        grind only
      · intro i hi
        by_cases he : i = p + 1
        · rw [he]; exact hFp1
        · exact hB i (by omega)

private theorem fw_ar_allS (f : Nat → Bool) (t : Nat) :
    ∀ p : Nat, (∀ i, i < p → f (t + i) = false) →
      Fw f (t + p) = Fw f t - (p : Int) ∧
      2 * Ar f t p = -((p : Int) * ((p : Int) + 1)) ∧
      (∀ i, i ≤ p → Fw f (t + i) = Fw f t - (i : Int))
  | 0, _ => by
      refine ⟨by simp, by simp [Ar], ?_⟩
      intro i hi
      have hi0 : i = 0 := by omega
      rw [hi0]; simp
  | p + 1, h => by
      obtain ⟨hF, hA, hB⟩ := fw_ar_allS f t p (fun i hi => h i (by omega))
      have hp : f (t + p) = false := h p (by omega)
      have hFp1 : Fw f (t + (p + 1)) = Fw f t - ((p + 1 : Nat) : Int) := by
        rw [show t + (p + 1) = t + p + 1 from rfl, Fw_succ, hp, hF]
        simp [sign]; omega
      refine ⟨hFp1, ?_, ?_⟩
      · rw [Ar_succ, show t + p + 1 = t + (p + 1) from rfl, hFp1]
        simp only [Int.natCast_add, Int.natCast_one] at hA ⊢
        grind only
      · intro i hi
        by_cases he : i = p + 1
        · rw [he]; exact hFp1
        · exact hB i (by omega)

private theorem fw_ar_as (f : Nat → Bool) (t : Nat) :
    ∀ m : Nat, (∀ i, i < m → f (t + 2 * i) = true ∧ f (t + 2 * i + 1) = false) →
      Fw f (t + 2 * m) = Fw f t ∧ Ar f t (2 * m) = (m : Int) ∧
      (∀ i, i ≤ 2 * m → Fw f t ≤ Fw f (t + i) ∧ Fw f (t + i) ≤ Fw f t + 1)
  | 0, _ => by
      refine ⟨by simp, by simp [Ar], ?_⟩
      intro i hi
      have hi0 : i = 0 := by omega
      rw [hi0, Nat.add_zero]; omega
  | m + 1, h => by
      obtain ⟨hF, hA, hB⟩ := fw_ar_as f t m (fun i hi => h i (by omega))
      obtain ⟨ha, hs⟩ := h m (by omega)
      have hF1 : Fw f (t + 2 * m + 1) = Fw f t + 1 := by
        rw [Fw_succ, ha, hF]; simp [sign]
      have hF2 : Fw f (t + 2 * (m + 1)) = Fw f t := by
        rw [show t + 2 * (m + 1) = t + 2 * m + 1 + 1 by omega, Fw_succ, hs, hF1]
        simp [sign]; omega
      refine ⟨hF2, ?_, ?_⟩
      · rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega, Ar_succ, Ar_succ,
            show t + (2 * m + 1) + 1 = t + 2 * (m + 1) by omega, hF1, hF2, hA]
        simp only [Int.natCast_add, Int.natCast_one]
        omega
      · intro i hi
        by_cases h1 : i ≤ 2 * m
        · exact hB i h1
        · by_cases h2 : i = 2 * m + 1
          · rw [h2, show t + (2 * m + 1) = t + 2 * m + 1 by omega, hF1]; omega
          · have h3 : i = 2 * (m + 1) := by omega
            rw [h3, hF2]; omega

private theorem fw_ar_sa (f : Nat → Bool) (t : Nat) :
    ∀ m : Nat, (∀ i, i < m → f (t + 2 * i) = false ∧ f (t + 2 * i + 1) = true) →
      Fw f (t + 2 * m) = Fw f t ∧ Ar f t (2 * m) = -(m : Int) ∧
      (∀ i, i ≤ 2 * m → Fw f t - 1 ≤ Fw f (t + i) ∧ Fw f (t + i) ≤ Fw f t)
  | 0, _ => by
      refine ⟨by simp, by simp [Ar], ?_⟩
      intro i hi
      have hi0 : i = 0 := by omega
      rw [hi0, Nat.add_zero]; omega
  | m + 1, h => by
      obtain ⟨hF, hA, hB⟩ := fw_ar_sa f t m (fun i hi => h i (by omega))
      obtain ⟨hs, ha⟩ := h m (by omega)
      have hF1 : Fw f (t + 2 * m + 1) = Fw f t - 1 := by
        rw [Fw_succ, hs, hF]; simp [sign]; omega
      have hF2 : Fw f (t + 2 * (m + 1)) = Fw f t := by
        rw [show t + 2 * (m + 1) = t + 2 * m + 1 + 1 by omega, Fw_succ, ha, hF1]
        simp [sign]
      refine ⟨hF2, ?_, ?_⟩
      · rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega, Ar_succ, Ar_succ,
            show t + (2 * m + 1) + 1 = t + 2 * (m + 1) by omega, hF1, hF2, hA]
        simp only [Int.natCast_add, Int.natCast_one]
        omega
      · intro i hi
        by_cases h1 : i ≤ 2 * m
        · exact hB i h1
        · by_cases h2 : i = 2 * m + 1
          · rw [h2, show t + (2 * m + 1) = t + 2 * m + 1 by omega, hF1]; omega
          · have h3 : i = 2 * (m + 1) := by omega
            rw [h3, hF2]; omega

private theorem count_allA_additions (f : Nat → Bool) (s : Nat) :
    ∀ p : Nat, (∀ i, i < p → f (s + i) = true) → additions f s p = p
  | 0, _ => rfl
  | p + 1, h => by
      unfold additions
      rw [cN_succ_pos (fun x => f x = true) s p (h p (by omega))]
      have ih := count_allA_additions f s p (fun i hi => h i (by omega))
      unfold additions at ih
      omega

private theorem count_allS_additions (f : Nat → Bool) (s : Nat) :
    ∀ p : Nat, (∀ i, i < p → f (s + i) = false) → additions f s p = 0
  | 0, _ => rfl
  | p + 1, h => by
      unfold additions
      rw [cN_succ_neg (fun x => f x = true) s p (by rw [h p (by omega)]; decide)]
      exact count_allS_additions f s p (fun i hi => h i (by omega))

private theorem count_as_additions (f : Nat → Bool) (s : Nat) :
    ∀ m : Nat, (∀ i, i < m → f (s + 2 * i) = true ∧ f (s + 2 * i + 1) = false) →
      additions f s (2 * m) = m
  | 0, _ => rfl
  | m + 1, h => by
      obtain ⟨ha, hs⟩ := h m (by omega)
      have ih := count_as_additions f s m (fun i hi => h i (by omega))
      unfold additions at ih ⊢
      rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega,
          cN_succ_neg (fun x => f x = true) s (2 * m + 1)
            (by rw [show s + (2 * m + 1) = s + 2 * m + 1 by omega, hs]; decide),
          cN_succ_pos (fun x => f x = true) s (2 * m) ha, ih]

private theorem count_sa_additions (f : Nat → Bool) (s : Nat) :
    ∀ m : Nat, (∀ i, i < m → f (s + 2 * i) = false ∧ f (s + 2 * i + 1) = true) →
      additions f s (2 * m) = m
  | 0, _ => rfl
  | m + 1, h => by
      obtain ⟨hs, ha⟩ := h m (by omega)
      have ih := count_sa_additions f s m (fun i hi => h i (by omega))
      unfold additions at ih ⊢
      rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega,
          cN_succ_pos (fun x => f x = true) s (2 * m + 1)
            (by rw [show s + (2 * m + 1) = s + 2 * m + 1 by omega]; exact ha),
          cN_succ_neg (fun x => f x = true) s (2 * m) (by rw [hs]; decide), ih]

private theorem count_evens_ge (P : Nat → Prop) (s : Nat) :
    ∀ m : Nat, (∀ j, j < m → P (s + 2 * j)) → m ≤ cN P s (2 * m)
  | 0, _ => Nat.zero_le _
  | m + 1, h => by
      have ih := count_evens_ge P s m (fun j hj => h j (by omega))
      have hm := h m (by omega)
      have h1 : cN P s (2 * m + 1) = cN P s (2 * m) + 1 := cN_succ_pos P s (2 * m) hm
      have h2 : cN P s (2 * m + 1) ≤ cN P s ((2 * m + 1) + 1) := by
        by_cases hp : P (s + (2 * m + 1))
        · rw [cN_succ_pos P s (2 * m + 1) hp]; omega
        · rw [cN_succ_neg P s (2 * m + 1) hp]; exact Nat.le_refl _
      rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega]
      omega

private theorem internalSupplied_mono {f : Nat → Bool} {c₁ c₂ q : Nat}
    (hc : c₁ ≤ c₂) (h : InternalSupplied f c₂ q) : InternalSupplied f c₁ q := by
  obtain ⟨ha, u, k, hcu, huk, hw⟩ := h
  exact ⟨ha, u, k, Nat.le_trans hc hcu, huk, hw⟩

private theorem internalSupplied_count_mono (f : Nat → Bool) {c₁ c₂ s len : Nat}
    (hc : c₁ ≤ c₂) :
    cN (InternalSupplied f c₂) s len ≤ cN (InternalSupplied f c₁) s len :=
  cN_mono _ _ s len (fun _ _ _ h => internalSupplied_mono hc h)

private theorem additions_append (f : Nat → Bool) (s l₁ l₂ : Nat) :
    additions f s (l₁ + l₂) = additions f s l₁ + additions f (s + l₁) l₂ :=
  cN_add (fun q => f q = true) s l₁ l₂

private theorem repeat_balanced_props (f : Nat → Bool) (w : List Bool)
    (H A Lint : Nat) (S : Int)
    (hspec : ∀ s', MatchesAt f s' w →
      Fw f (s' + w.length) = Fw f s' ∧
      (∀ i, i ≤ w.length → Fw f s' ≤ Fw f (s' + i) ∧ Fw f (s' + i) ≤ Fw f s' + (H : Int)) ∧
      Ar f s' w.length = S ∧
      additions f s' w.length = A ∧
      Lint ≤ internalSuppliedCount f s' w.length) :
    ∀ R s : Nat, MatchesAt f s (repeatWord R w) →
      Fw f (s + R * w.length) = Fw f s ∧
      (∀ i, i ≤ R * w.length → Fw f s ≤ Fw f (s + i) ∧ Fw f (s + i) ≤ Fw f s + (H : Int)) ∧
      Ar f s (R * w.length) = (R : Int) * S ∧
      additions f s (R * w.length) = R * A ∧
      R * Lint ≤ cN (InternalSupplied f s) s (R * w.length) := by
  intro R
  induction R with
  | zero =>
      intro s _
      refine ⟨by simp, ?_, by simp [Ar], by simp [additions, cN], by simp [cN]⟩
      intro i hi
      have hi0 : i = 0 := by omega
      rw [hi0, Nat.add_zero]; omega
  | succ R ih =>
      intro s hm
      have hm' : MatchesAt f s (w ++ repeatWord R w) := hm
      obtain ⟨h1, h2⟩ := matchesAt_append hm'
      obtain ⟨hF1, hB1, hAr1, hA1, hL1⟩ := hspec s h1
      obtain ⟨hF2, hB2, hAr2, hA2, hL2⟩ := ih (s + w.length) h2
      have hlen : (R + 1) * w.length = w.length + R * w.length := by
        rw [Nat.succ_mul]; omega
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [hlen, ← Nat.add_assoc, hF2, hF1]
      · intro i hi
        rw [hlen] at hi
        by_cases hle : i ≤ w.length
        · exact hB1 i hle
        · have hi2 := hB2 (i - w.length) (by omega)
          rw [show s + w.length + (i - w.length) = s + i by omega, hF1] at hi2
          exact hi2
      · rw [hlen, Ar_add, hAr1, hAr2, hF1]
        simp only [Int.natCast_add, Int.natCast_one]
        grind only
      · rw [hlen, additions_append, hA1, hA2, Nat.succ_mul]
        omega
      · rw [hlen, cN_add]
        have hm2 := internalSupplied_count_mono f (c₁ := s) (c₂ := s + w.length)
          (s := s + w.length) (len := R * w.length) (by omega)
        unfold internalSuppliedCount at hL1
        rw [Nat.succ_mul]
        omega

/-! ## Exact properties of `bankWord H a` -/

private theorem bankWord_props (f : Nat → Bool) (s H a : Nat) (hH : 2 ≤ H)
    (hmatch : MatchesAt f s (bankWord H a)) :
    Fw f (s + (bankWord H a).length) = Fw f s ∧
    (∀ i, i ≤ (bankWord H a).length →
      Fw f s ≤ Fw f (s + i) ∧ Fw f (s + i) ≤ Fw f s + ((H + 1 : Nat) : Int)) ∧
    Ar f s (bankWord H a).length = (H : Int) * (H : Int) + 8 * (a : Int) * ((H : Int) - 1) ∧
    additions f s (bankWord H a).length = H + 4 * a ∧
    (∀ j, j < 3 * a →
      let u := s + (H - 1) + 2 * j
      Fw f u = Fw f s + ((H : Int) - 1) ∧
      2 * Ar f u ((bankWord H a).length - (H - 1 + 2 * j)) =
        2 * ((j : Int) + 1) - (H : Int) * ((H : Int) - 1)) := by
  have hlen := bankWord_length H a hH
  have hmatch' : MatchesAt f s
      (List.replicate (H - 1) true ++
        (saRep (3 * a) ++ ([true] ++ (asRep a ++ List.replicate H false)))) := by
    simpa [bankWord, List.append_assoc] using hmatch
  obtain ⟨h1, hr1⟩ := matchesAt_append hmatch'
  obtain ⟨h2, hr2⟩ := matchesAt_append hr1
  obtain ⟨h3, hr3⟩ := matchesAt_append hr2
  obtain ⟨h4, h5⟩ := matchesAt_append hr3
  simp only [List.length_replicate, saRep_length, List.length_singleton, asRep_length] at hr1 hr2 hr3 h2 h3 h4 h5
  have hA1 := matchesAt_replicate h1
  have hSA := matchesAt_saRep h2
  have hA2 := matchesAt_singleton h3
  have hAS := matchesAt_asRep h4
  have hS := matchesAt_replicate h5
  let s1 := s + (H - 1)
  let s2 := s1 + 2 * (3 * a)
  let s3 := s2 + 1
  let s4 := s3 + 2 * a
  obtain ⟨hF1, hAr1, hB1⟩ := fw_ar_allA f s (H - 1) hA1
  obtain ⟨hF2, hAr2, hB2⟩ := fw_ar_sa f s1 (3 * a) hSA
  have hF3 : Fw f s3 = Fw f s + (H : Int) := by
    dsimp only [s3, s2, s1] at hF2 hA2 ⊢
    rw [Fw_succ, hA2, hF2, hF1]; simp [sign]; omega
  have hAr3 : Ar f s2 1 = 1 := by
    dsimp only [s2, s1] at hA2 ⊢
    simp [Ar, Fw_succ, hA2, sign]; omega
  obtain ⟨hF4, hAr4, hB4⟩ := fw_ar_as f s3 a hAS
  obtain ⟨hF5, hAr5, hB5⟩ := fw_ar_allS f s4 H hS
  have hH1 : ((H - 1 : Nat) : Int) = (H : Int) - 1 := by omega
  have hFw_end : Fw f (s + (bankWord H a).length) = Fw f s := by
    rw [hlen, show s + (2 * H + 8 * a) = s4 + H by dsimp only [s4, s3, s2, s1]; omega]
    rw [hF5, hF4, hF3]; omega
  have hBound : ∀ i, i ≤ (bankWord H a).length →
      Fw f s ≤ Fw f (s + i) ∧ Fw f (s + i) ≤ Fw f s + ((H + 1 : Nat) : Int) := by
    intro i hi
    rw [hlen] at hi
    by_cases c1 : i ≤ H - 1
    · have := hB1 i c1; omega
    · by_cases c2 : i ≤ (H - 1) + 2 * (3 * a)
      · have h := hB2 (i - (H - 1)) (by omega)
        rw [show s1 + (i - (H - 1)) = s + i by dsimp only [s1]; omega, hF1] at h
        omega
      · by_cases c3 : i = (H - 1) + 2 * (3 * a) + 1
        · rw [show s + i = s3 by dsimp only [s3, s2, s1]; omega, hF3]; omega
        · by_cases c4 : i ≤ (H - 1) + 2 * (3 * a) + 1 + 2 * a
          · have h := hB4 (i - ((H - 1) + 2 * (3 * a) + 1)) (by omega)
            rw [show s3 + (i - ((H - 1) + 2 * (3 * a) + 1)) = s + i by dsimp only [s3, s2, s1]; omega,
                hF3] at h
            omega
          · have h := hB5 (i - ((H - 1) + 2 * (3 * a) + 1 + 2 * a)) (by omega)
            rw [show s4 + (i - ((H - 1) + 2 * (3 * a) + 1 + 2 * a)) = s + i by
                  dsimp only [s4, s3, s2, s1]; omega, hF4, hF3] at h
            omega
  -- Exact Ar of bankWord H a
  have hAr_45 : 2 * Ar f s3 (2 * a + H) = 2 * (a : Int) - (H : Int) * ((H : Int) + 1) := by
    have := Ar_add f s3 (2 * a) H
    change Ar f s3 (2 * a + H) = Ar f s3 (2 * a) + Ar f s4 H + (H : Int) * (Fw f s4 - Fw f s3) at this
    rw [hAr4, hF4] at this
    omega
  have hAr_345 : 2 * Ar f s2 (1 + (2 * a + H)) =
      2 + 2 * (a : Int) - (H : Int) * ((H : Int) + 1) + 2 * (2 * (a : Int) + (H : Int)) := by
    have := Ar_add f s2 1 (2 * a + H)
    change Ar f s2 (1 + (2 * a + H)) = Ar f s2 1 + Ar f s3 (2 * a + H) +
      ((2 * a + H : Nat) : Int) * (Fw f s3 - Fw f s2) at this
    have hF32 : Fw f s3 - Fw f s2 = 1 := by rw [hF3, hF2, hF1, hH1]; omega
    rw [hAr3, hF32] at this
    simp only [Int.natCast_add, Int.natCast_mul] at this
    omega
  have hAr_2345 : 2 * Ar f s1 (2 * (3 * a) + (1 + (2 * a + H))) =
      -2 * (3 * (a : Int)) + 2 + 2 * (a : Int) - (H : Int) * ((H : Int) + 1) +
        2 * (2 * (a : Int) + (H : Int)) := by
    have := Ar_add f s1 (2 * (3 * a)) (1 + (2 * a + H))
    change Ar f s1 (2 * (3 * a) + (1 + (2 * a + H))) =
      Ar f s1 (2 * (3 * a)) + Ar f s2 (1 + (2 * a + H)) +
      ((1 + (2 * a + H) : Nat) : Int) * (Fw f s2 - Fw f s1) at this
    rw [hAr2, hF2] at this
    simp only [Int.natCast_mul] at this
    omega
  have hAr_all : Ar f s (bankWord H a).length =
      (H : Int) * (H : Int) + 8 * (a : Int) * ((H : Int) - 1) := by
    have hsplit : (bankWord H a).length = (H - 1) + (2 * (3 * a) + (1 + (2 * a + H))) := by omega
    rw [hsplit]
    have := Ar_add f s (H - 1) (2 * (3 * a) + (1 + (2 * a + H)))
    change Ar f s ((H - 1) + (2 * (3 * a) + (1 + (2 * a + H)))) =
      Ar f s (H - 1) + Ar f s1 (2 * (3 * a) + (1 + (2 * a + H))) +
      ((2 * (3 * a) + (1 + (2 * a + H)) : Nat) : Int) * (Fw f s1 - Fw f s) at this
    rw [hF1, hH1] at this
    rw [hH1] at hAr1
    simp only [Int.natCast_add, Int.natCast_mul, Int.natCast_one] at this
    grind only
  -- Exact additions of bankWord H a
  have hAdd : additions f s (bankWord H a).length = H + 4 * a := by
    have h1c := count_allA_additions f s (H - 1) hA1
    have h2c := count_sa_additions f s1 (3 * a) hSA
    have h3c : additions f s2 1 = 1 := by
      unfold additions
      rw [cN_succ_pos (fun q => f q = true) s2 0 (by simpa using hA2)]
      rfl
    have h4c := count_as_additions f s3 a hAS
    have h5c := count_allS_additions f s4 H hS
    have hsplit : (bankWord H a).length = (H - 1) + (2 * (3 * a) + (1 + (2 * a + H))) := by omega
    rw [hsplit, additions_append, additions_append, additions_append, additions_append]
    change additions f s (H - 1) +
        (additions f s1 (2 * (3 * a)) + (additions f s2 1 +
          (additions f s3 (2 * a) + additions f s4 H))) = H + 4 * a
    omega
  -- Bank peak positions u_j = s1 + 2 * j
  have hPeaks : ∀ j, j < 3 * a →
      let u := s + (H - 1) + 2 * j
      Fw f u = Fw f s + ((H : Int) - 1) ∧
      2 * Ar f u ((bankWord H a).length - (H - 1 + 2 * j)) =
        2 * ((j : Int) + 1) - (H : Int) * ((H : Int) - 1) := by
    intro j hj
    dsimp only
    obtain ⟨hFj, hArj, _⟩ := fw_ar_sa f s1 j (fun i hi => hSA i (by omega))
    have hFu : Fw f (s1 + 2 * j) = Fw f s + ((H : Int) - 1) := by
      rw [hFj, hF1, hH1]
    refine ⟨hFu, ?_⟩
    have hrem : (bankWord H a).length - (H - 1 + 2 * j) =
        2 * (3 * a - j) + (1 + (2 * a + H)) := by omega
    rw [hrem]
    have hSA_rem : ∀ i, i < 3 * a - j →
        f ((s1 + 2 * j) + 2 * i) = false ∧ f ((s1 + 2 * j) + 2 * i + 1) = true := by
      intro i hi
      have hji := hSA (j + i) (by omega)
      dsimp only [s1]
      simpa [show s + (H - 1) + 2 * (j + i) = s + (H - 1) + 2 * j + 2 * i by omega,
             show s + (H - 1) + 2 * (j + i) + 1 = s + (H - 1) + 2 * j + 2 * i + 1 by omega] using hji
    obtain ⟨hFrem, hArrem, _⟩ := fw_ar_sa f (s1 + 2 * j) (3 * a - j) hSA_rem
    have hidx : s1 + 2 * j + 2 * (3 * a - j) = s2 := by dsimp only [s2]; omega
    have hcomb := Ar_add f (s1 + 2 * j) (2 * (3 * a - j)) (1 + (2 * a + H))
    rw [hidx, hArrem] at hcomb
    have hFeq : Fw f s2 = Fw f (s1 + 2 * j) := by rw [← hidx, hFrem]
    rw [hFeq] at hcomb
    have hsub : ((3 * a - j : Nat) : Int) = 3 * (a : Int) - (j : Int) := by omega
    rw [hsub] at hcomb
    grind only
  exact ⟨hFw_end, hBound, hAr_all, hAdd, hPeaks⟩

/-! ## Mod-3 divisibility and exact single-step cascade lift (`liftWord`) -/

private theorem padH_div3 (H : Nat) (hH : 2 ≤ H) :
    3 ∣ padH H * (2 * H - 3) + (H * H - 2 * H) := by
  unfold padH
  have h1 : 2 * H ≤ H * H := by
    have : 2 * H ≤ H * H := Nat.mul_le_mul_right H hH
    exact this
  have h2 : H * H - 2 * H = H * (H - 2) := by
    rw [Nat.mul_sub_left_distrib, Nat.mul_comm H 2]
  rw [h2]
  have hmod : H % 3 = 0 ∨ H % 3 = 1 ∨ H % 3 = 2 := by omega
  rcases hmod with h0 | h1m | h2m
  · rw [if_neg (by omega), Nat.zero_mul, Nat.zero_add]
    exact Nat.dvd_mul_right_of_dvd (Nat.dvd_of_mod_eq_zero h0) _
  · rw [if_pos h1m]
    let u := H / 3 - 1
    have hH_eq : H = 3 * u + 4 := by dsimp only [u]; omega
    have h2H : 2 * H - 3 = 6 * u + 5 := by omega
    have hHm2 : H - 2 = 3 * u + 2 := by omega
    rw [h2H, hHm2, hH_eq]
    refine ⟨3 * u * u + 10 * u + 6, ?_⟩
    grind only
  · rw [if_neg (by omega), Nat.zero_mul, Nat.zero_add]
    exact Nat.dvd_mul_left_of_dvd (Nat.dvd_of_mod_eq_zero (by omega)) _

private theorem cycleWord_props (f : Nat → Bool) (s H : Nat) (B : List Bool)
    (m a A Lint D : Nat) (S : Int) (hH : 2 ≤ H)
    (hD : (D : Int) = ((H : Int) - 1) * (B.length : Int) - S)
    (ha_eq : 3 * a = 3 * m * D + padH H * (2 * H - 3) + (H * H - 2 * H))
    (hBspec : ∀ s', MatchesAt f s' B →
      Fw f (s' + B.length) = Fw f s' ∧
      (∀ i, i ≤ B.length → Fw f s' ≤ Fw f (s' + i) ∧ Fw f (s' + i) ≤ Fw f s' + (H : Int)) ∧
      Ar f s' B.length = S ∧
      additions f s' B.length = A ∧
      Lint ≤ internalSuppliedCount f s' B.length)
    (hmatch : MatchesAt f s (cycleWord H B m a)) :
    Fw f (s + (cycleWord H B m a).length) = Fw f s ∧
    (∀ i, i ≤ (cycleWord H B m a).length →
      Fw f s ≤ Fw f (s + i) ∧ Fw f (s + i) ≤ Fw f s + ((H + 1 : Nat) : Int)) ∧
    Ar f s (cycleWord H B m a).length =
      ((H : Int) - 1) * ((cycleWord H B m a).length : Int) ∧
    additions f s (cycleWord H B m a).length = padH H + 3 * m * A + H + a ∧
    (3 * m * Lint ≤ cN (InternalSupplied f s) (s + 2 * padH H) (3 * m * B.length)) ∧
    (∀ i, i < a →
      let q := s + 2 * padH H + 3 * m * B.length + H + 2 * i
      f q = true ∧
      Fw f q = Fw f s + (H : Int) ∧
      2 * Ar f s (2 * padH H + 3 * m * B.length + H + 2 * i) -
        2 * ((H : Int) - 1) * ((2 * padH H + 3 * m * B.length + H + 2 * i : Nat) : Int) =
        (H : Int) * ((H : Int) - 1) - 6 * ((a : Int) - (i : Int))) := by
  have hlen := cycleWord_length H B m a
  have hmatch' : MatchesAt f s
      (asRep (padH H) ++
        (repeatWord (3 * m) B ++ (List.replicate H true ++ (asRep a ++ List.replicate H false)))) := by
    simpa [cycleWord, List.append_assoc] using hmatch
  obtain ⟨h1, hr1⟩ := matchesAt_append hmatch'
  obtain ⟨h2, hr2⟩ := matchesAt_append hr1
  obtain ⟨h3, hr3⟩ := matchesAt_append hr2
  obtain ⟨h4, h5⟩ := matchesAt_append hr3
  simp only [asRep_length, repeatWord_length, List.length_replicate] at hr1 hr2 hr3 h2 h3 h4 h5
  have hPad := matchesAt_asRep h1
  have hClimb := matchesAt_replicate h3
  have hTop := matchesAt_asRep h4
  have hDesc := matchesAt_replicate h5
  let s1 := s + 2 * padH H
  let s2 := s1 + 3 * m * B.length
  let s3 := s2 + H
  let s4 := s3 + 2 * a
  obtain ⟨hF1, hAr1, hB1⟩ := fw_ar_as f s (padH H) hPad
  obtain ⟨hF2, hB2, hAr2, hA2, hL2⟩ := repeat_balanced_props f B H A Lint S hBspec (3 * m) s1 h2
  obtain ⟨hF3, hAr3, hB3⟩ := fw_ar_allA f s2 H hClimb
  obtain ⟨hF4, hAr4, hB4⟩ := fw_ar_as f s3 a hTop
  obtain ⟨hF5, hAr5, hB5⟩ := fw_ar_allS f s4 H hDesc
  have hH2 : 2 * H ≤ H * H := Nat.mul_le_mul_right H hH
  have h2H3 : 3 ≤ 2 * H := by omega
  have ha_int : 3 * (a : Int) =
      3 * (m : Int) * (D : Int) + (padH H : Int) * (2 * (H : Int) - 3) +
        ((H : Int) * (H : Int) - 2 * (H : Int)) := by
    have hcast : (3 * a : Int) = ((3 * m * D + padH H * (2 * H - 3) + (H * H - 2 * H) : Nat) : Int) := by
      exact_mod_cast ha_eq
    have hs1 : ((2 * H - 3 : Nat) : Int) = 2 * (H : Int) - 3 := by omega
    have hs2 : ((H * H - 2 * H : Nat) : Int) = (H : Int) * (H : Int) - 2 * (H : Int) := by
      have : ((H * H : Nat) : Int) = (H : Int) * (H : Int) := by exact_mod_cast rfl
      omega
    simp only [Int.natCast_add, Int.natCast_mul, hs1, hs2] at hcast
    grind only
  rw [hD] at ha_int
  have hFw_end : Fw f (s + (cycleWord H B m a).length) = Fw f s := by
    rw [hlen, show s + (2 * padH H + 3 * m * B.length + 2 * H + 2 * a) = s4 + H by
      dsimp only [s4, s3, s2, s1]; omega]
    rw [hF5, hF4, hF3, hF2, hF1]; omega
  have hBound : ∀ i, i ≤ (cycleWord H B m a).length →
      Fw f s ≤ Fw f (s + i) ∧ Fw f (s + i) ≤ Fw f s + ((H + 1 : Nat) : Int) := by
    intro i hi
    rw [hlen] at hi
    by_cases c1 : i ≤ 2 * padH H
    · have := hB1 i c1; omega
    · by_cases c2 : i ≤ 2 * padH H + 3 * m * B.length
      · have h := hB2 (i - 2 * padH H) (by omega)
        rw [show s1 + (i - 2 * padH H) = s + i by dsimp only [s1]; omega, hF1] at h
        omega
      · by_cases c3 : i ≤ 2 * padH H + 3 * m * B.length + H
        · have h := hB3 (i - (2 * padH H + 3 * m * B.length)) (by omega)
          rw [show s2 + (i - (2 * padH H + 3 * m * B.length)) = s + i by
                dsimp only [s2, s1]; omega, hF2, hF1] at h
          omega
        · by_cases c4 : i ≤ 2 * padH H + 3 * m * B.length + H + 2 * a
          · have h := hB4 (i - (2 * padH H + 3 * m * B.length + H)) (by omega)
            rw [show s3 + (i - (2 * padH H + 3 * m * B.length + H)) = s + i by
                  dsimp only [s3, s2, s1]; omega, hF3, hF2, hF1] at h
            omega
          · have h := hB5 (i - (2 * padH H + 3 * m * B.length + H + 2 * a)) (by omega)
            rw [show s4 + (i - (2 * padH H + 3 * m * B.length + H + 2 * a)) = s + i by
                  dsimp only [s4, s3, s2, s1]; omega, hF4, hF3, hF2, hF1] at h
            omega
  -- Compute Ar up to s3 and to end of V
  have hAr_12 : Ar f s (2 * padH H + 3 * m * B.length) = (padH H : Int) + 3 * (m : Int) * S := by
    have := Ar_add f s (2 * padH H) (3 * m * B.length)
    change Ar f s (2 * padH H + 3 * m * B.length) =
      Ar f s (2 * padH H) + Ar f s1 (3 * m * B.length) +
        ((3 * m * B.length : Nat) : Int) * (Fw f s1 - Fw f s) at this
    rw [hAr1, hAr2, hF1] at this
    simp only [Int.natCast_mul] at this
    grind only
  have hFs2 : Fw f s2 = Fw f s := by dsimp only [s2]; rw [hF2, hF1]
  have hFs3 : Fw f s3 = Fw f s + (H : Int) := by dsimp only [s3]; rw [hF3, hFs2]
  have hFs4 : Fw f s4 = Fw f s + (H : Int) := by dsimp only [s4]; rw [hF4, hFs3]
  have hAr_123 : 2 * Ar f s (2 * padH H + 3 * m * B.length + H) =
      2 * (padH H : Int) + 6 * (m : Int) * S + (H : Int) * ((H : Int) + 1) := by
    have h := Ar_add f s (2 * padH H + 3 * m * B.length) H
    rw [show s + (2 * padH H + 3 * m * B.length) = s2 by dsimp only [s2, s1]; omega] at h
    rw [hAr_12, hFs2, Int.sub_self, Int.mul_zero, Int.add_zero] at h
    grind only
  have hAr_45 : 2 * Ar f s3 (2 * a + H) = 2 * (a : Int) - (H : Int) * ((H : Int) + 1) := by
    have h := Ar_add f s3 (2 * a) H
    change Ar f s3 (2 * a + H) = Ar f s3 (2 * a) + Ar f s4 H + (H : Int) * (Fw f s4 - Fw f s3) at h
    rw [hAr4, hFs4, hFs3, Int.sub_self, Int.mul_zero, Int.add_zero] at h
    omega
  have hAr_all : Ar f s (cycleWord H B m a).length =
      ((H : Int) - 1) * ((cycleWord H B m a).length : Int) := by
    have hsplit : (cycleWord H B m a).length = (2 * padH H + 3 * m * B.length + H) + (2 * a + H) := by
      omega
    rw [hsplit]
    have h := Ar_add f s (2 * padH H + 3 * m * B.length + H) (2 * a + H)
    rw [show s + (2 * padH H + 3 * m * B.length + H) = s3 by dsimp only [s3, s2, s1]; omega] at h
    rw [hFs3, show Fw f s + (H : Int) - Fw f s = (H : Int) by omega] at h
    have h2eq : 2 * Ar f s ((2 * padH H + 3 * m * B.length + H) + (2 * a + H)) =
        2 * (((H : Int) - 1) * (((2 * padH H + 3 * m * B.length + H) + (2 * a + H) : Nat) : Int)) := by
      simp only [Int.natCast_add, Int.natCast_mul] at h ⊢
      grind only
    omega
  -- Additions count
  have hAdd : additions f s (cycleWord H B m a).length = padH H + 3 * m * A + H + a := by
    have h1c := count_as_additions f s (padH H) hPad
    have h3c := count_allA_additions f s2 H hClimb
    have h4c := count_as_additions f s3 a hTop
    have h5c := count_allS_additions f s4 H hDesc
    have hsplit : (cycleWord H B m a).length =
        2 * padH H + (3 * m * B.length + (H + (2 * a + H))) := by omega
    rw [hsplit, additions_append, additions_append, additions_append, additions_append]
    change additions f s (2 * padH H) +
      (additions f s1 (3 * m * B.length) +
        (additions f s2 H + (additions f s3 (2 * a) + additions f s4 H))) =
      padH H + 3 * m * A + H + a
    omega
  -- Internal supply inside B^{3m}
  have hIntB : 3 * m * Lint ≤ cN (InternalSupplied f s) s1 (3 * m * B.length) :=
    Nat.le_trans hL2 (internalSupplied_count_mono f (c₁ := s) (c₂ := s1) (by dsimp only [s1]; omega))
  -- Target positions inside asRep a
  have hTargets : ∀ i, i < a →
      let q := s + 2 * padH H + 3 * m * B.length + H + 2 * i
      f q = true ∧
      Fw f q = Fw f s + (H : Int) ∧
      2 * Ar f s (2 * padH H + 3 * m * B.length + H + 2 * i) -
        2 * ((H : Int) - 1) * ((2 * padH H + 3 * m * B.length + H + 2 * i : Nat) : Int) =
        (H : Int) * ((H : Int) - 1) - 6 * ((a : Int) - (i : Int)) := by
    intro i hi
    dsimp only
    obtain ⟨hFi, hAri, _⟩ := fw_ar_as f s3 i (fun j hj => hTop j (by omega))
    have hfqi : f (s3 + 2 * i) = true := (hTop i hi).1
    have hFqi : Fw f (s3 + 2 * i) = Fw f s + (H : Int) := by
      rw [hFi, hF3, hF2, hF1]
    refine ⟨hfqi, hFqi, ?_⟩
    have hcomb := Ar_add f s (2 * padH H + 3 * m * B.length + H) (2 * i)
    rw [show s + (2 * padH H + 3 * m * B.length + H) = s3 by dsimp only [s3, s2, s1]; omega] at hcomb
    rw [hAri, hFs3, show Fw f s + (H : Int) - Fw f s = (H : Int) by omega] at hcomb
    simp only [Int.natCast_add, Int.natCast_mul] at hcomb ⊢
    grind only
  exact ⟨hFw_end, hBound, hAr_all, hAdd, hIntB, hTargets⟩

/-- Single recursive cascade lift: given any balanced block `B` confined to `[0, H]`
with `D = (H - 1) * |B| - S > 0`, `liftWord H B m a R` stays in `[0, H + 1]`,
achieves exact `D_{H+1}(B') = 2 * A(B') + H * (H - 2) ≥ 2 * A(B')`, and internally
supplies all `R * a` height-`H` targets plus all `R * 3 * m` embedded copies of `B`. -/
theorem cascade_lift_step (H : Nat) (B : List Bool) (m a R A Lint D : Nat) (S : Int)
    (hH : 2 ≤ H)
    (hD : (D : Int) = ((H : Int) - 1) * (B.length : Int) - S)
    (ha_eq : 3 * a = 3 * m * D + padH H * (2 * H - 3) + (H * H - 2 * H))
    (hBspec : ∀ f s', MatchesAt f s' B →
      Fw f (s' + B.length) = Fw f s' ∧
      (∀ i, i ≤ B.length → Fw f s' ≤ Fw f (s' + i) ∧ Fw f (s' + i) ≤ Fw f s' + (H : Int)) ∧
      Ar f s' B.length = S ∧
      additions f s' B.length = A ∧
      Lint ≤ internalSuppliedCount f s' B.length) :
    ∀ f s, MatchesAt f s (liftWord H B m a R) →
      Fw f (s + (liftWord H B m a R).length) = Fw f s ∧
      (∀ i, i ≤ (liftWord H B m a R).length →
        Fw f s ≤ Fw f (s + i) ∧ Fw f (s + i) ≤ Fw f s + ((H + 1 : Nat) : Int)) ∧
      Ar f s (liftWord H B m a R).length =
        ((H : Int) * (H : Int) + 8 * (a : Int) * ((H : Int) - 1)) +
          (R : Int) * (((H : Int) - 1) * ((cycleWord H B m a).length : Int)) ∧
      additions f s (liftWord H B m a R).length =
        (H + 4 * a) + R * (padH H + 3 * m * A + H + a) ∧
      R * (3 * m * Lint + a) ≤ internalSuppliedCount f s (liftWord H B m a R).length := by
  intro f s hmatch
  have hmatch' : MatchesAt f s (bankWord H a ++ repeatWord R (cycleWord H B m a)) := hmatch
  obtain ⟨hBankM, hRepM⟩ := matchesAt_append hmatch'
  obtain ⟨hFB, hBB, hArB, hAddB, hPeaks⟩ := bankWord_props f s H a hH hBankM
  let sV := s + (bankWord H a).length
  let V := cycleWord H B m a
  have hVspec : ∀ s', MatchesAt f s' V →
      Fw f (s' + V.length) = Fw f s' ∧
      (∀ i, i ≤ V.length → Fw f s' ≤ Fw f (s' + i) ∧ Fw f (s' + i) ≤ Fw f s' + ((H + 1 : Nat) : Int)) ∧
      Ar f s' V.length = ((H : Int) - 1) * (V.length : Int) ∧
      additions f s' V.length = padH H + 3 * m * A + H + a ∧
      0 ≤ internalSuppliedCount f s' V.length := by
    intro s' hmV
    obtain ⟨h1, h2, h3, h4, _, _⟩ := cycleWord_props f s' H B m a A Lint D S hH hD ha_eq (hBspec f) hmV
    exact ⟨h1, h2, h3, h4, Nat.zero_le _⟩
  obtain ⟨hFR, hBR, hArR, hAddR, _⟩ := repeat_balanced_props f V (H + 1)
    (padH H + 3 * m * A + H + a) 0 (((H : Int) - 1) * (V.length : Int)) hVspec R sV hRepM
  have hlen_tot : (liftWord H B m a R).length = (bankWord H a).length + R * V.length := by
    unfold liftWord; rw [List.length_append, repeatWord_length]
  -- Count internal supplies across all R copies of V via induction on r
  have hRepSup : ∀ r, r ≤ R →
      MatchesAt f (sV + (R - r) * V.length) (repeatWord r V) →
      r * (3 * m * Lint + a) ≤
        cN (InternalSupplied f s) (sV + (R - r) * V.length) (r * V.length) := by
    intro r
    induction r with
    | zero => intro _ _; simp [cN]
    | succ r ihr =>
        intro hr hm
        have hm' : MatchesAt f (sV + (R - (r + 1)) * V.length) (V ++ repeatWord r V) := hm
        obtain ⟨hmOne, hmRest⟩ := matchesAt_append hm'
        let k := R - (r + 1)
        let sk := sV + k * V.length
        have hnext : sk + V.length = sV + (R - r) * V.length := by
          dsimp only [sk, k]
          have : R - r = (R - (r + 1)) + 1 := by omega
          rw [this, Nat.succ_mul]; omega
        rw [hnext] at hmRest
        have ih := ihr (by omega) hmRest
        -- Prefix k copies of V from sV to sk have zero Fw and Ar = (H-1) * k * |V|
        have hPrefM : MatchesAt f sV (repeatWord k V) := by
          intro idx hidx
          have h1 := hRepM idx (by simp [repeatWord_length] at hidx ⊢; exact Nat.lt_of_lt_of_le hidx (Nat.mul_le_mul_right _ (by omega)))
          have hget : (repeatWord R V)[idx]! = (repeatWord k V)[idx]! := by
            have hsplitR : repeatWord R V = repeatWord k V ++ repeatWord (R - k) V := by
              have hcat : ∀ a b, repeatWord (a + b) V = repeatWord a V ++ repeatWord b V := by
                intro x y; induction x with
                | zero => simp [repeatWord]
                | succ x ihx =>
                    rw [show x + 1 + y = (x + y) + 1 by omega]
                    simp [repeatWord, ihx, List.append_assoc]
              rw [← hcat k (R - k), show k + (R - k) = R by omega]
            rw [hsplitR]
            simp [List.getElem!_eq_getElem?_getD, List.getElem?_append_left hidx]
          rw [← hget]; exact h1
        obtain ⟨hFk, _, hArk, _, _⟩ := repeat_balanced_props f V (H + 1)
          (padH H + 3 * m * A + H + a) 0 (((H : Int) - 1) * (V.length : Int)) hVspec k sV hPrefM
        obtain ⟨_, _, _, _, hIntBk, hTargsk⟩ :=
          cycleWord_props f sk H B m a A Lint D S hH hD ha_eq (hBspec f) hmOne
        have hFsk : Fw f sk = Fw f s := by dsimp only [sk]; rw [hFk, hFB]
        -- All a targets in asRep a of copy k are supplied by bankWord H a!
        have hSupA : a ≤ cN (InternalSupplied f s) (sk + 2 * padH H + 3 * m * B.length + H) (2 * a) := by
          apply count_evens_ge
          intro i hi
          obtain ⟨hfq, hFq, hArq⟩ := hTargsk i hi
          let j := 3 * (a - i) - 1
          have hj : j < 3 * a := by dsimp only [j]; omega
          obtain ⟨hFu, hAru⟩ := hPeaks j hj
          let u := s + (H - 1) + 2 * j
          let q := sk + 2 * padH H + 3 * m * B.length + H + 2 * i
          have hsu : s ≤ u := by dsimp only [u]; omega
          have huq : u < q := by
            have hbl := bankWord_length H a hH
            dsimp only [u, q, sk, sV]; omega
          refine ⟨hfq, u, q - u, hsu, by omega, ?_, ?_, ?_⟩
          · omega
          · rw [show u + (q - u) = q by omega, hFq, hFsk, hFu]; omega
          · -- Compute Ar f u (q - u) = 0 via Ar_add across u -> sV -> sk -> q
            have h1 := Ar_add f u (sV - u) (q - sV)
            have h2 := Ar_add f sV (k * V.length) (2 * padH H + 3 * m * B.length + H + 2 * i)
            have hqlen : q - u = (sV - u) + (q - sV) := by
              have hbl := bankWord_length H a hH
              dsimp only [u, q, sk, sV]; omega
            have hqV : q - sV = k * V.length + (2 * padH H + 3 * m * B.length + H + 2 * i) := by
              dsimp only [q, sk]; omega
            rw [hqlen, h1, show u + (sV - u) = sV by
              have hbl := bankWord_length H a hH
              dsimp only [u, sV]; omega, hqV, h2]
            have hsu_len : sV - u = (bankWord H a).length - (H - 1 + 2 * j) := by
              dsimp only [sV, u]; omega
            rw [hsu_len]
            have hj_int : ((j : Int) + 1) = 3 * ((a : Int) - (i : Int)) := by
              dsimp only [j]; omega
            have hFsk' : Fw f (sV + k * V.length) = Fw f s := hFsk
            have hAr_sk : Ar f (sV + k * V.length) (2 * padH H + 3 * m * B.length + H + 2 * i) =
                Ar f sk (2 * padH H + 3 * m * B.length + H + 2 * i) := rfl
            rw [hFB, hFu, hArk, hFsk', hAr_sk]
            simp only [Int.natCast_add, Int.natCast_mul]
            grind only
        -- Combine disjoint slices [sk + 2*padH, sk + 2*padH + 3*m*L) and [..., + 2*a) inside copy k
        have hSupOne : 3 * m * Lint + a ≤ cN (InternalSupplied f s) sk V.length := by
          have hVL : V.length = 2 * padH H + (3 * m * B.length + (H + (2 * a + H))) := by
            dsimp only [V]; rw [cycleWord_length]; omega
          rw [hVL, cN_add, cN_add, cN_add, cN_add]
          have hB_s := Nat.le_trans hIntBk (internalSupplied_count_mono f (c₁ := s) (c₂ := sk)
            (by dsimp only [sk, sV]; omega))
          omega
        -- Combine copy k with remaining r copies
        have hlen_r : (r + 1) * V.length = V.length + r * V.length := by
          rw [Nat.succ_mul]; omega
        rw [hlen_r, cN_add]
        have hsk_eq : sV + (R - (r + 1)) * V.length = sk := rfl
        rw [hsk_eq, hnext, Nat.succ_mul]
        omega
  have hSupAll : R * (3 * m * Lint + a) ≤ internalSuppliedCount f s (liftWord H B m a R).length := by
    unfold internalSuppliedCount
    rw [hlen_tot, cN_add]
    have hR := hRepSup R (Nat.le_refl R) (by simpa using hRepM)
    simp only [Nat.sub_self, Nat.zero_mul, Nat.add_zero] at hR
    change R * (3 * m * Lint + a) ≤
      cN (InternalSupplied f s) s (bankWord H a).length +
        cN (InternalSupplied f s) sV (R * V.length)
    omega
  refine ⟨?_, ?_, ?_, ?_, hSupAll⟩
  · rw [hlen_tot, ← Nat.add_assoc]; exact hFR.trans hFB
  · intro i hi
    rw [hlen_tot] at hi
    by_cases c1 : i ≤ (bankWord H a).length
    · exact hBB i c1
    · have h := hBR (i - (bankWord H a).length) (by omega)
      rw [show sV + (i - (bankWord H a).length) = s + i by dsimp only [sV]; omega, hFB] at h
      exact h
  · rw [hlen_tot, Ar_add]
    change Ar f s (bankWord H a).length + Ar f sV (R * V.length) +
      ((R * V.length : Nat) : Int) * (Fw f sV - Fw f s) = _
    rw [hArB, hArR, hFB]
    simp only [Int.sub_self, Int.mul_zero, Int.add_zero]
    rfl
  · rw [hlen_tot, additions_append]
    change additions f s (bankWord H a).length + additions f sV (R * V.length) = _
    rw [hAddB, hAddR]

/-! ## Inductive exponential-in-`H` family (`(12/25 - ε) * (5/3)^H`) -/

private theorem cascade_ratio_step (p5 p3 N X R m A Fub A' Fub' : Nat)
    (hX : X = 4 * N + 3)
    (hPrev : 12 * p5 * X * Fub ≤ 25 * p3 * (X + 1) * A)
    (hXFub' : X * Fub' ≤ R * (3 * X + 2) * m * Fub)
    (hA'_ge : R * (5 * m * A) ≤ A') :
    12 * (5 * p5) * N * Fub' ≤ 25 * (3 * p3) * (N + 1) * A' := by
  have hXpos : 0 < X := by omega
  have hPoly : (3 * X + 2) * (X + 1) * N ≤ 3 * X * X * (N + 1) := by
    rw [hX]; grind only
  have h1 : X * (X * (12 * (5 * p5) * N * Fub')) ≤
      X * (12 * (5 * p5) * N * (R * (3 * X + 2) * m * Fub)) := by
    have hm1 := Nat.mul_le_mul_left (12 * (5 * p5) * N) hXFub'
    have hm2 := Nat.mul_le_mul_left X hm1
    have hl : X * (X * (12 * (5 * p5) * N * Fub')) =
        X * (12 * (5 * p5) * N * (X * Fub')) := by grind only
    rw [hl]; exact hm2
  have h2 : X * (12 * (5 * p5) * N * (R * (3 * X + 2) * m * Fub)) ≤
      5 * R * m * (3 * X + 2) * N * (25 * p3 * (X + 1) * A) := by
    have hl : X * (12 * (5 * p5) * N * (R * (3 * X + 2) * m * Fub)) =
        5 * R * m * (3 * X + 2) * N * (12 * p5 * X * Fub) := by grind only
    rw [hl]; exact Nat.mul_le_mul_left _ hPrev
  have h3 : 5 * R * m * (3 * X + 2) * N * (25 * p3 * (X + 1) * A) ≤
      X * (X * (25 * (3 * p3) * (N + 1) * (R * (5 * m * A)))) := by
    have hl : 5 * R * m * (3 * X + 2) * N * (25 * p3 * (X + 1) * A) =
        (5 * R * m * 25 * p3 * A) * ((3 * X + 2) * (X + 1) * N) := by grind only
    have hr : X * (X * (25 * (3 * p3) * (N + 1) * (R * (5 * m * A)))) =
        (5 * R * m * 25 * p3 * A) * (3 * X * X * (N + 1)) := by grind only
    rw [hl, hr]; exact Nat.mul_le_mul_left _ hPoly
  have h4 : X * (X * (25 * (3 * p3) * (N + 1) * (R * (5 * m * A)))) ≤
      X * (X * (25 * (3 * p3) * (N + 1) * A')) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hA'_ge))
  have hcomb := Nat.le_trans h1 (Nat.le_trans h2 (Nat.le_trans h3 h4))
  exact Nat.le_of_mul_le_mul_left (Nat.le_of_mul_le_mul_left hcomb hXpos) hXpos

private theorem cascade_inductive :
    ∀ (k N : Nat),
      ∃ (w : List Bool) (A Fub D : Nat) (S : Int),
        w.length = 2 * A ∧
        1 ≤ Fub ∧ Fub ≤ A ∧
        (D : Int) = ((k + 2 : Nat) : Int) * (w.length : Int) - S ∧
        2 * A ≤ D ∧
        12 * 5 ^ (k + 2) * N * Fub ≤ 25 * 3 ^ (k + 2) * (N + 1) * A ∧
        (∀ f s, MatchesAt f s w →
          Fw f (s + w.length) = Fw f s ∧
          (∀ i, i ≤ w.length →
            Fw f s ≤ Fw f (s + i) ∧ Fw f (s + i) ≤ Fw f s + ((k + 3 : Nat) : Int)) ∧
          Ar f s w.length = S ∧
          additions f s w.length = A ∧
          A - Fub ≤ internalSuppliedCount f s w.length) := by
  intro k
  induction k with
  | zero =>
      intro N
      let B0 : List Bool := [true, false]
      have hB0 : ∀ f s', MatchesAt f s' B0 →
          Fw f (s' + B0.length) = Fw f s' ∧
          (∀ i, i ≤ B0.length → Fw f s' ≤ Fw f (s' + i) ∧ Fw f (s' + i) ≤ Fw f s' + (2 : Int)) ∧
          Ar f s' B0.length = 1 ∧
          additions f s' B0.length = 1 ∧
          0 ≤ internalSuppliedCount f s' B0.length := by
        intro f s' hm
        have hm' : MatchesAt f s' (asRep 1) := hm
        have hAS := matchesAt_asRep hm'
        obtain ⟨hF, hAr, hB⟩ := fw_ar_as f s' 1 hAS
        have hAdd := count_as_additions f s' 1 hAS
        refine ⟨hF, ?_, hAr, hAdd, Nat.zero_le _⟩
        intro i hi; have := hB i hi; omega
      let m := 2 * (N + 1)
      let a := m
      have hpad2 : padH 2 = 0 := by decide
      have ha_eq : 3 * a = 3 * m * 1 + padH 2 * (2 * 2 - 3) + (2 * 2 - 2 * 2) := by
        rw [hpad2]; dsimp only [a]; omega
      let AV0 := 2 + 4 * a
      let R := 2 * (N + 1) * AV0
      let w := liftWord 2 B0 m a R
      let AV := padH 2 + 3 * m * 1 + 2 + a
      let A' := AV0 + R * AV
      let Fub' := AV0 + R * (padH 2 + 3 * m * 1 + 2)
      let S' : Int := (2 : Int) * 2 + 8 * (a : Int) * ((2 : Int) - 1) +
        (R : Int) * (((2 : Int) - 1) * ((cycleWord 2 B0 m a).length : Int))
      let D' := 2 * A'
      have hVlen : (cycleWord 2 B0 m a).length = 2 * AV := by
        rw [cycleWord_length]; dsimp only [AV, B0]; rw [hpad2]; simp; omega
      have hwlen : w.length = 2 * A' := by
        rw [liftWord_length 2 B0 m a R (by omega)]
        dsimp only [A', AV0, AV, B0]; rw [hpad2]; simp; grind only
      have hD' : (D' : Int) = ((0 + 2 : Nat) : Int) * (w.length : Int) - S' := by
        dsimp only [D', S', A', AV0, AV]
        rw [hwlen, hVlen]
        simp only [Int.natCast_add, Int.natCast_mul]
        grind only
      have hSpec := cascade_lift_step 2 B0 m a R 1 0 1 1 (by omega)
        (by dsimp only [B0]; simp) ha_eq hB0
      have hRatio : 12 * 5 ^ 2 * N * Fub' ≤ 25 * 3 ^ 2 * (N + 1) * A' := by
        have hF : Fub' = (8 * N + 10) + 2 * (N + 1) * (8 * N + 10) * (6 * N + 8) := by
          dsimp only [Fub', AV0, R, a, m]; rw [hpad2]; grind only
        have hA : A' = (8 * N + 10) + 2 * (N + 1) * (8 * N + 10) * (8 * N + 10) := by
          dsimp only [A', AV0, AV, R, a, m]; rw [hpad2]; grind only
        rw [hF, hA]
        grind only
      refine ⟨w, A', Fub', D', S', hwlen, ?_, ?_, hD', Nat.le_refl _, hRatio, ?_⟩
      · dsimp only [Fub', AV0]; omega
      · dsimp only [Fub', A', AV]
        have := Nat.mul_le_mul_left R (show padH 2 + 3 * m * 1 + 2 ≤ padH 2 + 3 * m * 1 + 2 + a by omega)
        omega
      · intro f s hm
        obtain ⟨h1, h2, h3, h4, h5⟩ := hSpec f s hm
        refine ⟨h1, h2, h3, h4, ?_⟩
        have hdiff : A' - Fub' = R * a := by
          dsimp only [A', Fub', AV]
          rw [Nat.add_sub_add_left, ← Nat.mul_sub_left_distrib]
          congr 1; omega
        rw [hdiff]
        simpa using h5
  | succ k ih =>
      intro N
      let X := 4 * N + 3
      obtain ⟨B, A, Fub, D, S, hBlen, hFub_pos, hFub_le, hD_eq, h2A_le_D, hRatio_prev, hBspec⟩ := ih X
      let H := k + 3
      have hH : 2 ≤ H := by dsimp only [H]; omega
      have hH2 : 2 * H ≤ H * H := Nat.mul_le_mul_right H hH
      let cH := padH H
      let m := X * (cH + H)
      have hm_pos : 1 ≤ m := Nat.mul_pos (by dsimp only [X]; omega) (by dsimp only [H]; omega)
      have hdiv := padH_div3 H hH
      let a := (3 * m * D + cH * (2 * H - 3) + (H * H - 2 * H)) / 3
      have ha_eq : 3 * a = 3 * m * D + cH * (2 * H - 3) + (H * H - 2 * H) := by
        obtain ⟨q, hq⟩ := hdiv
        have heq : 3 * m * D + cH * (2 * H - 3) + (H * H - 2 * H) = 3 * (m * D + q) := by
          dsimp only [cH]
          rw [Nat.add_assoc, hq]
          grind only
        dsimp only [a]
        rw [heq, Nat.mul_div_right _ (by decide)]
      have ha_ge : 2 * m * A ≤ a := by
        have h1 : 3 * (2 * m * A) ≤ 3 * m * D := by
          have := Nat.mul_le_mul_left (3 * m) h2A_le_D
          grind only
        omega
      let AV0 := H + 4 * a
      let R := X * AV0
      let w := liftWord H B m a R
      let AV := cH + 3 * m * A + H + a
      let A' := AV0 + R * AV
      let Fub' := AV0 + R * (cH + 3 * m * Fub + H)
      let S' : Int := ((H : Int) * (H : Int) + 8 * (a : Int) * ((H : Int) - 1)) +
        (R : Int) * (((H : Int) - 1) * ((cycleWord H B m a).length : Int))
      let D' := 2 * A' + (H * H - 2 * H)
      have hVlen : (cycleWord H B m a).length = 2 * AV := by
        rw [cycleWord_length, hBlen]
        dsimp only [AV, cH]
        grind only
      have hwlen : w.length = 2 * A' := by
        rw [liftWord_length H B m a R hH, hBlen]
        dsimp only [A', AV0, AV, cH]
        grind only
      have hD' : (D' : Int) = ((k + 1 + 2 : Nat) : Int) * (w.length : Int) - S' := by
        have hHcast : ((k + 1 + 2 : Nat) : Int) = (H : Int) := rfl
        have hsub : ((H * H - 2 * H : Nat) : Int) = (H : Int) * (H : Int) - 2 * (H : Int) := by
          have : ((H * H : Nat) : Int) = (H : Int) * (H : Int) := by exact_mod_cast rfl
          omega
        rw [hHcast]
        dsimp only [D', S', A', AV0, AV]
        rw [hwlen, hVlen]
        simp only [Int.natCast_add, Int.natCast_mul, hsub]
        grind only
      have hD_cast : (D : Int) = ((H : Int) - 1) * (B.length : Int) - S := by
        have : ((k + 2 : Nat) : Int) = (H : Int) - 1 := by dsimp only [H]; omega
        rw [← this]; exact hD_eq
      have hSpec := cascade_lift_step H B m a R A (A - Fub) D S hH hD_cast ha_eq (by
        intro f s' hm
        obtain ⟨h1, h2, h3, h4, h5⟩ := hBspec f s' hm
        exact ⟨h1, h2, h3, h4, h5⟩)
      -- Ratio preservation: 12 * 5^(k+3) * N * Fub' <= 25 * 3^(k+3) * (N+1) * A'
      have hRatio : 12 * 5 ^ (k + 1 + 2) * N * Fub' ≤ 25 * 3 ^ (k + 1 + 2) * (N + 1) * A' := by
        have hAV_ge : 5 * m * A ≤ AV := by
          dsimp only [AV]
          have : 3 * m * A + 2 * m * A = 5 * m * A := by grind only
          omega
        have hA'_ge : R * (5 * m * A) ≤ A' := by
          dsimp only [A']
          have := Nat.mul_le_mul_left R hAV_ge
          omega
        have hXFub' : X * Fub' ≤ R * (3 * X + 2) * m * Fub := by
          have h1 : X * AV0 = R := rfl
          have h2 : X * (cH + H) = m := rfl
          have h3 : 1 ≤ m * Fub := Nat.mul_pos hm_pos hFub_pos
          have h4 : m ≤ m * Fub := Nat.le_mul_of_pos_right m hFub_pos
          have h5 : R * 1 ≤ R * (m * Fub) := Nat.mul_le_mul_left R h3
          have h6 : R * m ≤ R * (m * Fub) := Nat.mul_le_mul_left R h4
          have hexp : X * Fub' = R + R * (X * (3 * m * Fub)) + R * m := by
            dsimp only [Fub']
            have : X * (AV0 + R * (cH + 3 * m * Fub + H)) =
                X * AV0 + R * (X * (3 * m * Fub)) + R * (X * (cH + H)) := by grind only
            rw [this, h1, h2]
          have hrhs : R * (3 * X + 2) * m * Fub =
              R * (m * Fub) + R * (X * (3 * m * Fub)) + R * (m * Fub) := by grind only
          omega
        have hpow5 : 5 ^ (k + 1 + 2) = 5 * 5 ^ (k + 2) := by
          rw [show k + 1 + 2 = (k + 2) + 1 by omega, Nat.pow_succ, Nat.mul_comm]
        have hpow3 : 3 ^ (k + 1 + 2) = 3 * 3 ^ (k + 2) := by
          rw [show k + 1 + 2 = (k + 2) + 1 by omega, Nat.pow_succ, Nat.mul_comm]
        rw [hpow5, hpow3]
        exact cascade_ratio_step (5 ^ (k + 2)) (3 ^ (k + 2)) N X R m A Fub A' Fub' rfl
          hRatio_prev hXFub' hA'_ge
      refine ⟨w, A', Fub', D', S', hwlen, ?_, ?_, hD', ?_, hRatio, ?_⟩
      · dsimp only [Fub', AV0, H]; omega
      · dsimp only [Fub', A', AV]
        have := Nat.mul_le_mul_left (3 * m) hFub_le
        have := Nat.mul_le_mul_left R (show cH + 3 * m * Fub + H ≤ cH + 3 * m * A + H + a by omega)
        omega
      · dsimp only [D']; omega
      · intro f s hm
        obtain ⟨h1, h2, h3, h4, h5⟩ := hSpec f s hm
        refine ⟨h1, h2, h3, h4, ?_⟩
        have hdiff : A' - Fub' = R * (3 * m * (A - Fub) + a) := by
          have h1' : 3 * m * Fub ≤ 3 * m * A := Nat.mul_le_mul_left (3 * m) hFub_le
          have h2' : 3 * m * (A - Fub) = 3 * m * A - 3 * m * Fub := Nat.mul_sub_left_distrib _ _ _
          have h3' : R * (cH + 3 * m * Fub + H) ≤ R * AV :=
            Nat.mul_le_mul_left R (by dsimp only [AV]; omega)
          dsimp only [A', Fub', AV]
          rw [h2']
          have h4' : AV0 + R * (cH + 3 * m * A + H + a) - (AV0 + R * (cH + 3 * m * Fub + H)) =
              R * (cH + 3 * m * A + H + a) - R * (cH + 3 * m * Fub + H) :=
            Nat.add_sub_add_left AV0 _ _
          rw [h4', ← Nat.mul_sub_left_distrib]
          congr 1
          omega
        rw [hdiff]
        exact h5

/-! ## Public exponential-in-`H` lower-bound theorems on actual `EndN` -/

/-- For every height `H ≥ 2` and every rational precision `N : Nat`, there exists a
balanced word `w` confined to relative height strip `[0, H + 1]` attaining
`A / (F + O_c) ≥ (N / (N + 1)) * (12 / 25) * (5 / 3)^H` on actual `EndN` for every
sign function `f` and every arbitrary prehistory length `s`. -/
theorem exponential_cascade_ratio_approx (H N : Nat) (hH : 2 ≤ H) :
    ∃ w : List Bool,
      0 < w.length ∧
      ∀ f s, MatchesAt f s w →
        Fw f (s + w.length) = Fw f s ∧
        (∀ i, i ≤ w.length →
          Fw f s ≤ Fw f (s + i) ∧ Fw f (s + i) ≤ Fw f s + ((H + 1 : Nat) : Int)) ∧
        12 * 5 ^ H * N * (free f s w.length + exclusiveOldCount f s w.length) ≤
          25 * 3 ^ H * (N + 1) * additions f s w.length := by
  obtain ⟨w, A, Fub, _, _, hwlen, hFub_pos, hFub_le, _, _, hRatio, hspec⟩ :=
    cascade_inductive (H - 2) N
  have hH2 : H - 2 + 2 = H := by omega
  have hH3 : H - 2 + 3 = H + 1 := by omega
  rw [hH2] at hRatio
  refine ⟨w, by omega, ?_⟩
  intro f s hm
  obtain ⟨h1, h2, _, hAdd, hInt⟩ := hspec f s hm
  have hpart := additions_partition_after_cut f s w.length
  have hFO : free f s w.length + exclusiveOldCount f s w.length ≤ Fub := by omega
  refine ⟨h1, ?_, ?_⟩
  · intro i hi
    have := h2 i hi
    rw [hH3] at this
    exact this
  · rw [hAdd]
    exact Nat.le_trans (Nat.mul_le_mul_left _ hFO) hRatio

private theorem pow_succ_left (b n : Nat) (hn : 1 ≤ n) : b ^ n = b * b ^ (n - 1) := by
  cases n with
  | zero => omega
  | succ n =>
      rw [Nat.pow_succ, Nat.mul_comm]
      rfl

/-- Unconditional exponential-in-`H` lower bound on actual `EndN`: for every `H ≥ 2`,
there exists a balanced word `w` confined to `[0, H + 1]` such that for every `f` and
every arbitrary prehistory `s`, `2 * 5^(H - 1) * (F + O_c) ≤ 3^H * A`
(i.e. `A / (F + O_c) ≥ (2 / 5) * (5 / 3)^H`). -/
theorem exponential_actual_endn_lower_bound (H : Nat) (hH : 2 ≤ H) :
    ∃ w : List Bool,
      0 < w.length ∧
      ∀ f s, MatchesAt f s w →
        Fw f (s + w.length) = Fw f s ∧
        (∀ i, i ≤ w.length →
          Fw f s ≤ Fw f (s + i) ∧ Fw f (s + i) ≤ Fw f s + ((H + 1 : Nat) : Int)) ∧
        2 * 5 ^ (H - 1) * (free f s w.length + exclusiveOldCount f s w.length) ≤
          3 ^ H * additions f s w.length := by
  obtain ⟨w, hpos, hspec⟩ := exponential_cascade_ratio_approx H 5 hH
  refine ⟨w, hpos, ?_⟩
  intro f s hm
  obtain ⟨h1, h2, h3⟩ := hspec f s hm
  refine ⟨h1, h2, ?_⟩
  rw [pow_succ_left 5 H (by omega)] at h3
  have hl : 12 * (5 * 5 ^ (H - 1)) * 5 * (free f s w.length + exclusiveOldCount f s w.length) =
      150 * (2 * 5 ^ (H - 1) * (free f s w.length + exclusiveOldCount f s w.length)) := by grind only
  have hr : 25 * 3 ^ H * (5 + 1) * additions f s w.length =
      150 * (3 ^ H * additions f s w.length) := by grind only
  rw [hl, hr] at h3
  exact Nat.le_of_mul_le_mul_left h3 (by decide)

private theorem exp_outgrows_linear (a b K : Nat) (hab : a < b) :
    ∃ n : Nat, 2 ≤ n ∧ K * a ^ n < b ^ n := by
  by_cases ha : a = 0
  · refine ⟨2, Nat.le_refl 2, ?_⟩
    subst ha
    have hb : 1 ≤ b := by omega
    have hb2 : 1 ≤ b ^ 2 := Nat.one_le_pow 2 b hb
    have hz : 0 ^ 2 = 0 := rfl
    rw [hz, Nat.mul_zero]
    omega
  · -- Bernoulli: (a + 1)^m ≥ a^m + m * a^(m - 1) for m ≥ 1; at m = K * a + 2, b^m ≥ (a+1)^m > K * a^m
    have ha_pos : 1 ≤ a := by omega
    have hbern : ∀ m : Nat, 1 ≤ m → a ^ m + m * a ^ (m - 1) ≤ (a + 1) ^ m := by
      intro m
      induction m with
      | zero => intro h; omega
      | succ m ih =>
          intro _
          cases m with
          | zero => simp
          | succ m =>
              have h1 := ih (by omega)
              rw [Nat.pow_succ (a + 1) (m + 1), Nat.mul_add, Nat.mul_one]
              have h2 := Nat.mul_le_mul_right a h1
              have h3 : a ^ (m + 1) ≤ (a + 1) ^ (m + 1) := Nat.pow_le_pow_left (by omega) _
              have hpow : a ^ (m + 1 + 1) = a ^ (m + 1) * a := Nat.pow_succ a (m + 1)
              have hpow2 : a ^ (m + 1) = a ^ m * a := Nat.pow_succ a m
              rw [hpow, show m + 1 + 1 - 1 = m + 1 by omega]
              have h2' : a ^ (m + 1) * a + (m + 1) * a ^ (m + 1) ≤ (a + 1) ^ (m + 1) * a := by
                have hexp : (a ^ (m + 1) + (m + 1) * a ^ (m + 1 - 1)) * a =
                    a ^ (m + 1) * a + (m + 1) * (a ^ m * a) := by
                  rw [show m + 1 - 1 = m by omega]; grind only
                rw [hexp, ← hpow2] at h2
                exact h2
              have h4 : (m + 1 + 1) * a ^ (m + 1) = (m + 1) * a ^ (m + 1) + a ^ (m + 1) := by
                grind only
              omega
    let n := K * a + 2
    refine ⟨n, by dsimp only [n]; omega, ?_⟩
    have hstep1 := hbern n (by dsimp only [n]; omega)
    have hstep2 : (a + 1) ^ n ≤ b ^ n := Nat.pow_le_pow_left (by omega) n
    have hpow_n : a ^ n = a ^ (n - 1) * a := by
      rw [pow_succ_left a n (by dsimp only [n]; omega), Nat.mul_comm]
    have hap : 0 < a ^ (n - 1) := Nat.pow_pos ha_pos
    have hgt : K * a ^ n < n * a ^ (n - 1) := by
      rw [hpow_n]
      have hl : K * (a ^ (n - 1) * a) = (K * a) * a ^ (n - 1) := by grind only
      rw [hl]
      exact Nat.mul_lt_mul_of_pos_right (by dsimp only [n]; omega) hap
    omega

/-- No sub-`(5/3)^H` exponential bound (and in particular no polynomial-in-`H` bound)
holds on actual `EndN`: for every rational base `P / Q < 5 / 3` (`3 * P < 5 * Q`)
and every constant `C : Nat`, there exists `H ≥ 2` and a balanced word `w` confined
to `[0, H + 1]` breaking `C * (P / Q)^H` for every `f` and every arbitrary prehistory `s`. -/
theorem no_subexponential_five_thirds_bound (P Q C : Nat) (hPQ : 3 * P < 5 * Q) :
    ∃ (H : Nat) (w : List Bool),
      2 ≤ H ∧ 0 < w.length ∧
      ∀ f s, MatchesAt f s w →
        Fw f (s + w.length) = Fw f s ∧
        (∀ i, i ≤ w.length →
          Fw f s ≤ Fw f (s + i) ∧ Fw f (s + i) ≤ Fw f s + ((H + 1 : Nat) : Int)) ∧
        C * P ^ H * (free f s w.length + exclusiveOldCount f s w.length) <
          Q ^ H * additions f s w.length := by
  obtain ⟨H, hH, hgrow⟩ := exp_outgrows_linear (3 * P) (5 * Q) (5 * C + 5) hPQ
  obtain ⟨w, hpos, hspec⟩ := exponential_actual_endn_lower_bound H hH
  refine ⟨H, w, hH, hpos, ?_⟩
  intro f s hm
  obtain ⟨h1, h2, h3⟩ := hspec f s hm
  refine ⟨h1, h2, ?_⟩
  -- Since 0 < w.length and w is balanced, additions f s w.length > 0!
  have hAdd_pos : 0 < additions f s w.length := by
    by_cases hz : 0 < additions f s w.length
    · exact hz
    · exfalso
      have hzero : additions f s w.length = 0 := by omega
      have hallS : ∀ i, i < w.length → f (s + i) = false := by
        intro i hi
        by_cases hf : f (s + i) = true
        · have hsplit1 := additions_append f s i (w.length - i)
          rw [show i + (w.length - i) = w.length by omega] at hsplit1
          have hsplit2 := additions_append f (s + i) 1 (w.length - i - 1)
          rw [show 1 + (w.length - i - 1) = w.length - i by omega] at hsplit2
          have h1add : additions f (s + i) 1 = 1 := by
            unfold additions
            rw [cN_succ_pos (fun q => f q = true) (s + i) 0 (by simpa using hf)]
            rfl
          omega
        · cases h : f (s + i)
          · rfl
          · exact (hf h).elim
      obtain ⟨hFs, _, _⟩ := fw_ar_allS f s w.length hallS
      omega
  have hQ_pos : 0 < Q := by omega
  have hQH_pos : 0 < Q ^ H := Nat.pow_pos hQ_pos
  by_cases hFO : free f s w.length + exclusiveOldCount f s w.length = 0
  · rw [hFO, Nat.mul_zero]
    exact Nat.mul_pos hQH_pos hAdd_pos
  · have hFO_pos : 0 < free f s w.length + exclusiveOldCount f s w.length := by omega
    have hpow5 : 5 ^ H = 5 * 5 ^ (H - 1) := pow_succ_left 5 H (by omega)
    have hpow3P : (3 * P) ^ H = 3 ^ H * P ^ H := Nat.mul_pow 3 P H
    have hpow5Q : (5 * Q) ^ H = 5 ^ H * Q ^ H := Nat.mul_pow 5 Q H
    rw [hpow3P, hpow5Q, hpow5] at hgrow
    -- From hgrow: (5 * C + 5) * (3^H * P^H) < 5 * 5^(H-1) * Q^H
    -- Hence C * 3^H * P^H < 5^(H-1) * Q^H < 2 * 5^(H-1) * Q^H!
    have hstrict : C * 3 ^ H * P ^ H < 2 * 5 ^ (H - 1) * Q ^ H := by
      have : 5 * (C * 3 ^ H * P ^ H) < 5 * (5 ^ (H - 1) * Q ^ H) := by grind only
      have hlt : C * 3 ^ H * P ^ H < 5 ^ (H - 1) * Q ^ H := Nat.lt_of_mul_lt_mul_left this
      have h2eq : 2 * 5 ^ (H - 1) * Q ^ H = 5 ^ (H - 1) * Q ^ H + 5 ^ (H - 1) * Q ^ H := by
        grind only
      omega
    have hm1 := Nat.mul_lt_mul_of_pos_right hstrict hFO_pos
    have hm2 := Nat.mul_le_mul_left (Q ^ H) h3
    have hl : C * 3 ^ H * P ^ H * (free f s w.length + exclusiveOldCount f s w.length) =
        3 ^ H * (C * P ^ H * (free f s w.length + exclusiveOldCount f s w.length)) := by grind only
    have hm_mid : 2 * 5 ^ (H - 1) * Q ^ H * (free f s w.length + exclusiveOldCount f s w.length) =
        Q ^ H * (2 * 5 ^ (H - 1) * (free f s w.length + exclusiveOldCount f s w.length)) := by grind only
    have hr : Q ^ H * (3 ^ H * additions f s w.length) =
        3 ^ H * (Q ^ H * additions f s w.length) := by grind only
    rw [hl, hm_mid] at hm1
    rw [hr] at hm2
    exact Nat.lt_of_mul_lt_mul_left (Nat.lt_of_lt_of_le hm1 hm2)

end Recaman.ExponentialHeightCascade

