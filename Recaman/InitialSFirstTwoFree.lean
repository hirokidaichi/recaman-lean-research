import Recaman.BlockSuffixPositivity

namespace Recaman.InitialSFirstTwoFree

open Recaman.BlockSuffixPositivity Recaman.SingleWindowEquality
open Recaman.ShortPeriodicSupply (sign)

/-! The first two additions after an initial subtraction block are original
free positions. Every later original supply therefore sits strictly after
two free additions. This pays the earliest exclusive height-two target and
does not inject the later ones. -/

private theorem fw_all_S (f : Nat → Bool) (n : Nat)
    (h : ∀ i, i < n → f i = false) : Fw f n = -((n : Nat) : Int) := by
  have hrun := fw_false_run f 0 n (fun i _ hi => h i (by omega))
  simp only [Nat.zero_add] at hrun
  rw [show Fw f 0 = 0 from rfl] at hrun
  have hneg : (0 : Int) - ((n : Nat) : Int) = -((n : Nat) : Int) := by omega
  simpa [hneg] using hrun

theorem cN_zero_of (P : Nat → Prop) :
    ∀ n, (∀ i, i < n → ¬ P i) → cN P 0 n = 0
  | 0, _ => rfl
  | n+1, h => by
      have hn : ¬ P (0 + n) := by simpa using h n (by omega)
      rw [cN_succ_neg P 0 n hn]
      exact cN_zero_of P n (fun i hi => h i (by omega))

theorem cN_two_points (P : Nat → Prop) (a b n : Nat)
    (hab : a < b) (hbn : b < n) (ha : P a) (hb : P b) :
    2 ≤ cN P 0 n := by
  have ha0 : P (0 + a) := by simpa using ha
  have hleft : cN P 0 (a + 1) = cN P 0 a + 1 := cN_succ_pos P 0 a ha0
  have hsplit0 := cN_add (P := P) (s := 0) (a + 1) (n - (a + 1))
  have hn : a + 1 + (n - (a + 1)) = n := by omega
  have hsplit : cN P 0 n = cN P 0 (a + 1) + cN P (a + 1) (n - (a + 1)) := by
    simpa [hn, Nat.zero_add] using hsplit0
  have hbindex : (a + 1) + (b - (a + 1)) = b := by omega
  have hb0 : P ((a + 1) + (b - (a + 1))) := by simpa [hbindex] using hb
  have hstep : cN P (a + 1) ((b - (a + 1)) + 1) =
      cN P (a + 1) (b - (a + 1)) + 1 :=
    cN_succ_pos P (a + 1) (b - (a + 1)) hb0
  have hba : b - a = b - (a + 1) + 1 := by omega
  have hpad0 := cN_add (P := P) (s := a + 1) (b - a) (n - (a + 1) - (b - a))
  have hlen : b - a + (n - (a + 1) - (b - a)) = n - (a + 1) := by omega
  have htail : 1 ≤ cN P (a + 1) (n - (a + 1)) := by
    rw [← hlen, hpad0, hba, hstep]
    omega
  rw [hsplit, hleft]
  omega

/-- Least addition at or before a known addition. -/
theorem least_addition (f : Nat → Bool) :
    ∀ q, f q = true → ∃ p, p ≤ q ∧ f p = true ∧ ∀ i, i < p → f i = false
  | 0, h => ⟨0, Nat.le_refl _, h, fun i hi => (Nat.not_lt_zero i hi).elim⟩
  | q+1, h => by
    by_cases h0 : f 0 = true
    · exact ⟨0, Nat.zero_le _, h0, fun i hi => (Nat.not_lt_zero i hi).elim⟩
    · by_cases hex : ∃ i, i ≤ q ∧ f i = true
      · obtain ⟨i, hi, ht⟩ := hex
        obtain ⟨p, hp, hpt, hmin⟩ := least_addition f i ht
        exact ⟨p, Nat.le_trans hp (Nat.le_trans hi (Nat.le_succ _)), hpt, hmin⟩
      · exact ⟨q+1, Nat.le_refl _, h, fun i hi => by
          have hiq : i ≤ q := Nat.le_of_lt_succ hi
          have hf : f i = false := by
            cases hfi : f i with
            | false => rfl
            | true => exact (hex ⟨i, hiq, hfi⟩).elim
          exact hf⟩

/-- The earliest addition has no original window. -/
theorem initial_S_first_addition_free (f : Nat → Bool) (p : Nat)
    (_hA : f p = true) (hearlier : ∀ i, i < p → f i = false) :
    ¬ EndN f 0 p := by
  intro he
  obtain ⟨_, t, k, _, htk, _hk0, hF, hAr⟩ := he
  have hFw : Fw f p = -((p : Nat) : Int) := fw_all_S f p hearlier
  have hFwT : Fw f t = -((t : Nat) : Int) :=
    fw_all_S f t (fun i hi => hearlier i (by omega))
  have hRise : Fw f p = Fw f t + 1 := by simpa [htk] using hF
  have htEq : t = p-1 := by
    rw [hFw, hFwT] at hRise
    omega
  have hk : k = 1 := by omega
  have hAr' : Ar f (p-1) 1 = 0 := by simpa [hk, htEq] using hAr
  have hArea : Ar f (p-1) 1 = Fw f p - Fw f (p-1) := by
    have hp1 : (p-1)+1 = p := by omega
    simp [Ar, hp1]
  have hPrev : Fw f (p-1) = -(((p-1 : Nat) : Int)) :=
    fw_all_S f (p-1) (fun i hi => hearlier i (by omega))
  rw [hArea, hFw, hPrev] at hAr'
  omega

/-- The second addition is free. After the first addition, a pure subtraction
run never reaches the source height of a window. -/
theorem initial_S_second_addition_free (f : Nat → Bool) (p r : Nat)
    (hpr : p < r) (hpA : f p = true) (_hrA : f r = true)
    (hbeforeP : ∀ i, i < p → f i = false)
    (hbetween : ∀ i, p < i → i < r → f i = false) :
    ¬ EndN f 0 r := by
  intro he
  obtain ⟨_, t, k, _, htk, _hk0, hF, hAr⟩ := he
  have hFwp : Fw f p = -((p : Nat) : Int) := fw_all_S f p hbeforeP
  have hStep : Fw f (p+1) = Fw f p + 1 := by
    rw [Fw_succ, hpA]
    simp [sign]
  let gap : Nat := r-p-1
  have hgap : p+1+gap = r := by dsimp [gap]; omega
  have hFwR : Fw f r = Fw f (p+1) - (gap : Int) := by
    have hrun := fw_false_run f (p+1) gap (fun i hi hir => by
      exact hbetween i (by omega) (by omega))
    simpa [hgap] using hrun
  have hSrc : Fw f r = Fw f t + 1 := by simpa [htk] using hF
  have hSigma : Fw f t = -((p : Nat) : Int) - (gap : Int) := by
    rw [hFwR, hStep, hFwp] at hSrc
    omega
  by_cases hgap0 : gap = 0
  · have hArea : Ar f p 1 = Fw f (p+1) - Fw f p := by simp [Ar]
    have hFwt : Fw f t = -((t : Nat) : Int) :=
      fw_all_S f t (fun i hi => hbeforeP i (by omega))
    have htP : t = p := by
      rw [hFwt, hgap0] at hSigma
      omega
    have hr1 : r = p+1 := by dsimp [gap] at hgap0; omega
    have hk1 : k = 1 := by omega
    have hAr' : Ar f p 1 = 0 := by simpa [hk1, htP] using hAr
    rw [hArea, hStep] at hAr'
    omega
  · have hnone : Fw f t ≠ -((p : Nat) : Int) - (gap : Int) := by
      by_cases htp : t ≤ p
      · rw [fw_all_S f t (fun i hi => hbeforeP i (by omega))]
        omega
      · have hrun := fw_false_run f (p+1) (t-(p+1)) (fun i hi hir =>
          hbetween i (by omega) (by omega))
        have htidx : p+1+(t-(p+1)) = t := by omega
        rw [htidx] at hrun
        have hFw1 : Fw f (p+1) = 1 - ((p : Nat) : Int) := by rw [hStep, hFwp]; omega
        rw [hrun, hFw1]
        omega
    exact hnone hSigma

/-- Least addition strictly after `p`, given a later addition. -/
theorem least_after (f : Nat → Bool) :
    ∀ d p, f (p + 1 + d) = true →
      ∃ r, p < r ∧ r ≤ p + 1 + d ∧ f r = true ∧ ∀ i, p < i → i < r → f i = false
  | 0, p, h => ⟨p + 1, by omega, Nat.le_refl _, by simpa using h, fun i _ hir => by omega⟩
  | d+1, p, h => by
    by_cases h1 : f (p + 1) = true
    · exact ⟨p + 1, by omega, by omega, h1, fun i _ hir => by omega⟩
    · have hshift : f ((p + 1) + 1 + d) = true := by
        have : p + 1 + (d + 1) = (p + 1) + 1 + d := by omega
        simpa [this] using h
      obtain ⟨r, hpr, hr, hrA, hmin⟩ := least_after f d (p + 1) hshift
      refine ⟨r, by omega, by omega, hrA, ?_⟩
      intro i hip hir
      cases Nat.lt_or_ge (p + 1) i with
      | inl hi => exact hmin i hi hir
      | inr hge =>
        have hiEq : i = p + 1 := by omega
        cases hfi : f i with
        | false => rfl
        | true =>
          subst hiEq
          exact (h1 hfi).elim

/-- Any original supply is strictly later than two original free additions. -/
theorem supplied_addition_has_two_free (f : Nat → Bool) (h q : Nat)
    (hS : ∀ i, i < h → f i = false) (_hh : 0 < h) (he : EndN f 0 q) :
    2 ≤ cN (fun i => f i = true ∧ ¬ EndN f 0 i) 0 q := by
  have hA : f q = true := he.1
  have hqh : h ≤ q := by
    cases Nat.lt_or_ge q h with
    | inl hlt =>
      have hf := hS q hlt
      rw [hf] at hA
      cases hA
    | inr hge => exact hge
  obtain ⟨p, _hpq0, hpA, hbefore⟩ := least_addition f q hA
  have hph : h ≤ p := by
    cases Nat.lt_or_ge p h with
    | inl hlt =>
      have hf := hS p hlt
      rw [hf] at hpA
      cases hpA
    | inr hge => exact hge
  have hpFree : ¬ EndN f 0 p := initial_S_first_addition_free f p hpA hbefore
  have hpq : p < q := by
    have hle : p ≤ q := _hpq0
    cases Nat.eq_or_lt_of_le hle with
    | inl heq => exact absurd (heq.symm ▸ he) hpFree
    | inr hlt => exact hlt
  have hdist : p + 1 + (q - p - 1) = q := by omega
  have hAt : f (p + 1 + (q - p - 1)) = true := by simpa [hdist] using hA
  obtain ⟨r, hpr, hrq0, hrA, hbetween⟩ := least_after f (q - p - 1) p hAt
  have hrFree : ¬ EndN f 0 r :=
    initial_S_second_addition_free f p r hpr hpA hrA hbefore hbetween
  have hrq0' : r ≤ q := by simpa [hdist] using hrq0
  have hrq : r < q := by
    cases Nat.eq_or_lt_of_le hrq0' with
    | inl heq => exact absurd (heq.symm ▸ he) hrFree
    | inr hlt => exact hlt
  exact cN_two_points (fun i => f i = true ∧ ¬ EndN f 0 i) p r q
    hpr hrq ⟨hpA, hpFree⟩ ⟨hrA, hrFree⟩

end Recaman.InitialSFirstTwoFree
