import Recaman.ShortPeriodicSupply
import Recaman.LagElevenSupply

namespace Recaman.LagElevenPeriodic

/-! # Periodic glue of the lag-11 injection

The E-079 kernel classifies min-lag-11 windows. This module recovers those
windows from an arbitrary periodic sign stream and proves
`|U7 ∪ U11min| ≤ |D|`. No Recamán freshness or reachability is used.
-/

open Recaman.ShortPeriodicSupply
open Recaman.LagElevenSupply

def maskAux (e : Int → Bool) (t : Int) : Nat → Nat
  | 0 => 0
  | n + 1 =>
      if e (t - ((n + 1 : Nat) : Int)) then maskAux e t n
      else maskAux e t n ||| (1 <<< n)

def maskAt (e : Int → Bool) (t : Int) : Nat := maskAux e t 11

theorem maskAux_testBit_ge (e : Int → Bool) (t : Int) :
    ∀ n i, n ≤ i → (maskAux e t n).testBit i = false := by
  intro n
  induction n with
  | zero =>
    intro i hi
    simp [maskAux]
  | succ n ih =>
    intro i hi
    simp only [maskAux]
    have hprev : (maskAux e t n).testBit i = false := ih i (Nat.le_of_succ_le hi)
    have hne : n ≠ i := Nat.ne_of_lt (Nat.lt_of_succ_le hi)
    have hpow : (1 <<< n).testBit i = false := by
      rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow]
      exact decide_eq_false hne
    by_cases he : e (t - ((n + 1 : Nat) : Int))
    · rw [if_pos he]; exact hprev
    · rw [if_neg he, Nat.testBit_or, hprev, hpow]; rfl

theorem maskAux_testBit (e : Int → Bool) (t : Int) :
    ∀ n i, i < n → (maskAux e t n).testBit i = !e (t - ((i + 1 : Nat) : Int)) := by
  intro n
  induction n with
  | zero =>
    intro i hi
    cases hi
  | succ n ih =>
    intro i hi
    simp only [maskAux]
    have hlt : i ≤ n := Nat.le_of_lt_succ hi
    by_cases hieq : i = n
    · subst i
      have hn1 : ((n + 1 : Nat) : Int) = (n : Int) + 1 := by omega
      have hprev : (maskAux e t n).testBit n = false :=
        maskAux_testBit_ge e t n n (Nat.le_refl n)
      have hpow : (1 <<< n).testBit n = true := by
        rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow]
        simp
      rw [hn1]
      by_cases he : e (t - ((n : Int) + 1))
      · simp [he, hprev]
      · simp [he, Nat.testBit_or, hprev, hpow]
    · have hltn : i < n := Nat.lt_of_le_of_ne hlt hieq
      have hprev := ih i hltn
      have hne : n ≠ i := Ne.symm (Nat.ne_of_lt hltn)
      have hpow : (1 <<< n).testBit i = false := by
        rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow]
        exact decide_eq_false hne
      by_cases he : e (t - ((n + 1 : Nat) : Int))
      · rw [if_pos he]; exact hprev
      · rw [if_neg he, Nat.testBit_or, hprev, hpow]; simp

theorem maskAt_testBit (e : Int → Bool) (t : Int) (i : Nat) (hi : i < 11) :
    (maskAt e t).testBit i = !e (t - ((i + 1 : Nat) : Int)) :=
  maskAux_testBit e t 11 i hi

theorem maskAt_lt (e : Int → Bool) (t : Int) : maskAt e t < 2048 := by
  change maskAt e t < 2 ^ 11
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  exact maskAux_testBit_ge e t 11 i hi

theorem isS_maskAt (e : Int → Bool) (t : Int) (k : Nat) (hk : 1 ≤ k) (hk11 : k ≤ 11) :
    isS (maskAt e t) k = !e (t - (k : Int)) := by
  have : k - 1 < 11 := by omega
  have hb := maskAt_testBit e t (k - 1) this
  have hk1 : ((k - 1 + 1 : Nat) : Int) = (k : Int) := by omega
  unfold isS
  simpa [hk1] using hb

theorem p2At_iff_P2 (e : Int → Bool) (t : Int) (d : Nat) (hd : d ≤ 11) :
    p2At (maskAt e t) d = true ↔ P2 e t d := by
  unfold p2At P2
  simp only [decide_eq_true_eq]
  have hmap :
      ((List.range d).map fun i => (if isS (maskAt e t) (i + 1) then (-1 : Int) else 1)) =
        (List.range d).map fun i => sign (e (t - ((i + 1 : Nat) : Int))) := by
    apply List.map_congr_left
    intro i hi
    have hi' := List.mem_range.mp hi
    have hs := isS_maskAt e t (i + 1) (by omega) (by omega)
    rw [hs, sign]
    cases he : e (t - ((i + 1 : Nat) : Int)) <;> simp [he]
  have hmom :
      ((List.range d).map fun i =>
          ((i + 1 : Nat) : Int) * (if isS (maskAt e t) (i + 1) then (-1 : Int) else 1)) =
        (List.range d).map fun i =>
          ((i + 1 : Nat) : Int) * sign (e (t - ((i + 1 : Nat) : Int))) := by
    apply List.map_congr_left
    intro i hi
    have hi' := List.mem_range.mp hi
    have hs := isS_maskAt e t (i + 1) (by omega) (by omega)
    rw [hs, sign]
    cases he : e (t - ((i + 1 : Nat) : Int)) <;> simp [he]
  constructor
  · intro h
    rw [← hmap, ← hmom]
    exact h
  · intro h
    rw [hmap, hmom]
    exact h

def minLag11At (e : Int → Bool) (t : Int) : Prop :=
  P2 e t 11 ∧ ¬ P2 e t 3 ∧ ¬ P2 e t 7

theorem minLag11_eq_true_iff (m : Nat) :
    minLag11 m = true ↔ p2At m 11 = true ∧ p2At m 3 = false ∧ p2At m 7 = false := by
  simp only [minLag11]
  cases p2At m 11 <;> cases p2At m 3 <;> cases p2At m 7 <;> simp

theorem minLag11At_iff (e : Int → Bool) (t : Int) :
    minLag11 (maskAt e t) = true ↔ minLag11At e t := by
  constructor
  · intro h
    have ⟨h11, h3, h7⟩ := (minLag11_eq_true_iff (maskAt e t)).mp h
    exact ⟨(p2At_iff_P2 e t 11 (by decide)).mp h11,
      fun hP => (Bool.eq_false_iff.mp h3) ((p2At_iff_P2 e t 3 (by decide)).mpr hP),
      fun hP => (Bool.eq_false_iff.mp h7) ((p2At_iff_P2 e t 7 (by decide)).mpr hP)⟩
  · intro h
    apply (minLag11_eq_true_iff (maskAt e t)).mpr
    exact ⟨(p2At_iff_P2 e t 11 (by decide)).mpr h.1,
      Bool.eq_false_iff.mpr (mt (p2At_iff_P2 e t 3 (by decide)).mp h.2.1),
      Bool.eq_false_iff.mpr (mt (p2At_iff_P2 e t 7 (by decide)).mp h.2.2)⟩

theorem typeOf_spec (m : Nat) (hm : m < 2048) (h : minLag11 m = true) :
    typeOf m ∈ types ∧ maskOf (typeOf m) = m := by
  have hall := List.all_eq_true.mp types_complete
  have hm' : m ∈ List.range 2048 := List.mem_range.mpr hm
  have hany : types.any (fun offs => maskOf offs == m) = true := by
    have hpred := hall m hm'
    simpa [h] using hpred
  cases hfind : types.find? (fun offs => maskOf offs == m) with
  | none =>
    have hx := (List.find?_eq_none.mp hfind)
    obtain ⟨offs, hmem, heq⟩ := List.any_eq_true.mp hany
    have := hx offs hmem
    simp at heq
    simp [heq] at this
  | some offs =>
    have hmem := List.mem_of_find?_eq_some hfind
    have hp := List.find?_some hfind
    simp [typeOf, hfind]
    exact ⟨hmem, by simpa using hp⟩

theorem contains_iff_isS (offs : List Nat) (h : offs ∈ types) (i : Nat) (hi : i < 11) :
    offs.contains (i + 1) = isS (maskOf offs) (i + 1) := by
  have hall := List.all_eq_true.mp types_contains_isS
  have h1 := hall offs h
  have h2 := List.all_eq_true.mp h1
  simpa using h2 i (List.mem_range.mpr hi)

theorem signOff_typeAt (e : Int → Bool) (t : Int) (k : Nat)
    (hA : e t = true) (hmin : minLag11At e t) (hk : k ≤ 11) :
    signOff (typeOf (maskAt e t)) k = sign (e (t - (k : Int))) := by
  have ⟨hmem, hmask⟩ := typeOf_spec (maskAt e t) (maskAt_lt e t)
    ((minLag11At_iff e t).mpr hmin)
  cases k with
  | zero =>
    simp [signOff, sign, hA]
  | succ k =>
    have hk11 : k + 1 ≤ 11 := hk
    have hklt : k < 11 := by omega
    have hcont := contains_iff_isS (typeOf (maskAt e t)) hmem k hklt
    have hs := isS_maskAt e t (k + 1) (by omega) hk11
    have hso : signOff (typeOf (maskAt e t)) (k + 1) =
        if (typeOf (maskAt e t)).contains (k + 1) then (-1 : Int) else 1 := by
      simp [signOff, hk11]
    rw [hso, hcont, hmask, hs, sign]
    cases he : e (t - ((k + 1 : Nat) : Int)) <;> simp [he]

def phi11 (e : Int → Bool) (t : Int) : Int :=
  t - (charge (typeOf (maskAt e t)) : Int)

theorem phi11_is_sub (e : Int → Bool) (t : Int)
    (_hA : e t = true) (hmin : minLag11At e t) :
    e (phi11 e t) = false := by
  have ⟨hmem, hmask⟩ := typeOf_spec (maskAt e t) (maskAt_lt e t)
    ((minLag11At_iff e t).mpr hmin)
  have hS : (typeOf (maskAt e t)).contains (charge (typeOf (maskAt e t))) = true :=
    List.all_eq_true.mp charge_is_S _ hmem
  have hcb := of_decide_eq_true (List.all_eq_true.mp charge_bounds _ hmem)
  have hc2 : charge (typeOf (maskAt e t)) ≤ 11 := hcb.2
  have hc1 : 3 ≤ charge (typeOf (maskAt e t)) := hcb.1
  have hk : charge (typeOf (maskAt e t)) - 1 < 11 := by omega
  have hiff := contains_iff_isS (typeOf (maskAt e t)) hmem
    (charge (typeOf (maskAt e t)) - 1) hk
  have hcsucc : charge (typeOf (maskAt e t)) - 1 + 1 =
      charge (typeOf (maskAt e t)) := by omega
  rw [hcsucc] at hiff
  have hbit : isS (maskAt e t) (charge (typeOf (maskAt e t))) = true := by
    rw [hiff] at hS
    rw [hmask] at hS
    exact hS
  have hs := isS_maskAt e t (charge (typeOf (maskAt e t))) (by omega) hc2
  unfold phi11
  cases he : e (t - (charge (typeOf (maskAt e t)) : Int))
  · rfl
  · rw [hs, he] at hbit
    cases hbit

theorem timeClash_same_time (e : Int → Bool) (T S : Int)
    (hTA : e T = true) (hSA : e S = true)
    (hT : minLag11At e T) (hS : minLag11At e S)
    (hdelta : S = T + (charge (typeOf (maskAt e S)) : Int) -
      (charge (typeOf (maskAt e T)) : Int))
    (hne : typeOf (maskAt e T) ≠ typeOf (maskAt e S)) :
    False := by
  have ⟨hTmem, _⟩ := typeOf_spec (maskAt e T) (maskAt_lt e T)
    ((minLag11At_iff e T).mpr hT)
  have ⟨hSmem, _⟩ := typeOf_spec (maskAt e S) (maskAt_lt e S)
    ((minLag11At_iff e S).mpr hS)
  have hcl := pairwise_timeClash_mem _ _ hTmem hSmem hne
  have hany := List.any_eq_true.mp hcl
  obtain ⟨k, hkmem, hbit⟩ := hany
  have hk : k < 12 := List.mem_range.mp hkmem
  have hk11 : k ≤ 11 := by omega
  have hbit' :
      0 ≤ (charge (typeOf (maskAt e S)) : Int) -
            charge (typeOf (maskAt e T)) + k ∧
        (charge (typeOf (maskAt e S)) : Int) -
            charge (typeOf (maskAt e T)) + k ≤ 11 ∧
          signOff (typeOf (maskAt e T)) k ≠
            signOff (typeOf (maskAt e S))
              (((charge (typeOf (maskAt e S)) : Int) -
                  charge (typeOf (maskAt e T)) + k).toNat) := by
    simpa [decide_eq_true_eq] using hbit
  let sOff : Int :=
    (charge (typeOf (maskAt e S)) : Int) - charge (typeOf (maskAt e T)) + k
  have hs0 : 0 ≤ sOff := hbit'.1
  have hneSign := hbit'.2.2
  have hsignT := signOff_typeAt e T k hTA hT hk11
  have hsNat : sOff.toNat ≤ 11 := by
    have : (sOff.toNat : Int) = sOff := Int.toNat_of_nonneg hs0
    have hs11 : sOff ≤ 11 := hbit'.2.1
    omega
  have hsignS := signOff_typeAt e S sOff.toNat hSA hS hsNat
  have htime : S - (sOff.toNat : Int) = T - (k : Int) := by
    have : (sOff.toNat : Int) = sOff := Int.toNat_of_nonneg hs0
    rw [this, hdelta]
    omega
  have hto : (sOff.toNat : Int) = sOff := Int.toNat_of_nonneg hs0
  have hne' : sign (e (T - (k : Int))) ≠ sign (e (S - (sOff.toNat : Int))) := by
    rw [hsignT] at hneSign
    rw [hsignS] at hneSign
    exact hneSign
  rw [htime] at hne'
  exact hne' rfl

def u11Count (e : Int → Bool) (t : Int) : Nat → Nat
  | 0 => 0
  | n + 1 =>
      u11Count e t n +
        if e (t + n) && minLag11 (maskAt e (t + n)) then 1 else 0

def phi11Phase (e : Int → Bool) (t : Int) (p i : Nat) : Nat :=
  Int.toNat (((i : Int) - (charge (typeOf (maskAt e (t + i))) : Int)) % (p : Int))

theorem e_shift_nat (e : Int → Bool) (p : Nat) (hp : ∀ x : Int, e (x + p) = e x) :
    ∀ n : Nat, ∀ x : Int, e (x + n * p) = e x := by
  intro n
  induction n with
  | zero =>
    intro x
    simp
  | succ n ih =>
    intro x
    have hn : ((n + 1 : Nat) : Int) = (n : Int) + 1 := by omega
    have hmul : ((n + 1 : Nat) : Int) * p = (n : Int) * p + p := by
      rw [hn, Int.add_mul, Int.one_mul]
    have hx : x + ((n + 1 : Nat) : Int) * p = (x + (n : Int) * p) + p := by
      rw [hmul]; omega
    rw [hx, hp, ih]

theorem e_shift (e : Int → Bool) (p : Nat) (hp : ∀ x : Int, e (x + p) = e x)
    (k : Int) (x : Int) : e (x + k * p) = e x := by
  match k with
  | Int.ofNat n =>
    simpa using e_shift_nat e p hp n x
  | Int.negSucc n =>
    have hnat := e_shift_nat e p hp (n + 1) (x + (Int.negSucc n) * p)
    have hx : x + (Int.negSucc n) * p + ((n + 1 : Nat) : Int) * p = x := by
      have hk : Int.negSucc n = -((n + 1 : Nat) : Int) := rfl
      rw [hk, Int.neg_mul]
      exact Int.neg_add_cancel_right _ _
    rw [hx] at hnat
    exact hnat.symm

theorem maskAt_shift (e : Int → Bool) (p : Nat)
    (hp : ∀ x : Int, e (x + p) = e x) (t : Int) (k : Int) :
    maskAt e (t + k * p) = maskAt e t := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 11
  · rw [maskAt_testBit e (t + k * p) i hi, maskAt_testBit e t i hi]
    have := e_shift e p hp k (t - ((i + 1 : Nat) : Int))
    have hpos : t + k * p - ((i + 1 : Nat) : Int) =
        (t - ((i + 1 : Nat) : Int)) + k * p := by omega
    rw [hpos, this]
  · have : 11 ≤ i := by omega
    unfold maskAt
    rw [maskAux_testBit_ge e (t + k * p) 11 i this,
      maskAux_testBit_ge e t 11 i this]

set_option maxHeartbeats 0 in
theorem supplied_is_lag3_or_h1_or_h2 :
    ∀ s : Window,
      supplied s = true →
        (s.val.testBit 0 = true ∧ s.val.testBit 1 = true ∧ s.val.testBit 2 = false) ∨
        (s.val.testBit 0 = false ∧ s.val.testBit 1 = true ∧ s.val.testBit 2 = true ∧
          s.val.testBit 3 = true ∧ s.val.testBit 4 = true ∧ s.val.testBit 5 = false ∧
          s.val.testBit 6 = false) ∨
        (s.val.testBit 0 = true ∧ s.val.testBit 1 = false ∧ s.val.testBit 2 = true ∧
          s.val.testBit 3 = true ∧ s.val.testBit 4 = false ∧ s.val.testBit 5 = true ∧
          s.val.testBit 6 = false) := by
  decide

theorem range3 : List.range 3 = [0, 1, 2] := by decide

theorem range7 : List.range 7 = [0, 1, 2, 3, 4, 5, 6] := by decide

theorem u7_not_u11 (e : Int → Bool) (t : Int)
    (h : supplied (window e t) = true) :
    minLag11 (maskAt e t) = false := by
  have hpat := supplied_is_lag3_or_h1_or_h2 (window e t) h
  have b0 := window_bit e t 0 (by decide)
  have b1 := window_bit e t 1 (by decide)
  have b2 := window_bit e t 2 (by decide)
  have b3 := window_bit e t 3 (by decide)
  have b4 := window_bit e t 4 (by decide)
  have b5 := window_bit e t 5 (by decide)
  have b6 := window_bit e t 6 (by decide)
  have ebit (i : Nat) (hi : i < 7) :
      e (t - ((i + 1 : Nat) : Int)) = (window e t).val.testBit i :=
    (window_bit e t i hi).symm
  have not11 : ¬ minLag11At e t := by
    intro hmin
    rcases hpat with hlag3 | h1 | h2
    · have : P2 e t 3 := by
        have e0 := (ebit 0 (by decide)).trans hlag3.1
        have e1 := (ebit 1 (by decide)).trans hlag3.2.1
        have e2 := (ebit 2 (by decide)).trans hlag3.2.2
        simp at e0 e1 e2
        constructor
        · simp [range3, sign, List.map, List.sum, e0, e1, e2]
        · simp [range3, sign, List.map, List.sum, e0, e1, e2]
      exact hmin.2.1 this
    · have : P2 e t 7 := by
        have e0 := (ebit 0 (by decide)).trans h1.1
        have e1 := (ebit 1 (by decide)).trans h1.2.1
        have e2 := (ebit 2 (by decide)).trans h1.2.2.1
        have e3 := (ebit 3 (by decide)).trans h1.2.2.2.1
        have e4 := (ebit 4 (by decide)).trans h1.2.2.2.2.1
        have e5 := (ebit 5 (by decide)).trans h1.2.2.2.2.2.1
        have e6 := (ebit 6 (by decide)).trans h1.2.2.2.2.2.2
        simp at e0 e1 e2 e3 e4 e5 e6
        constructor
        · simp [range7, sign, List.map, List.sum, e0, e1, e2, e3, e4, e5, e6]
        · simp [range7, sign, List.map, List.sum, e0, e1, e2, e3, e4, e5, e6]
      exact hmin.2.2 this
    · have : P2 e t 7 := by
        have e0 := (ebit 0 (by decide)).trans h2.1
        have e1 := (ebit 1 (by decide)).trans h2.2.1
        have e2 := (ebit 2 (by decide)).trans h2.2.2.1
        have e3 := (ebit 3 (by decide)).trans h2.2.2.2.1
        have e4 := (ebit 4 (by decide)).trans h2.2.2.2.2.1
        have e5 := (ebit 5 (by decide)).trans h2.2.2.2.2.2.1
        have e6 := (ebit 6 (by decide)).trans h2.2.2.2.2.2.2
        simp at e0 e1 e2 e3 e4 e5 e6
        constructor
        · simp [range7, sign, List.map, List.sum, e0, e1, e2, e3, e4, e5, e6]
        · simp [range7, sign, List.map, List.sum, e0, e1, e2, e3, e4, e5, e6]
      exact hmin.2.2 this
  cases hml : minLag11 (maskAt e t)
  · rfl
  · exact absurd ((minLag11At_iff e t).mp hml) not11

def u11Phases (e : Int → Bool) (t : Int) (p : Nat) : List Nat :=
  (List.range p).filter (fun i => e (t + i) && minLag11 (maskAt e (t + i)))

def subPhases (e : Int → Bool) (t : Int) (p : Nat) : List Nat :=
  (List.range p).filter (fun i => decide (e (t + i) = false))

theorem phi11Phase_lt (e : Int → Bool) (t : Int) {p : Nat} (hp : 0 < p) (i : Nat) :
    phi11Phase e t p i < p := by
  unfold phi11Phase
  have hp0 : (0 : Int) < p := by omega
  have hmod := Int.emod_lt_of_pos
    ((i : Int) - (charge (typeOf (maskAt e (t + i))) : Int)) hp0
  have hpne : (p : Int) ≠ 0 := Int.natCast_ne_zero.mpr (Nat.ne_zero_of_lt hp)
  have hnn := Int.emod_nonneg
    ((i : Int) - (charge (typeOf (maskAt e (t + i))) : Int)) hpne
  have heq : ((Int.toNat
      (((i : Int) - (charge (typeOf (maskAt e (t + i))) : Int)) % (p : Int))) : Int) =
      (((i : Int) - (charge (typeOf (maskAt e (t + i))) : Int)) % (p : Int)) :=
    Int.toNat_of_nonneg hnn
  have hltInt : ((Int.toNat
      (((i : Int) - (charge (typeOf (maskAt e (t + i))) : Int)) % (p : Int))) : Int) < p := by
    rw [heq]; exact hmod
  exact Int.ofNat_lt.mp hltInt

theorem emod_toNat_inj {p : Nat} (_hp : 0 < p) {a b : Int}
    (ha : 0 ≤ a % p) (hb : 0 ≤ b % p)
    (h : Int.toNat (a % p) = Int.toNat (b % p)) :
    a % p = b % p := by
  have ha' : ((Int.toNat (a % p) : Int) = a % p) := Int.toNat_of_nonneg ha
  have hb' : ((Int.toNat (b % p) : Int) = b % p) := Int.toNat_of_nonneg hb
  rw [← ha', ← hb', h]

theorem phi11Phase_emod (e : Int → Bool) (t : Int) {p : Nat} (hp : 0 < p) (i : Nat) :
    (phi11Phase e t p i : Int) =
      ((i : Int) - (charge (typeOf (maskAt e (t + i))) : Int)) % p := by
  unfold phi11Phase
  have hpne : (p : Int) ≠ 0 := Int.natCast_ne_zero.mpr (Nat.ne_zero_of_lt hp)
  exact Int.toNat_of_nonneg (Int.emod_nonneg _ hpne)

theorem minLag11At_shift (e : Int → Bool) (p : Nat)
    (hp : ∀ x : Int, e (x + p) = e x) (t : Int) (k : Int) :
    minLag11At e (t + k * p) ↔ minLag11At e t := by
  have hm := maskAt_shift e p hp t k
  constructor
  · intro h
    exact (minLag11At_iff e t).mp (by
      have := (minLag11At_iff e (t + k * p)).mpr h
      simpa [hm] using this)
  · intro h
    exact (minLag11At_iff e (t + k * p)).mp (by
      have := (minLag11At_iff e t).mpr h
      simpa [hm] using this)

theorem phi11Phase_is_sub (e : Int → Bool) (t : Int) {p : Nat}
    (hper : ∀ x : Int, e (x + p) = e x) (hp : 0 < p) (i : Nat)
    (hA : e (t + i) = true) (hmin : minLag11 (maskAt e (t + i)) = true) :
    e (t + phi11Phase e t p i) = false := by
  have hminP : minLag11At e (t + i) := (minLag11At_iff e (t + i)).mp hmin
  have hs := phi11_is_sub e (t + i) hA hminP
  have hphi : phi11 e (t + i) =
      (t + i) - (charge (typeOf (maskAt e (t + i))) : Int) := rfl
  rw [hphi] at hs
  have hdecomp := Int.ediv_mul_add_emod
    ((i : Int) - (charge (typeOf (maskAt e (t + i))) : Int)) (p : Int)
  have hclock :
      (t + i : Int) - charge (typeOf (maskAt e (t + i))) =
        (t + (((i : Int) - charge (typeOf (maskAt e (t + i)))) % p)) +
          (((i : Int) - charge (typeOf (maskAt e (t + i)))) / p) * p := by
    have := hdecomp
    omega
  have hshift := e_shift e p hper
    (((i : Int) - (charge (typeOf (maskAt e (t + i))) : Int)) / p)
    (t + (((i : Int) - (charge (typeOf (maskAt e (t + i))) : Int)) % p))
  have hmod :
      e (t + (((i : Int) - charge (typeOf (maskAt e (t + i)))) % p)) =
        e ((t + i) - charge (typeOf (maskAt e (t + i)))) := by
    rw [hclock, hshift]
  have hnat : (t + phi11Phase e t p i : Int) =
      t + (((i : Int) - charge (typeOf (maskAt e (t + i)))) % p) := by
    have := phi11Phase_emod e t hp i
    omega
  have heq : e (t + phi11Phase e t p i) =
      e (t + (((i : Int) - charge (typeOf (maskAt e (t + i)))) % p)) := by
    rw [hnat]
  rw [heq, hmod]
  exact hs

theorem charge_eq_of_typeOf_eq (m₁ m₂ : Nat)
    (h : typeOf m₁ = typeOf m₂) :
    charge (typeOf m₁) = charge (typeOf m₂) := by
  rw [h]

theorem phi11Phase_inj (e : Int → Bool) (t : Int) {p : Nat}
    (hper : ∀ x : Int, e (x + p) = e x) (hp : 0 < p)
    (i j : Nat) (hi : i < p) (hj : j < p)
    (hAi : e (t + i) = true) (hAj : e (t + j) = true)
    (hmi : minLag11 (maskAt e (t + i)) = true)
    (hmj : minLag11 (maskAt e (t + j)) = true)
    (heq : phi11Phase e t p i = phi11Phase e t p j) :
    i = j := by
  have hemod :
      ((i : Int) - charge (typeOf (maskAt e (t + i)))) % p =
        ((j : Int) - charge (typeOf (maskAt e (t + j)))) % p := by
    have hi' := phi11Phase_emod e t hp i
    have hj' := phi11Phase_emod e t hp j
    rw [← hi', ← hj', heq]
  have hdvd : (p : Int) ∣
      ((i : Int) - charge (typeOf (maskAt e (t + i)))) -
        ((j : Int) - charge (typeOf (maskAt e (t + j)))) :=
    Int.dvd_iff_emod_eq_zero.mpr
      ((Int.emod_eq_emod_iff_emod_sub_eq_zero).mp hemod)
  obtain ⟨k, hk⟩ := hdvd
  have hk' :
      ((i : Int) - charge (typeOf (maskAt e (t + i)))) -
        ((j : Int) - charge (typeOf (maskAt e (t + j)))) = k * p := by
    rw [Int.mul_comm] at hk
    exact hk
  by_cases htypes : typeOf (maskAt e (t + i)) = typeOf (maskAt e (t + j))
  · have hch : charge (typeOf (maskAt e (t + i))) =
        charge (typeOf (maskAt e (t + j))) := by rw [htypes]
    have hij : (i : Int) - j = k * p := by
      rw [hch] at hk'
      omega
    have hk0 : k = 0 := by
      have hhi : k * p < p := by
        have : (i : Int) - j < p := by omega
        rw [← hij]; exact this
      have hlo : -((p : Int)) < k * p := by
        have : -((p : Int)) < (i : Int) - j := by omega
        rw [← hij]; exact this
      by_cases hkpos : 0 ≤ k
      · by_cases hz : k = 0
        · exact hz
        · have hk1 : (1 : Int) ≤ k := by omega
          have hle : (1 : Int) * p ≤ k * p :=
            Int.mul_le_mul_of_nonneg_right hk1 (by omega : (0 : Int) ≤ p)
          rw [Int.one_mul] at hle
          omega
      · have hk1 : k ≤ (-1 : Int) := by omega
        have hle : k * p ≤ (-1 : Int) * p :=
          Int.mul_le_mul_of_nonneg_right hk1 (by omega : (0 : Int) ≤ p)
        rw [Int.neg_one_mul] at hle
        omega
    have : (i : Int) = j := by
      rw [hk0] at hij
      omega
    exact Int.ofNat_inj.mp this
  · have hS' :
        (t + i : Int) + charge (typeOf (maskAt e (t + j))) -
            charge (typeOf (maskAt e (t + i))) =
          (t + j) + k * p := by
      omega
    have heS' : e ((t + i : Int) + charge (typeOf (maskAt e (t + j))) -
        charge (typeOf (maskAt e (t + i)))) = true := by
      have hsh := e_shift e p hper k (t + j)
      rw [hS']
      simpa using hsh.trans hAj
    have hmask' :
        maskAt e ((t + i : Int) + charge (typeOf (maskAt e (t + j))) -
            charge (typeOf (maskAt e (t + i)))) =
          maskAt e (t + j) := by
      have hsh := maskAt_shift e p hper (t + j) k
      rw [hS']
      exact hsh
    have hminT : minLag11At e (t + i) := (minLag11At_iff e (t + i)).mp hmi
    have hminS' : minLag11At e ((t + i : Int) +
        charge (typeOf (maskAt e (t + j))) -
        charge (typeOf (maskAt e (t + i)))) := by
      have hminJ : minLag11At e (t + j) := (minLag11At_iff e (t + j)).mp hmj
      have := (minLag11At_shift e p hper (t + j) k).mpr hminJ
      simpa [hS'] using this
    have hne : typeOf (maskAt e (t + i)) ≠
        typeOf (maskAt e ((t + i : Int) +
          charge (typeOf (maskAt e (t + j))) -
          charge (typeOf (maskAt e (t + i))))) := by
      simpa [hmask'] using htypes
    have hdelta :
        (t + i : Int) + charge (typeOf (maskAt e (t + j))) -
            charge (typeOf (maskAt e (t + i))) =
          (t + i) +
            charge (typeOf (maskAt e ((t + i : Int) +
              charge (typeOf (maskAt e (t + j))) -
              charge (typeOf (maskAt e (t + i)))))) -
            charge (typeOf (maskAt e (t + i))) := by
      simp [hmask']
    exact (timeClash_same_time e (t + i)
      ((t + i : Int) + charge (typeOf (maskAt e (t + j))) -
        charge (typeOf (maskAt e (t + i))))
      hAi heS' hminT hminS' hdelta hne).elim

theorem filter_length_succ (pred : Nat → Bool) (n : Nat) :
    ((List.range (n + 1)).filter pred).length =
      ((List.range n).filter pred).length + if pred n then 1 else 0 := by
  rw [List.range_succ, List.filter_append, List.length_append]
  cases h : pred n
  · rw [List.filter_cons_of_neg (by simp [h])]
    simp
  · rw [List.filter_cons_of_pos (by simpa using h)]
    simp

theorem range_zero : List.range 0 = [] :=
  (List.range_eq_nil (n := 0)).mpr rfl

theorem u11Count_eq_filter (e : Int → Bool) (t : Int) :
    ∀ n, u11Count e t n = (u11Phases e t n).length := by
  intro n
  induction n with
  | zero =>
    simp [u11Count, u11Phases, range_zero]
  | succ n ih =>
    rw [u11Count]
    have hsucc := filter_length_succ
      (fun (i : Nat) => e (t + i) && minLag11 (maskAt e (t + i))) n
    have h1 : u11Phases e t (n + 1) =
        (List.range (n + 1)).filter
          (fun (i : Nat) => e (t + i) && minLag11 (maskAt e (t + i))) := rfl
    have h0 : u11Phases e t n =
        (List.range n).filter
          (fun (i : Nat) => e (t + i) && minLag11 (maskAt e (t + i))) := rfl
    rw [h1, hsucc, ← h0, ih]

def u7Phases (e : Int → Bool) (t : Int) (p : Nat) : List Nat :=
  (List.range p).filter (fun i => e (t + i) && supplied (window e (t + i)))

theorem suppliedCount_eq_filter (e : Int → Bool) (t : Int) :
    ∀ n, suppliedCount e t n = (u7Phases e t n).length := by
  intro n
  induction n with
  | zero =>
    simp [suppliedCount, u7Phases, range_zero]
  | succ n ih =>
    rw [suppliedCount]
    have hsucc := filter_length_succ
      (fun (i : Nat) => e (t + i) && supplied (window e (t + i))) n
    have h1 : u7Phases e t (n + 1) =
        (List.range (n + 1)).filter
          (fun (i : Nat) => e (t + i) && supplied (window e (t + i))) := rfl
    have h0 : u7Phases e t n =
        (List.range n).filter
          (fun (i : Nat) => e (t + i) && supplied (window e (t + i))) := rfl
    rw [h1, hsucc, ← h0, ih]

theorem subtractionCount_eq_filter (e : Int → Bool) (t : Int) :
    ∀ n, subtractionCount e t n = (subPhases e t n).length := by
  intro n
  induction n with
  | zero =>
    simp [subtractionCount, subPhases, range_zero]
  | succ n ih =>
    rw [subtractionCount]
    have hsucc := filter_length_succ
      (fun (i : Nat) => decide (e (t + i) = false)) n
    have h1 : subPhases e t (n + 1) =
        (List.range (n + 1)).filter
          (fun (i : Nat) => decide (e (t + i) = false)) := rfl
    have h0 : subPhases e t n =
        (List.range n).filter
          (fun (i : Nat) => decide (e (t + i) = false)) := rfl
    rw [h1, hsucc, ← h0, ih]
    cases h : e (t + n) <;> simp [h]

theorem mem_u11Phases (e : Int → Bool) (t : Int) (p i : Nat) :
    i ∈ u11Phases e t p ↔
      i < p ∧ e (t + i) = true ∧ minLag11 (maskAt e (t + i)) = true := by
  simp [u11Phases, List.mem_filter, List.mem_range, Bool.and_eq_true]

theorem mem_u7Phases (e : Int → Bool) (t : Int) (p i : Nat) :
    i ∈ u7Phases e t p ↔
      i < p ∧ e (t + i) = true ∧ supplied (window e (t + i)) = true := by
  simp [u7Phases, List.mem_filter, List.mem_range, Bool.and_eq_true]

theorem mem_subPhases (e : Int → Bool) (t : Int) (p i : Nat) :
    i ∈ subPhases e t p ↔ i < p ∧ e (t + i) = false := by
  simp [subPhases, List.mem_filter, List.mem_range]

theorem nodup_map_of_inj {l : List Nat} {f : Nat → Nat}
    (h : l.Nodup)
    (hinj : ∀ a b, a ∈ l → b ∈ l → f a = f b → a = b) :
    (l.map f).Nodup := by
  induction l with
  | nil => simp
  | cons a xs ih =>
    rw [List.nodup_cons] at h
    refine (List.nodup_cons.mpr ⟨?_, ?_⟩)
    · intro hmem
      obtain ⟨b, hb, hfeq⟩ := List.mem_map.mp hmem
      have heqab : a = b := hinj a b List.mem_cons_self (List.mem_cons_of_mem _ hb) hfeq.symm
      exact h.1 (heqab ▸ hb)
    · exact ih h.2 fun x y hx hy =>
        hinj x y (List.mem_cons_of_mem _ hx) (List.mem_cons_of_mem _ hy)

def isLag3Win (s : Window) : Bool :=
  s.val.testBit 0 && s.val.testBit 1 && !s.val.testBit 2

def isH1Win (s : Window) : Bool :=
  !s.val.testBit 0 && s.val.testBit 1 && s.val.testBit 2 &&
    s.val.testBit 3 && s.val.testBit 4 && !s.val.testBit 5 && !s.val.testBit 6

def isH2Win (s : Window) : Bool :=
  s.val.testBit 0 && !s.val.testBit 1 && s.val.testBit 2 &&
    s.val.testBit 3 && !s.val.testBit 4 && s.val.testBit 5 && !s.val.testBit 6

def phi7Off (s : Window) : Nat :=
  if isLag3Win s then 3 else if isH1Win s then 7 else 5

def phi7Phase (e : Int → Bool) (t : Int) (p i : Nat) : Nat :=
  Int.toNat (((i : Int) - (phi7Off (window e (t + i)) : Int)) % (p : Int))

def followingGap (e : Int → Bool) (t : Int) (p q : Nat) : Nat :=
  (List.range p).findIdx
    (fun d => decide (e (t + (q + d + 1 : Nat)) = false)) + 1

theorem u11_images_subset_sub (e : Int → Bool) (t : Int) {p : Nat}
    (hper : ∀ x : Int, e (x + p) = e x) (hp : 0 < p) :
    (u11Phases e t p).map (phi11Phase e t p) ⊆ subPhases e t p := by
  intro y hy
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy
  have ⟨hip, hA, hmin⟩ := (mem_u11Phases e t p i).mp hi
  have hs := phi11Phase_is_sub e t hper hp i hA hmin
  have hlt := phi11Phase_lt e t hp i
  exact (mem_subPhases e t p _).mpr ⟨hlt, hs⟩

theorem u11_images_nodup (e : Int → Bool) (t : Int) {p : Nat}
    (hper : ∀ x : Int, e (x + p) = e x) (hp : 0 < p) :
    ((u11Phases e t p).map (phi11Phase e t p)).Nodup := by
  refine nodup_map_of_inj (List.Nodup.sublist List.filter_sublist List.nodup_range) ?_
  intro a b ha hb hf
  have ha' := (mem_u11Phases e t p a).mp ha
  have hb' := (mem_u11Phases e t p b).mp hb
  exact phi11Phase_inj e t hper hp a b ha'.1 hb'.1 ha'.2.1 hb'.2.1 ha'.2.2 hb'.2.2 hf

theorem u11Count_le_subtractionCount (e : Int → Bool) (t : Int) {p : Nat}
    (hper : ∀ x : Int, e (x + p) = e x) (hp : 0 < p) :
    u11Count e t p ≤ subtractionCount e t p := by
  have hnodup := u11_images_nodup e t hper hp
  have hsub := u11_images_subset_sub e t hper hp
  have hlen := hnodup.length_le_of_subset hsub
  simpa [u11Count_eq_filter, subtractionCount_eq_filter, List.length_map] using hlen

theorem phi7Off_of_supplied (s : Window) (h : supplied s = true) :
    (isLag3Win s = true ∧ phi7Off s = 3) ∨
      (isH1Win s = true ∧ phi7Off s = 7) ∨
        (isH2Win s = true ∧ phi7Off s = 5) := by
  have hpat := supplied_is_lag3_or_h1_or_h2 s h
  rcases hpat with h3 | h1 | h2
  · refine .inl ⟨?_, ?_⟩
    · simp [isLag3Win, h3]
    · simp [phi7Off, isLag3Win, h3]
  · refine .inr (.inl ⟨?_, ?_⟩)
    · simp [isH1Win, h1]
    · simp [phi7Off, isLag3Win, isH1Win, h1]
  · refine .inr (.inr ⟨?_, ?_⟩)
    · simp [isH2Win, h2]
    · simp [phi7Off, isLag3Win, isH1Win, isH2Win, h2]

theorem phi7Off_is_S (e : Int → Bool) (t : Int)
    (h : supplied (window e t) = true) :
    e (t - (phi7Off (window e t) : Int)) = false := by
  have b2 := window_bit e t 2 (by decide)
  have b4 := window_bit e t 4 (by decide)
  have b6 := window_bit e t 6 (by decide)
  rcases phi7Off_of_supplied (window e t) h with h3 | h1 | h2
  · have hoff : phi7Off (window e t) = 3 := h3.2
    have hs : (window e t).val.testBit 2 = false := by
      have hw := h3.1
      unfold isLag3Win at hw
      cases h0 : (window e t).val.testBit 0 <;>
        cases h1 : (window e t).val.testBit 1 <;>
        cases h2 : (window e t).val.testBit 2 <;>
        simp [h0, h1, h2] at hw <;> rfl
    have he3 : e (t - (3 : Int)) = false := by
      have hb := b2
      simp at hb
      rw [← hb]
      exact hs
    rw [hoff]
    exact he3
  · have hoff : phi7Off (window e t) = 7 := h1.2
    have hs : (window e t).val.testBit 6 = false := by
      have hw := h1.1
      unfold isH1Win at hw
      cases h6 : (window e t).val.testBit 6 <;> simp [h6] at hw <;> rfl
    have he7 : e (t - (7 : Int)) = false := by
      have hb := b6
      simp at hb
      rw [← hb]
      exact hs
    rw [hoff]
    exact he7
  · have hoff : phi7Off (window e t) = 5 := h2.2
    have hs : (window e t).val.testBit 4 = false := by
      have hw := h2.1
      unfold isH2Win at hw
      cases h4 : (window e t).val.testBit 4 <;> simp [h4] at hw <;> rfl
    have he5 : e (t - (5 : Int)) = false := by
      have hb := b4
      simp at hb
      rw [← hb]
      exact hs
    rw [hoff]
    exact he5

theorem phi7Phase_emod (e : Int → Bool) (t : Int) {p : Nat} (hp : 0 < p) (i : Nat) :
    (phi7Phase e t p i : Int) =
      ((i : Int) - (phi7Off (window e (t + i)) : Int)) % p := by
  unfold phi7Phase
  have hpne : (p : Int) ≠ 0 := Int.natCast_ne_zero.mpr (Nat.ne_zero_of_lt hp)
  exact Int.toNat_of_nonneg (Int.emod_nonneg _ hpne)

theorem phi7Phase_lt (e : Int → Bool) (t : Int) {p : Nat} (hp : 0 < p) (i : Nat) :
    phi7Phase e t p i < p := by
  unfold phi7Phase
  have hp0 : (0 : Int) < p := by omega
  have hmod := Int.emod_lt_of_pos
    ((i : Int) - (phi7Off (window e (t + i)) : Int)) hp0
  have hpne : (p : Int) ≠ 0 := Int.natCast_ne_zero.mpr (Nat.ne_zero_of_lt hp)
  have hnn := Int.emod_nonneg
    ((i : Int) - (phi7Off (window e (t + i)) : Int)) hpne
  have heq : ((Int.toNat
      (((i : Int) - (phi7Off (window e (t + i)) : Int)) % (p : Int))) : Int) =
      (((i : Int) - (phi7Off (window e (t + i)) : Int)) % (p : Int)) :=
    Int.toNat_of_nonneg hnn
  have hltInt : ((Int.toNat
      (((i : Int) - (phi7Off (window e (t + i)) : Int)) % (p : Int))) : Int) < p := by
    rw [heq]; exact hmod
  exact Int.ofNat_lt.mp hltInt

theorem phi7Phase_is_sub (e : Int → Bool) (t : Int) {p : Nat}
    (hper : ∀ x : Int, e (x + p) = e x) (hp : 0 < p) (i : Nat)
    (_hA : e (t + i) = true) (hsup : supplied (window e (t + i)) = true) :
    e (t + phi7Phase e t p i) = false := by
  have hs := phi7Off_is_S e (t + i) hsup
  have hdecomp := Int.ediv_mul_add_emod
    ((i : Int) - (phi7Off (window e (t + i)) : Int)) (p : Int)
  have hclock :
      (t + i : Int) - phi7Off (window e (t + i)) =
        (t + (((i : Int) - phi7Off (window e (t + i))) % p)) +
          (((i : Int) - phi7Off (window e (t + i))) / p) * p := by
    have := hdecomp
    omega
  have hshift := e_shift e p hper
    (((i : Int) - (phi7Off (window e (t + i)) : Int)) / p)
    (t + (((i : Int) - (phi7Off (window e (t + i)) : Int)) % p))
  have hmod :
      e (t + (((i : Int) - phi7Off (window e (t + i))) % p)) =
        e ((t + i) - phi7Off (window e (t + i))) := by
    rw [hclock, hshift]
  have hnat : (t + phi7Phase e t p i : Int) =
      t + (((i : Int) - phi7Off (window e (t + i))) % p) := by
    have := phi7Phase_emod e t hp i
    omega
  have heq : e (t + phi7Phase e t p i) =
      e (t + (((i : Int) - phi7Off (window e (t + i))) % p)) := by
    rw [hnat]
  rw [heq, hmod]
  exact hs

def signOff7 (offs : List Nat) : Nat → Int
  | 0 => 1
  | k + 1 =>
      if k + 1 ≤ 7 then (if offs.contains (k + 1) then -1 else 1) else 99

def timeClash7 (tau sig : List Nat) (i j : Nat) : Bool :=
  (List.range 8).any fun k =>
    let sOff := (j : Int) - i + k
    decide
      (0 ≤ sOff ∧ sOff ≤ 7 ∧ signOff7 tau k ≠ signOff7 sig sOff.toNat)

def u7lag3 : List Nat := [3]
def u7h1 : List Nat := [1, 6, 7]
def u7h2 : List Nat := [2, 5, 7]

set_option maxHeartbeats 0 in
theorem u7_pairwise_timeClash7 :
    timeClash7 u7lag3 u7h1 3 7 = true ∧
      timeClash7 u7h1 u7lag3 7 3 = true ∧
      timeClash7 u7lag3 u7h2 3 5 = true ∧
      timeClash7 u7h2 u7lag3 5 3 = true ∧
      timeClash7 u7h1 u7h2 7 5 = true ∧
      timeClash7 u7h2 u7h1 5 7 = true := by
  decide

theorem window_shift (e : Int → Bool) (p : Nat)
    (hp : ∀ x : Int, e (x + p) = e x) (t : Int) (k : Int) :
    window e (t + k * p) = window e t := by
  have h (i : Int) : e (t + k * p - i) = e (t - i) := by
    have : t + k * p - i = (t - i) + k * p := by omega
    rw [this, e_shift e p hp k (t - i)]
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  have h5 := h 5
  have h6 := h 6
  have h7 := h 7
  simp only [window, h1, h2, h3, h4, h5, h6, h7]

theorem phi7Off_bounds {s : Window} (h : supplied s = true) :
    3 ≤ phi7Off s ∧ phi7Off s ≤ 7 := by
  rcases phi7Off_of_supplied s h with h3 | h1 | h2
  · simp [h3.2]
  · simp [h1.2]
  · simp [h2.2]

set_option maxHeartbeats 0 in
theorem isLag3Win_bits {s : Window} (h : isLag3Win s = true) :
    s.val.testBit 0 = true ∧ s.val.testBit 1 = true ∧ s.val.testBit 2 = false := by
  revert h
  unfold isLag3Win
  cases h0 : s.val.testBit 0 <;> cases h1 : s.val.testBit 1 <;>
    cases h2 : s.val.testBit 2 <;> intro h <;> simp at h ⊢

set_option maxHeartbeats 0 in
theorem isH1Win_bits {s : Window} (h : isH1Win s = true) :
    s.val.testBit 0 = false ∧ s.val.testBit 1 = true ∧ s.val.testBit 2 = true ∧
      s.val.testBit 3 = true ∧ s.val.testBit 4 = true ∧
      s.val.testBit 5 = false ∧ s.val.testBit 6 = false := by
  revert h
  unfold isH1Win
  cases h0 : s.val.testBit 0 <;> cases h1 : s.val.testBit 1 <;>
    cases h2 : s.val.testBit 2 <;> cases h3 : s.val.testBit 3 <;>
    cases h4 : s.val.testBit 4 <;> cases h5 : s.val.testBit 5 <;>
    cases h6 : s.val.testBit 6 <;> intro h <;> simp at h ⊢

set_option maxHeartbeats 0 in
theorem isH2Win_bits {s : Window} (h : isH2Win s = true) :
    s.val.testBit 0 = true ∧ s.val.testBit 1 = false ∧ s.val.testBit 2 = true ∧
      s.val.testBit 3 = true ∧ s.val.testBit 4 = false ∧
      s.val.testBit 5 = true ∧ s.val.testBit 6 = false := by
  revert h
  unfold isH2Win
  cases h0 : s.val.testBit 0 <;> cases h1 : s.val.testBit 1 <;>
    cases h2 : s.val.testBit 2 <;> cases h3 : s.val.testBit 3 <;>
    cases h4 : s.val.testBit 4 <;> cases h5 : s.val.testBit 5 <;>
    cases h6 : s.val.testBit 6 <;> intro h <;> simp at h ⊢

theorem window_e1 (e : Int → Bool) (t : Int) :
    (window e t).val.testBit 0 = e (t - 1) := by
  simpa using window_bit e t 0 (by decide)
theorem window_e2 (e : Int → Bool) (t : Int) :
    (window e t).val.testBit 1 = e (t - 2) := by
  simpa using window_bit e t 1 (by decide)
theorem window_e3 (e : Int → Bool) (t : Int) :
    (window e t).val.testBit 2 = e (t - 3) := by
  simpa using window_bit e t 2 (by decide)
theorem window_e4 (e : Int → Bool) (t : Int) :
    (window e t).val.testBit 3 = e (t - 4) := by
  simpa using window_bit e t 3 (by decide)
theorem window_e5 (e : Int → Bool) (t : Int) :
    (window e t).val.testBit 4 = e (t - 5) := by
  simpa using window_bit e t 4 (by decide)
theorem window_e6 (e : Int → Bool) (t : Int) :
    (window e t).val.testBit 5 = e (t - 6) := by
  simpa using window_bit e t 5 (by decide)
theorem window_e7 (e : Int → Bool) (t : Int) :
    (window e t).val.testBit 6 = e (t - 7) := by
  simpa using window_bit e t 6 (by decide)

theorem int_nat1 : ((1 : Nat) : Int) = 1 := rfl
theorem int_nat2 : ((2 : Nat) : Int) = 2 := rfl
theorem int_nat3 : ((3 : Nat) : Int) = 3 := rfl
theorem int_nat4 : ((4 : Nat) : Int) = 4 := rfl
theorem int_nat5 : ((5 : Nat) : Int) = 5 := rfl
theorem int_nat6 : ((6 : Nat) : Int) = 6 := rfl
theorem int_nat7 : ((7 : Nat) : Int) = 7 := rfl

theorem isH1Win_sign (e : Int → Bool) (T : Int)
    (hA : e T = true) (hw : isH1Win (window e T) = true)
    (k : Nat) (hk : k ≤ 7) :
    sign (e (T - (k : Int))) =
      (if k == 0 then (1 : Int)
        else if k == 1 || k == 6 || k == 7 then -1 else 1) := by
  have bits := isH1Win_bits hw
  have b1 := window_e1 e T
  have b2 := window_e2 e T
  have b3 := window_e3 e T
  have b4 := window_e4 e T
  have b5 := window_e5 e T
  have b6 := window_e6 e T
  have b7 := window_e7 e T
  have hk7 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega
  rcases hk7 with hk0 | hk1 | hk2 | hk3 | hk4 | hk5 | hk6 | hk7
  · subst k; simp [sign, hA]
  · subst k
    have : e (T - 1) = false := by rw [← b1]; exact bits.1
    simp [sign, this, int_nat1, int_nat2, int_nat3, int_nat4, int_nat5, int_nat6, int_nat7]
  · subst k
    have : e (T - 2) = true := by rw [← b2]; exact bits.2.1
    simp [sign, this, int_nat1, int_nat2, int_nat3, int_nat4, int_nat5, int_nat6, int_nat7]
  · subst k
    have : e (T - 3) = true := by rw [← b3]; exact bits.2.2.1
    simp [sign, this, int_nat1, int_nat2, int_nat3, int_nat4, int_nat5, int_nat6, int_nat7]
  · subst k
    have : e (T - 4) = true := by rw [← b4]; exact bits.2.2.2.1
    simp [sign, this, int_nat1, int_nat2, int_nat3, int_nat4, int_nat5, int_nat6, int_nat7]
  · subst k
    have : e (T - 5) = true := by rw [← b5]; exact bits.2.2.2.2.1
    simp [sign, this, int_nat1, int_nat2, int_nat3, int_nat4, int_nat5, int_nat6, int_nat7]
  · subst k
    have : e (T - 6) = false := by rw [← b6]; exact bits.2.2.2.2.2.1
    simp [sign, this, int_nat1, int_nat2, int_nat3, int_nat4, int_nat5, int_nat6, int_nat7]
  · subst k
    have : e (T - 7) = false := by rw [← b7]; exact bits.2.2.2.2.2.2
    simp [sign, this, int_nat1, int_nat2, int_nat3, int_nat4, int_nat5, int_nat6, int_nat7]

theorem isH2Win_sign (e : Int → Bool) (T : Int)
    (hA : e T = true) (hw : isH2Win (window e T) = true)
    (k : Nat) (hk : k ≤ 7) :
    sign (e (T - (k : Int))) =
      (if k == 0 then (1 : Int)
        else if k == 2 || k == 5 || k == 7 then -1 else 1) := by
  have bits := isH2Win_bits hw
  have b1 := window_e1 e T
  have b2 := window_e2 e T
  have b3 := window_e3 e T
  have b4 := window_e4 e T
  have b5 := window_e5 e T
  have b6 := window_e6 e T
  have b7 := window_e7 e T
  have hk7 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega
  rcases hk7 with hk0 | hk1 | hk2 | hk3 | hk4 | hk5 | hk6 | hk7
  · subst k; simp [sign, hA]
  · subst k
    have : e (T - 1) = true := by rw [← b1]; exact bits.1
    simp [sign, this, int_nat1, int_nat2, int_nat3, int_nat4, int_nat5, int_nat6, int_nat7]
  · subst k
    have : e (T - 2) = false := by rw [← b2]; exact bits.2.1
    simp [sign, this, int_nat1, int_nat2, int_nat3, int_nat4, int_nat5, int_nat6, int_nat7]
  · subst k
    have : e (T - 3) = true := by rw [← b3]; exact bits.2.2.1
    simp [sign, this, int_nat1, int_nat2, int_nat3, int_nat4, int_nat5, int_nat6, int_nat7]
  · subst k
    have : e (T - 4) = true := by rw [← b4]; exact bits.2.2.2.1
    simp [sign, this, int_nat1, int_nat2, int_nat3, int_nat4, int_nat5, int_nat6, int_nat7]
  · subst k
    have : e (T - 5) = false := by rw [← b5]; exact bits.2.2.2.2.1
    simp [sign, this, int_nat1, int_nat2, int_nat3, int_nat4, int_nat5, int_nat6, int_nat7]
  · subst k
    have : e (T - 6) = true := by rw [← b6]; exact bits.2.2.2.2.2.1
    simp [sign, this, int_nat1, int_nat2, int_nat3, int_nat4, int_nat5, int_nat6, int_nat7]
  · subst k
    have : e (T - 7) = false := by rw [← b7]; exact bits.2.2.2.2.2.2
    simp [sign, this, int_nat1, int_nat2, int_nat3, int_nat4, int_nat5, int_nat6, int_nat7]

/-- Forced-bit clash of distinct U7 types at distance `j-i`. The six
`timeClash7` kernel bits lie in these forced positions. -/
theorem phi7_timeClash (e : Int → Bool) (T S : Int)
    (hTA : e T = true) (hSA : e S = true)
    (hTsup : supplied (window e T) = true)
    (hSsup : supplied (window e S) = true)
    (hdelta : S = T + (phi7Off (window e S) : Int) -
      (phi7Off (window e T) : Int))
    (hne : phi7Off (window e T) ≠ phi7Off (window e S)) :
    False := by
  have hTpat := phi7Off_of_supplied (window e T) hTsup
  have hSpat := phi7Off_of_supplied (window e S) hSsup
  have T2 := window_e2 e T
  have T4 := window_e4 e T
  have T6 := window_e6 e T
  have S2 := window_e2 e S
  have S4 := window_e4 e S
  have S6 := window_e6 e S
  rcases hTpat with ⟨hTL3, hToff⟩ | ⟨hTH1, hToff⟩ | ⟨hTH2, hToff⟩
  · rcases hSpat with ⟨hSL3, hSoff⟩ | ⟨hSH1, hSoff⟩ | ⟨hSH2, hSoff⟩
    · exact hne (hToff.trans hSoff.symm)
    · have Tbits := isLag3Win_bits hTL3
      have Sbits := isH1Win_bits hSH1
      rw [hToff, hSoff] at hdelta
      have htime : T - 2 = S - 6 := by omega
      have eT2 : e (T - 2) = true := by rw [← T2]; exact Tbits.2.1
      have eS6 : e (S - 6) = false := by rw [← S6]; exact Sbits.2.2.2.2.2.1
      rw [htime] at eT2
      rw [eT2] at eS6
      cases eS6
    · have Sbits := isH2Win_bits hSH2
      rw [hToff, hSoff] at hdelta
      have htime : T = S - 2 := by omega
      have eS2 : e (S - 2) = false := by rw [← S2]; exact Sbits.2.1
      rw [← htime, hTA] at eS2
      cases eS2
  · rcases hSpat with ⟨hSL3, hSoff⟩ | ⟨hSH1, hSoff⟩ | ⟨hSH2, hSoff⟩
    · have Tbits := isH1Win_bits hTH1
      have Sbits := isLag3Win_bits hSL3
      rw [hToff, hSoff] at hdelta
      have htime : T - 6 = S - 2 := by omega
      have eT6 : e (T - 6) = false := by rw [← T6]; exact Tbits.2.2.2.2.2.1
      have eS2 : e (S - 2) = true := by rw [← S2]; exact Sbits.2.1
      rw [htime] at eT6
      rw [eT6] at eS2
      cases eS2
    · exact hne (hToff.trans hSoff.symm)
    · have Tbits := isH1Win_bits hTH1
      have Sbits := isH2Win_bits hSH2
      rw [hToff, hSoff] at hdelta
      have htime : T - 4 = S - 2 := by omega
      have eT4 : e (T - 4) = true := by rw [← T4]; exact Tbits.2.2.2.1
      have eS2 : e (S - 2) = false := by rw [← S2]; exact Sbits.2.1
      rw [htime] at eT4
      rw [eT4] at eS2
      cases eS2
  · rcases hSpat with ⟨hSL3, hSoff⟩ | ⟨hSH1, hSoff⟩ | ⟨hSH2, hSoff⟩
    · have Tbits := isH2Win_bits hTH2
      rw [hToff, hSoff] at hdelta
      have htime : T - 2 = S := by omega
      have eT2 : e (T - 2) = false := by rw [← T2]; exact Tbits.2.1
      rw [htime, hSA] at eT2
      cases eT2
    · have Tbits := isH2Win_bits hTH2
      have Sbits := isH1Win_bits hSH1
      rw [hToff, hSoff] at hdelta
      have htime : T - 2 = S - 4 := by omega
      have eT2 : e (T - 2) = false := by rw [← T2]; exact Tbits.2.1
      have eS4 : e (S - 4) = true := by rw [← S4]; exact Sbits.2.2.2.1
      rw [htime] at eT2
      rw [eT2] at eS4
      cases eS4
    · exact hne (hToff.trans hSoff.symm)

theorem phi7Phase_inj (e : Int → Bool) (t : Int) {p : Nat}
    (hper : ∀ x : Int, e (x + p) = e x) (hp : 0 < p)
    (i j : Nat) (hi : i < p) (hj : j < p)
    (hAi : e (t + i) = true) (hAj : e (t + j) = true)
    (hsi : supplied (window e (t + i)) = true)
    (hsj : supplied (window e (t + j)) = true)
    (heq : phi7Phase e t p i = phi7Phase e t p j) :
    i = j := by
  have hemod :
      ((i : Int) - phi7Off (window e (t + i))) % p =
        ((j : Int) - phi7Off (window e (t + j))) % p := by
    have hi' := phi7Phase_emod e t hp i
    have hj' := phi7Phase_emod e t hp j
    rw [← hi', ← hj', heq]
  have hdvd : (p : Int) ∣
      ((i : Int) - phi7Off (window e (t + i))) -
        ((j : Int) - phi7Off (window e (t + j))) :=
    Int.dvd_iff_emod_eq_zero.mpr
      ((Int.emod_eq_emod_iff_emod_sub_eq_zero).mp hemod)
  obtain ⟨k, hk⟩ := hdvd
  have hk' :
      ((i : Int) - phi7Off (window e (t + i))) -
        ((j : Int) - phi7Off (window e (t + j))) = k * p := by
    rw [Int.mul_comm] at hk
    exact hk
  by_cases hoffs : phi7Off (window e (t + i)) = phi7Off (window e (t + j))
  · have hij : (i : Int) - j = k * p := by
      rw [hoffs] at hk'
      omega
    have hk0 : k = 0 := by
      have hhi : k * p < p := by
        have : (i : Int) - j < p := by omega
        rw [← hij]; exact this
      have hlo : -((p : Int)) < k * p := by
        have : -((p : Int)) < (i : Int) - j := by omega
        rw [← hij]; exact this
      by_cases hkpos : 0 ≤ k
      · by_cases hz : k = 0
        · exact hz
        · have hk1 : (1 : Int) ≤ k := by omega
          have hle : (1 : Int) * p ≤ k * p :=
            Int.mul_le_mul_of_nonneg_right hk1 (by omega : (0 : Int) ≤ p)
          rw [Int.one_mul] at hle
          omega
      · have hk1 : k ≤ (-1 : Int) := by omega
        have hle : k * p ≤ (-1 : Int) * p :=
          Int.mul_le_mul_of_nonneg_right hk1 (by omega : (0 : Int) ≤ p)
        rw [Int.neg_one_mul] at hle
        omega
    have : (i : Int) = j := by
      rw [hk0] at hij
      omega
    exact Int.ofNat_inj.mp this
  · have hS' :
        (t + i : Int) + phi7Off (window e (t + j)) -
            phi7Off (window e (t + i)) =
          (t + j) + k * p := by
      omega
    have heS' : e ((t + i : Int) + phi7Off (window e (t + j)) -
        phi7Off (window e (t + i))) = true := by
      have hsh := e_shift e p hper k (t + j)
      rw [hS']
      simpa using hsh.trans hAj
    have hwin' :
        window e ((t + i : Int) + phi7Off (window e (t + j)) -
            phi7Off (window e (t + i))) =
          window e (t + j) := by
      have hsh := window_shift e p hper (t + j) k
      rw [hS']
      exact hsh
    have hsupS' : supplied (window e ((t + i : Int) +
        phi7Off (window e (t + j)) -
        phi7Off (window e (t + i)))) = true := by
      simpa [hwin'] using hsj
    have hne : phi7Off (window e (t + i)) ≠
        phi7Off (window e ((t + i : Int) +
          phi7Off (window e (t + j)) -
          phi7Off (window e (t + i)))) := by
      simpa [hwin'] using hoffs
    have hdelta :
        (t + i : Int) + phi7Off (window e (t + j)) -
            phi7Off (window e (t + i)) =
          (t + i) +
            phi7Off (window e ((t + i : Int) +
              phi7Off (window e (t + j)) -
              phi7Off (window e (t + i)))) -
            phi7Off (window e (t + i)) := by
      simp [hwin']
    exact (phi7_timeClash e (t + i)
      ((t + i : Int) + phi7Off (window e (t + j)) -
        phi7Off (window e (t + i)))
      hAi heS' hsi hsupS' hdelta hne).elim

theorem u7_images_subset_sub (e : Int → Bool) (t : Int) {p : Nat}
    (hper : ∀ x : Int, e (x + p) = e x) (hp : 0 < p) :
    (u7Phases e t p).map (phi7Phase e t p) ⊆ subPhases e t p := by
  intro y hy
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy
  have ⟨hip, hA, hsup⟩ := (mem_u7Phases e t p i).mp hi
  have hs := phi7Phase_is_sub e t hper hp i hA hsup
  have hlt := phi7Phase_lt e t hp i
  exact (mem_subPhases e t p _).mpr ⟨hlt, hs⟩

theorem u7_images_nodup (e : Int → Bool) (t : Int) {p : Nat}
    (hper : ∀ x : Int, e (x + p) = e x) (hp : 0 < p) :
    ((u7Phases e t p).map (phi7Phase e t p)).Nodup := by
  refine nodup_map_of_inj (List.Nodup.sublist List.filter_sublist List.nodup_range) ?_
  intro a b ha hb hf
  have ha' := (mem_u7Phases e t p a).mp ha
  have hb' := (mem_u7Phases e t p b).mp hb
  exact phi7Phase_inj e t hper hp a b ha'.1 hb'.1 ha'.2.1 hb'.2.1 ha'.2.2 hb'.2.2 hf

theorem u7Blocked_parts {offs : List Nat} (h : offs ∈ types) :
    (lag3Contradicts offs (charge offs) = true ∧
      lag7h1Contradicts offs (charge offs) = true) ∧
        lag7h2Contradicts offs (charge offs) = true := by
  have hall := List.all_eq_true.mp charge_u7_blocked
  have hb : u7Blocked offs (charge offs) = true := hall offs h
  unfold u7Blocked at hb
  simpa [Bool.and_eq_true] using hb

theorem contradicts_true {offs : List Nat} {off : Nat} {val : Int}
    (h : contradicts offs off val = true) :
    off ≤ 11 ∧ signOff offs off ≠ val := by
  simpa [contradicts, decide_eq_true_eq] using h

theorem contradicts_false_of_eq {offs : List Nat} {off : Nat} {val : Int}
    (h : off ≤ 11 → signOff offs off = val) :
    contradicts offs off val = false := by
  unfold contradicts
  by_cases hle : off ≤ 11
  · have : ¬ (off ≤ 11 ∧ signOff offs off ≠ val) := by
      intro ⟨_, hne⟩
      exact hne (h hle)
    exact decide_eq_false this
  · have : ¬ (off ≤ 11 ∧ signOff offs off ≠ val) :=
      fun ⟨hle', _⟩ => hle hle'
    exact decide_eq_false this

theorem u7_blocked_by_window (e : Int → Bool) (U T : Int)
    (hUA : e U = true) (hTA : e T = true)
    (hmin : minLag11At e U)
    (hsup : supplied (window e T) = true)
    (hrel : T = U - (charge (typeOf (maskAt e U)) : Int) +
      (phi7Off (window e T) : Int)) :
    False := by
  have ⟨hmem, _hmask⟩ := typeOf_spec (maskAt e U) (maskAt_lt e U)
    ((minLag11At_iff e U).mpr hmin)
  have ⟨⟨hL3, hH1⟩, hH2⟩ := u7Blocked_parts hmem
  have hcb := of_decide_eq_true (List.all_eq_true.mp charge_bounds _ hmem)
  have hch3 : 3 ≤ charge (typeOf (maskAt e U)) := hcb.1
  have hch11 : charge (typeOf (maskAt e U)) ≤ 11 := hcb.2
  rcases phi7Off_of_supplied (window e T) hsup with ⟨hw3, hoff⟩ | ⟨hw1, hoff⟩ | ⟨hw2, hoff⟩
  · rw [hoff] at hrel
    have bits := isLag3Win_bits hw3
    have e1 : e (T - 1) = true := by
      have h := window_e1 e T
      rw [← h]; exact bits.1
    have e2 : e (T - 2) = true := by
      have h := window_e2 e T
      rw [← h]; exact bits.2.1
    have e3 : e (T - 3) = false := by
      have h := window_e3 e T
      rw [← h]; exact bits.2.2
    have c0 : contradicts (typeOf (maskAt e U))
        (charge (typeOf (maskAt e U)) - 3) 1 = false := by
      apply contradicts_false_of_eq
      intro _hle
      have hsign := signOff_typeAt e U (charge (typeOf (maskAt e U)) - 3)
        hUA hmin (by omega)
      have hcast : ((charge (typeOf (maskAt e U)) - 3 : Nat) : Int) =
          (charge (typeOf (maskAt e U)) : Int) - 3 := by omega
      have htime : U - ((charge (typeOf (maskAt e U)) - 3 : Nat) : Int) = T := by
        rw [hcast, hrel]; omega
      rw [hsign, htime, sign, hTA]; simp
    have c1 : contradicts (typeOf (maskAt e U))
        (charge (typeOf (maskAt e U)) - 2) 1 = false := by
      apply contradicts_false_of_eq
      intro _hle
      have hsign := signOff_typeAt e U (charge (typeOf (maskAt e U)) - 2)
        hUA hmin (by omega)
      have hcast : ((charge (typeOf (maskAt e U)) - 2 : Nat) : Int) =
          (charge (typeOf (maskAt e U)) : Int) - 2 := by omega
      have htime : U - ((charge (typeOf (maskAt e U)) - 2 : Nat) : Int) =
          T - 1 := by
        rw [hcast, hrel]; omega
      rw [hsign, htime, sign, e1]; simp
    have c2 : contradicts (typeOf (maskAt e U))
        (charge (typeOf (maskAt e U)) - 1) 1 = false := by
      apply contradicts_false_of_eq
      intro _hle
      have hsign := signOff_typeAt e U (charge (typeOf (maskAt e U)) - 1)
        hUA hmin (by omega)
      have hcast : ((charge (typeOf (maskAt e U)) - 1 : Nat) : Int) =
          (charge (typeOf (maskAt e U)) : Int) - 1 := by omega
      have htime : U - ((charge (typeOf (maskAt e U)) - 1 : Nat) : Int) =
          T - 2 := by
        rw [hcast, hrel]; omega
      rw [hsign, htime, sign, e2]; simp
    have c3 : contradicts (typeOf (maskAt e U))
        (charge (typeOf (maskAt e U))) (-1) = false := by
      apply contradicts_false_of_eq
      intro _hle
      have hsign := signOff_typeAt e U (charge (typeOf (maskAt e U)))
        hUA hmin hch11
      have htime : U - (charge (typeOf (maskAt e U)) : Int) = T - 3 := by
        rw [hrel]; omega
      rw [hsign, htime, sign, e3]; simp
    have hf : lag3Contradicts (typeOf (maskAt e U))
        (charge (typeOf (maskAt e U))) = false := by
      unfold lag3Contradicts
      have d3 : decide (3 ≤ charge (typeOf (maskAt e U))) = true :=
        decide_eq_true hch3
      have d2 : decide (2 ≤ charge (typeOf (maskAt e U))) = true :=
        decide_eq_true (Nat.le_trans (by decide : 2 ≤ 3) hch3)
      have d1 : decide (1 ≤ charge (typeOf (maskAt e U))) = true :=
        decide_eq_true (Nat.le_trans (by decide : 1 ≤ 3) hch3)
      simp [c0, c1, c2, c3, d3, d2, d1]
    rw [hf] at hL3
    cases hL3
  · rw [hoff] at hrel
    obtain ⟨k, hkmem, hbit⟩ := List.any_eq_true.mp hH1
    have hk : k < 8 := List.mem_range.mp hkmem
    have hk7 : k ≤ 7 := by omega
    let off : Int := (charge (typeOf (maskAt e U)) : Int) - 7 + k
    let val : Int :=
      if k == 0 then (1 : Int)
      else if k == 1 || k == 6 || k == 7 then -1 else 1
    have hbit' :
        (0 ≤ off ∧ off ≤ 11) ∧
          contradicts (typeOf (maskAt e U)) off.toNat val = true := by
      simpa [off, val, Bool.and_eq_true, decide_eq_true_eq] using hbit
    have hc' := contradicts_true hbit'.2
    have hs0 : 0 ≤ off := hbit'.1.1
    have hto : (off.toNat : Int) = off := Int.toNat_of_nonneg hs0
    have hoff11 : off.toNat ≤ 11 := by
      have : off ≤ 11 := hbit'.1.2
      omega
    have hsign := signOff_typeAt e U off.toNat hUA hmin hoff11
    have htime : U - (off.toNat : Int) = T - (k : Int) := by
      rw [hto]
      dsimp only [off]
      omega
    have hpat := isH1Win_sign e T hTA hw1 k hk7
    have : signOff (typeOf (maskAt e U)) off.toNat = val := by
      rw [hsign, htime]
      exact hpat
    exact hc'.2 this
  · rw [hoff] at hrel
    obtain ⟨k, hkmem, hbit⟩ := List.any_eq_true.mp hH2
    have hk : k < 8 := List.mem_range.mp hkmem
    have hk7 : k ≤ 7 := by omega
    let off : Int := (charge (typeOf (maskAt e U)) : Int) - 5 + k
    let val : Int :=
      if k == 0 then (1 : Int)
      else if k == 2 || k == 5 || k == 7 then -1 else 1
    have hbit' :
        (0 ≤ off ∧ off ≤ 11) ∧
          contradicts (typeOf (maskAt e U)) off.toNat val = true := by
      simpa [off, val, Bool.and_eq_true, decide_eq_true_eq] using hbit
    have hc' := contradicts_true hbit'.2
    have hs0 : 0 ≤ off := hbit'.1.1
    have hto : (off.toNat : Int) = off := Int.toNat_of_nonneg hs0
    have hoff11 : off.toNat ≤ 11 := by
      have : off ≤ 11 := hbit'.1.2
      omega
    have hsign := signOff_typeAt e U off.toNat hUA hmin hoff11
    have htime : U - (off.toNat : Int) = T - (k : Int) := by
      rw [hto]
      dsimp only [off]
      omega
    have hpat := isH2Win_sign e T hTA hw2 k hk7
    have : signOff (typeOf (maskAt e U)) off.toNat = val := by
      rw [hsign, htime]
      exact hpat
    exact hc'.2 this

theorem phi7_phi11_image_ne (e : Int → Bool) (t : Int) {p : Nat}
    (hper : ∀ x : Int, e (x + p) = e x) (hp : 0 < p)
    (i j : Nat) (_hi : i < p) (_hj : j < p)
    (hAi : e (t + i) = true) (hAj : e (t + j) = true)
    (hsup : supplied (window e (t + i)) = true)
    (hmin : minLag11 (maskAt e (t + j)) = true)
    (heq : phi7Phase e t p i = phi11Phase e t p j) :
    False := by
  have hemod :
      ((i : Int) - phi7Off (window e (t + i))) % p =
        ((j : Int) - charge (typeOf (maskAt e (t + j)))) % p := by
    have hi' := phi7Phase_emod e t hp i
    have hj' := phi11Phase_emod e t hp j
    rw [← hi', ← hj', heq]
  have hdvd : (p : Int) ∣
      ((i : Int) - phi7Off (window e (t + i))) -
        ((j : Int) - charge (typeOf (maskAt e (t + j)))) :=
    Int.dvd_iff_emod_eq_zero.mpr
      ((Int.emod_eq_emod_iff_emod_sub_eq_zero).mp hemod)
  obtain ⟨k, hk⟩ := hdvd
  have hk' :
      ((i : Int) - phi7Off (window e (t + i))) -
        ((j : Int) - charge (typeOf (maskAt e (t + j)))) = k * p := by
    rw [Int.mul_comm] at hk
    exact hk
  have hT' :
      (t + i : Int) - k * p =
        (t + j) - charge (typeOf (maskAt e (t + j))) +
          phi7Off (window e (t + i)) := by
    omega
  have heT' : e ((t + i : Int) - k * p) = true := by
    have hsh := e_shift e p hper (-k) (t + i)
    have : (t + i : Int) + (-k) * p = (t + i) - k * p := by
      simp [Int.neg_mul]
      omega
    rw [← this]
    simpa using hsh.trans hAi
  have hwin' : window e ((t + i : Int) - k * p) = window e (t + i) := by
    have hsh := window_shift e p hper (t + i) (-k)
    have : (t + i : Int) + (-k) * p = (t + i) - k * p := by
      simp [Int.neg_mul]
      omega
    rw [← this]
    exact hsh
  have hsup' : supplied (window e ((t + i : Int) - k * p)) = true := by
    simpa [hwin'] using hsup
  have hminU : minLag11At e (t + j) := (minLag11At_iff e (t + j)).mp hmin
  have hrel :
      (t + i : Int) - k * p =
        (t + j) - charge (typeOf (maskAt e (t + j))) +
          phi7Off (window e ((t + i : Int) - k * p)) := by
    simpa [hwin'] using hT'
  exact u7_blocked_by_window e (t + j) ((t + i : Int) - k * p)
    hAj heT' hminU hsup' hrel

theorem nodup_append {l₁ l₂ : List Nat}
    (h₁ : l₁.Nodup) (h₂ : l₂.Nodup)
    (h : ∀ a, a ∈ l₁ → a ∉ l₂) : (l₁ ++ l₂).Nodup := by
  induction l₁ with
  | nil => simpa
  | cons x xs ih =>
    rw [List.nodup_cons] at h₁
    rw [List.cons_append, List.nodup_cons]
    constructor
    · intro hx
      have hx' := List.mem_append.mp hx
      rcases hx' with hxs | hl2
      · exact h₁.1 hxs
      · exact h x List.mem_cons_self hl2
    · exact ih h₁.2 (fun a ha => h a (List.mem_cons_of_mem _ ha))

theorem phi7_phi11_images_disjoint (e : Int → Bool) (t : Int) {p : Nat}
    (hper : ∀ x : Int, e (x + p) = e x) (hp : 0 < p)
    {y : Nat}
    (h7 : y ∈ (u7Phases e t p).map (phi7Phase e t p))
    (h11 : y ∈ (u11Phases e t p).map (phi11Phase e t p)) :
    False := by
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp h7
  obtain ⟨j, hj, heq⟩ := List.mem_map.mp h11
  have hi' := (mem_u7Phases e t p i).mp hi
  have hj' := (mem_u11Phases e t p j).mp hj
  exact phi7_phi11_image_ne e t hper hp i j hi'.1 hj'.1 hi'.2.1 hj'.2.1
    hi'.2.2 hj'.2.2 heq.symm

/-- All-period capacity: `|U7 ∪ U11min| ≤ |D|`. Stronger than E-071. -/
theorem suppliedCount_add_u11Count_le_subtractionCount
    (e : Int → Bool) (t : Int) {p : Nat}
    (hper : ∀ x : Int, e (x + p) = e x) (hp : 0 < p) :
    suppliedCount e t p + u11Count e t p ≤ subtractionCount e t p := by
  have h7nodup := u7_images_nodup e t hper hp
  have h11nodup := u11_images_nodup e t hper hp
  have h7sub := u7_images_subset_sub e t hper hp
  have h11sub := u11_images_subset_sub e t hper hp
  have hdisj : ∀ a, a ∈ (u7Phases e t p).map (phi7Phase e t p) →
      a ∉ (u11Phases e t p).map (phi11Phase e t p) :=
    fun a ha h11 => phi7_phi11_images_disjoint e t hper hp ha h11
  have hnodup := nodup_append h7nodup h11nodup hdisj
  have hsub :
      ((u7Phases e t p).map (phi7Phase e t p) ++
        (u11Phases e t p).map (phi11Phase e t p)) ⊆ subPhases e t p :=
    List.append_subset.mpr ⟨h7sub, h11sub⟩
  have hlen := hnodup.length_le_of_subset hsub
  have hmap : ((u7Phases e t p).map (phi7Phase e t p) ++
      (u11Phases e t p).map (phi11Phase e t p)).length =
      (u7Phases e t p).length + (u11Phases e t p).length := by
    simp [List.length_append, List.length_map]
  rw [hmap] at hlen
  simpa [suppliedCount_eq_filter, u11Count_eq_filter,
    subtractionCount_eq_filter] using hlen

end Recaman.LagElevenPeriodic
