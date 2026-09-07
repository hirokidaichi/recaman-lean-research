namespace Recaman.ShortPeriodicSupply

/-! # Short supplier capacity for arbitrary periodic sign words

An addition has a P2 supplier at lag d if the preceding signs have sum one
and backward first moment zero. This module proves, for every period length,
that the number of additions with a supplier at lag at most seven is at most
the number of subtractions. Consequently a positive-sum period has an addition
without such a short supplier. Suppliers at longer lags remain possible.

The explicit potential below was found on the seven-bit shift graph. Lean
checks every local inequality with `decide`; the proof then constructs the
window from the actual periodic signs and telescopes. Thus neither a fixed
period census nor an assumed opaque automaton path replaces the word claim.
The independent paper proof charges the three minimal short patterns to
subtractions with distinct following-gap types: at least four, one, and three.
No Recamán reachability or subtraction-freshness assumption is present.
-/

def sign (b : Bool) : Int := if b then 1 else -1
abbrev Window := Fin 128

def lagSum (s : Window) (d : Nat) : Int :=
  ((List.range d).map fun i => sign (s.val.testBit i)).sum

def lagMoment (s : Window) (d : Nat) : Int :=
  ((List.range d).map fun i => (i+1 : Nat) * sign (s.val.testBit i)).sum

def supplied (s : Window) : Bool :=
  (List.range 7).any fun k => decide (lagSum s (k+1) = 1 ∧ lagMoment s (k+1) = 0)

def advance (s : Window) (b : Bool) : Window :=
  ⟨(2*s.val + if b then 1 else 0) % 128, Nat.mod_lt _ (by decide)⟩

def charge (s : Window) (b : Bool) : Int :=
  if b then (if supplied s then 1 else 0) else -1

def potential (s : Window) : Int :=
  if s.val ∈ [55, 63, 95, 111, 119, 127] then 2 else if s.val ∈ [7, 15, 23, 31, 39, 47, 59, 61, 62, 71, 79, 87, 91, 93, 94, 103, 110, 123, 125, 126] then 1 else 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem potential_step : ∀ (s : Window) (b : Bool),
    potential s + charge s b ≤ potential (advance s b) := by
  decide



def bitValue (b : Bool) : Nat := if b then 1 else 0

def encode (b0 b1 b2 b3 b4 b5 b6 : Bool) : Window :=
  ⟨(bitValue b0 + 2*bitValue b1 + 4*bitValue b2 + 8*bitValue b3 +
    16*bitValue b4 + 32*bitValue b5 + 64*bitValue b6) % 128,
    Nat.mod_lt _ (by decide)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem encode_advance : ∀ (b0 b1 b2 b3 b4 b5 b6 b : Bool),
    advance (encode b0 b1 b2 b3 b4 b5 b6) b = encode b b0 b1 b2 b3 b4 b5 := by
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem encode_bits : ∀ (b0 b1 b2 b3 b4 b5 b6 : Bool) (i : Fin 7),
    (encode b0 b1 b2 b3 b4 b5 b6).val.testBit i.val =
      [b0,b1,b2,b3,b4,b5,b6][i.val]'(by exact i.isLt) := by
  decide

/-- The seven actual signs preceding the step at integer clock t, newest first. -/
def window (e : Int → Bool) (t : Int) : Window :=
  encode (e (t-1)) (e (t-2)) (e (t-3)) (e (t-4)) (e (t-5)) (e (t-6)) (e (t-7))

theorem window_advance (e : Int → Bool) (t : Int) :
    advance (window e t) (e t) = window e (t+1) := by
  have h := encode_advance (e (t-1)) (e (t-2)) (e (t-3)) (e (t-4))
    (e (t-5)) (e (t-6)) (e (t-7)) (e t)
  have h1 : t+1-1=t := by omega
  have h2 : t+1-2=t-1 := by omega
  have h3 : t+1-3=t-2 := by omega
  have h4 : t+1-4=t-3 := by omega
  have h5 : t+1-5=t-4 := by omega
  have h6 : t+1-6=t-5 := by omega
  have h7 : t+1-7=t-6 := by omega
  simpa only [window, h1,h2,h3,h4,h5,h6,h7] using h

theorem window_bit (e : Int → Bool) (t : Int) (i : Nat) (hi : i < 7) :
    (window e t).val.testBit i = e (t - ((i+1 : Nat) : Int)) := by
  have h := encode_bits (e (t-1)) (e (t-2)) (e (t-3)) (e (t-4))
    (e (t-5)) (e (t-6)) (e (t-7)) ⟨i,hi⟩
  have casesI : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 := by omega
  rcases casesI with h0 | h1 | h2 | h3 | h4 | h5 | h6
  all_goals subst i; simpa [window] using h

theorem window_lagSum (e : Int → Bool) (t : Int) (d : Nat) (hd : d ≤ 7) :
    lagSum (window e t) d =
      ((List.range d).map fun i => sign (e (t - ((i+1 : Nat) : Int)))).sum := by
  unfold lagSum
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [window_bit e t i (by have := List.mem_range.mp hi; omega)]

theorem window_lagMoment (e : Int → Bool) (t : Int) (d : Nat) (hd : d ≤ 7) :
    lagMoment (window e t) d =
      ((List.range d).map fun i => ((i+1 : Nat) : Int) * sign (e (t - ((i+1 : Nat) : Int)))).sum := by
  unfold lagMoment
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [window_bit e t i (by have := List.mem_range.mp hi; omega)]

/-- The two exact backward identities; no greedy-orbit hypothesis is hidden here. -/
def P2 (e : Int → Bool) (t : Int) (d : Nat) : Prop :=
  ((List.range d).map fun i => sign (e (t - ((i+1 : Nat) : Int)))).sum = 1 ∧
  ((List.range d).map fun i => ((i+1 : Nat) : Int) * sign (e (t - ((i+1 : Nat) : Int)))).sum = 0

theorem supplied_window_iff (e : Int → Bool) (t : Int) :
    supplied (window e t) = true ↔ ∃ d : Nat, 1 ≤ d ∧ d ≤ 7 ∧ P2 e t d := by
  simp only [supplied, List.any_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨k,hk,hs,hm⟩
    have hk' := List.mem_range.mp hk
    refine ⟨k+1,by omega,by omega,?_,?_⟩
    · simpa only [window_lagSum e t (k+1) (by omega)] using hs
    · simpa only [window_lagMoment e t (k+1) (by omega)] using hm
  · rintro ⟨d,hd0,hd7,hs,hm⟩
    refine ⟨d-1,List.mem_range.mpr (by omega),?_,?_⟩
    · rw [show d-1+1=d by omega, window_lagSum e t d hd7]
      exact hs
    · rw [show d-1+1=d by omega, window_lagMoment e t d hd7]
      exact hm



/-- Number of supplied additions in clocks t through t+n-1. -/
def suppliedCount (e : Int → Bool) (t : Int) : Nat → Nat
  | 0 => 0
  | n+1 => suppliedCount e t n +
      if e (t+n) && supplied (window e (t+n)) then 1 else 0

def subtractionCount (e : Int → Bool) (t : Int) : Nat → Nat
  | 0 => 0
  | n+1 => subtractionCount e t n + if e (t+n) then 0 else 1

def additionCount (e : Int → Bool) (t : Int) : Nat → Nat
  | 0 => 0
  | n+1 => additionCount e t n + if e (t+n) then 1 else 0

def signSum (e : Int → Bool) (t : Int) : Nat → Int
  | 0 => 0
  | n+1 => signSum e t n + sign (e (t+n))

def chargeSum (e : Int → Bool) (t : Int) : Nat → Int
  | 0 => 0
  | n+1 => chargeSum e t n + charge (window e (t+n)) (e (t+n))

theorem signSum_eq_counts (e : Int → Bool) (t : Int) (n : Nat) :
    signSum e t n = (additionCount e t n : Int) - (subtractionCount e t n : Int) := by
  induction n with
  | zero => simp [signSum, additionCount, subtractionCount]
  | succ n ih =>
    cases hb : e (t+n) <;>
      simp [signSum, additionCount, subtractionCount, sign, hb, ih] <;> omega

theorem chargeSum_eq_counts (e : Int → Bool) (t : Int) (n : Nat) :
    chargeSum e t n = (suppliedCount e t n : Int) - (subtractionCount e t n : Int) := by
  induction n with
  | zero => simp [chargeSum, suppliedCount, subtractionCount]
  | succ n ih =>
    cases hb : e (t+n) <;> cases hs : supplied (window e (t+n)) <;>
      simp [chargeSum, suppliedCount, subtractionCount, charge, hb, hs, ih] <;> omega

/-- Telescoping the checked potential along the actual seven preceding signs. -/
theorem chargeSum_le_potential (e : Int → Bool) (t : Int) (n : Nat) :
    chargeSum e t n ≤ potential (window e (t+n)) - potential (window e t) := by
  induction n with
  | zero => simp [chargeSum]
  | succ n ih =>
    have h := potential_step (window e (t+n)) (e (t+n))
    rw [window_advance] at h
    have hc : t + ((n+1 : Nat) : Int) = t+n+1 := by omega
    rw [chargeSum, hc]
    omega

theorem window_periodic (e : Int → Bool) (p : Nat)
    (hp : ∀ x : Int, e (x+p) = e x) (t : Int) :
    window e (t+p) = window e t := by
  have h (i : Int) : e (t+p-i) = e (t-i) := by
    rw [show t+p-i = (t-i)+p by omega]
    exact hp (t-i)
  simp only [window, h]

/-- All periods, with no limit on period length: short supplied A phases cannot
outnumber S phases. The only lag bound is the explicit seven in supplied_window_iff. -/
theorem periodic_capacity (e : Int → Bool) (p : Nat)
    (hp : ∀ x : Int, e (x+p) = e x) (t : Int) :
    suppliedCount e t p ≤ subtractionCount e t p := by
  have h := chargeSum_le_potential e t p
  rw [window_periodic e p hp t, chargeSum_eq_counts] at h
  omega

theorem suppliedCount_eq_additionCount_of_all (e : Int → Bool) (t : Int) (n : Nat)
    (hall : ∀ i : Nat, i < n → e (t+i) = true → supplied (window e (t+i)) = true) :
    suppliedCount e t n = additionCount e t n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hprev := ih (fun i hi hb => hall i (by omega) hb)
    have hhere := hall n (by omega)
    cases hb : e (t+n)
    · simp [suppliedCount, additionCount, hb, hprev]
    · have hs := hhere hb
      simp [suppliedCount, additionCount, hb, hs, hprev]

/-- A positive-sum periodic sign word always has an A phase without any P2 lag
from 1 through 7. This does not exclude a supplier at a longer lag. -/
theorem exists_phase_without_short_supply (e : Int → Bool) (p : Nat)
    (hp : ∀ x : Int, e (x+p) = e x) (t : Int) (hpos : 0 < signSum e t p) :
    ∃ i : Nat, i < p ∧ e (t+i) = true ∧
      ¬ ∃ d : Nat, 1 ≤ d ∧ d ≤ 7 ∧ P2 e (t+i) d := by
  classical
  apply Classical.byContradiction
  intro hnot
  have hall : ∀ i : Nat, i < p → e (t+i) = true → supplied (window e (t+i)) = true := by
    intro i hi hb
    cases hs : supplied (window e (t+i))
    · have hn : ¬ ∃ d : Nat, 1 ≤ d ∧ d ≤ 7 ∧ P2 e (t+i) d := by
        intro hex
        have he := (supplied_window_iff e (t+i)).mpr hex
        rw [hs] at he
        contradiction
      exact False.elim (hnot ⟨i,hi,hb,hn⟩)
    · rfl
  have heq := suppliedCount_eq_additionCount_of_all e t p hall
  have hle := periodic_capacity e p hp t
  have hsum := signSum_eq_counts e t p
  omega

/-- A periodic word where a longer supplier exists despite no short supplier. -/
def longLagControl (t : Int) : Bool :=
  [false,false,false,false,true,true,true,true,false,true,true,true][(t % 12).toNat]!

/-- Semantic guard: the short-lag theorem must not be read as all-lag exclusion. -/
theorem lag_eleven_survives_short_exclusion :
    P2 longLagControl 7 11 ∧
      ¬ ∃ d : Nat, 1 ≤ d ∧ d ≤ 7 ∧ P2 longLagControl 7 d := by
  constructor
  · unfold P2
    decide
  · rw [← supplied_window_iff]
    decide

end Recaman.ShortPeriodicSupply
