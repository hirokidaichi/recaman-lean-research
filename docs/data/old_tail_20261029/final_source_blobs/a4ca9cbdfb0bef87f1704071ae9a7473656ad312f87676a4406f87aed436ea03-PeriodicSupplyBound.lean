import Recaman.LeadingRunSupply
import Recaman.ParitySupply

namespace Recaman.PeriodicSupplyBound

open LeadingRunSupply

/-! # Positive period drift bounds every P2 supplier lag

Let `e : Int → Bool` be a sign word (`true` is an addition, `false` a
subtraction) that is periodic with period `p`. Reading backwards from a clock
`t`, the word `past e t d` records the `d` signs immediately preceding `t`, and
`mass` is their signed sum. A P2 supplier at lag `d` is a backward window whose
mass is one and whose first moment vanishes, which is the predicate
`ShortPeriodicSupply.P2 e t d`.

The quantity that controls how far back a supplier can hide is the mass of one
full period,

    `periodMass e p = mass (past e 0 p)`.

Periodicity makes this independent of the phase (`period_mass_const`), so the
backward mass of `k` whole periods is exactly `k * periodMass e p`
(`mass_past_mul_period`). When `periodMass e p` is nonnegative the residual
block of fewer than `p` signs can subtract at most `p - 1`, hence every backward
window has mass strictly above `-(p : Int)` (`mass_past_lower`). That is a drift
statement: once the backward mass has climbed to `p + 1` it can never return to
the value `1` required by P2 (`no_return_of_large`).

Taking `k = p + 1` whole periods, a strictly positive `periodMass e p` pushes the
backward mass to at least `p + 1` by lag `p * (p + 1)`. Therefore a phase with a
P2 supplier at some lag already has one at a lag at most `p * (p + 1)`
(`supply_lag_bound`), and dually a finite scan that finds no supplier up to that
lag proves there is no supplier at any lag whatsoever
(`unsupplied_of_bounded_check`).

Why this module exists: every computational search in this project for periodic
supply counterexamples stops its backward scan using exactly this drift
criterion, but the criterion itself had not been checked by Lean. With this
module a claim of the form "phase `t` of this periodic word has no P2 supplier"
becomes a finite, kernel-checkable statement, and the lag bound
`d ≤ p * (p + 1)` is *derived* from positivity of the period mass rather than
being taken for granted. Nothing here refers to Recamán reachability; the input
is the sign word alone.
-/

/-- Signed mass of one full period, read backwards from clock zero. -/
def periodMass (e : Int → Bool) (p : Nat) : Int := mass (past e 0 p)

/-! ## The period window has a phase-independent mass -/

/-- Advancing the clock by one rotates the length-`p` backward window: the sign
`e t` enters at the front and the sign `e (t - p)` leaves at the back, and those
two signs agree by periodicity. -/
theorem window_mass_shift (e : Int → Bool) (p : Nat)
    (hper : ∀ x : Int, e (x + p) = e x) (t : Int) :
    mass (past e (t+1) p) = mass (past e t p) := by
  have hleft := ParitySupply.past_succ e (t+1) p
  have ht : t+1-1 = t := by omega
  rw [ht] at hleft
  have hright := past_append e (t+1) p 1
  have he := hper (t - (p : Int))
  have hepos : t - (p : Int) + p = t := by omega
  rw [hepos] at he
  have hlast : mass (past e (t+1-(p : Nat)) 1) = ShortPeriodicSupply.sign (e t) := by
    have hs : t+1-(p : Int)-1 = t - (p : Int) := by omega
    simp [past, hs, ← he]
  have hlm := congrArg mass hleft
  have hrm := congrArg mass hright
  simp only [mass_append, mass_cons] at hlm hrm
  rw [hlast] at hrm
  omega

/-- The same rotation read the other way. -/
theorem window_mass_shift_down (e : Int → Bool) (p : Nat)
    (hper : ∀ x : Int, e (x + p) = e x) (t : Int) :
    mass (past e (t-1) p) = mass (past e t p) := by
  have h := window_mass_shift e p hper (t-1)
  have ht : t-1+1 = t := by omega
  rw [ht] at h
  omega

theorem period_mass_const_nat (e : Int → Bool) (p : Nat)
    (hper : ∀ x : Int, e (x + p) = e x) (n : Nat) :
    mass (past e (n : Int) p) = periodMass e p := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hc : ((n+1 : Nat) : Int) = (n : Int) + 1 := by omega
    rw [hc]
    exact (window_mass_shift e p hper (n : Int)).trans ih

theorem period_mass_const_neg (e : Int → Bool) (p : Nat)
    (hper : ∀ x : Int, e (x + p) = e x) (n : Nat) :
    mass (past e (-(n : Int)) p) = periodMass e p := by
  induction n with
  | zero => show mass (past e 0 p) = periodMass e p; rfl
  | succ n ih =>
    have h := window_mass_shift_down e p hper (-(n : Int))
    have ht : -(n : Int) - 1 = -((n+1 : Nat) : Int) := by omega
    rw [ht] at h
    omega

/-- Every phase sees the same period mass. -/
theorem period_mass_const (e : Int → Bool) (p : Nat)
    (hper : ∀ x : Int, e (x + p) = e x) (t : Int) :
    mass (past e t p) = periodMass e p := by
  cases t with
  | ofNat n => exact period_mass_const_nat e p hper n
  | negSucc n =>
    have h := period_mass_const_neg e p hper (n+1)
    have ht : (-((n+1 : Nat) : Int)) = Int.negSucc n := rfl
    rw [ht] at h
    exact h

/-! ## Backward mass of whole periods, and the drift floor -/

/-- `k` whole periods of history carry exactly `k` copies of the period mass. -/
theorem mass_past_mul_period (e : Int → Bool) (p : Nat)
    (hper : ∀ x : Int, e (x + p) = e x) (t : Int) (k : Nat) :
    mass (past e t (k * p)) = (k : Int) * periodMass e p := by
  induction k with
  | zero => simp [past]
  | succ k ih =>
    have hsplit := past_append e t (k*p) p
    rw [← Nat.succ_mul] at hsplit
    rw [hsplit, mass_append, ih, period_mass_const e p hper]
    have hc : ((k+1 : Nat) : Int) = (k : Int) + 1 := by omega
    rw [hc, Int.add_mul, Int.one_mul]

/-- The crudest possible floor: a window of `d` signs has mass at least `-d`. -/
theorem mass_past_ge_neg (e : Int → Bool) (t : Int) (d : Nat) :
    -(d : Int) ≤ mass (past e t d) := by
  have hlen : (past e t d).length = d := by simp [past]
  have hb := ones_bounds (past e t d)
  have hm := mass_eq (past e t d)
  rw [hlen] at hb hm
  omega

/-- Nonnegative period drift gives a floor independent of the lag: no backward
window ever dips to `-(p : Int)` or below, because the whole-period part
contributes nonnegatively and the residual part is shorter than `p`. -/
theorem mass_past_lower (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x) (hmass : 0 ≤ periodMass e p)
    (t : Int) (d : Nat) : -(p : Int) < mass (past e t d) := by
  have hdm := Nat.div_add_mod d p
  have he : d/p*p + d%p = d := by rw [Nat.mul_comm (d/p) p]; exact hdm
  have hsplit : past e t d = past e t (d/p*p) ++ past e (t - (d/p*p : Nat)) (d%p) := by
    have h := past_append e t (d/p*p) (d%p)
    rw [he] at h
    exact h
  rw [hsplit, mass_append, mass_past_mul_period e p hper t (d/p)]
  have h1 : 0 ≤ ((d/p : Nat) : Int) * periodMass e p :=
    Int.mul_nonneg (Int.natCast_nonneg (d/p)) hmass
  have h2 := mass_past_ge_neg e (t - (d/p*p : Nat)) (d%p)
  have h3 : d % p < p := Nat.mod_lt _ hp
  omega

/-! ## The termination criterion -/

/-- Once the backward mass has risen to `p + 1` it cannot come back down to the
P2 value `1` at any longer lag: extending the window can cost strictly less than
`p`. This is the criterion that lets a backward scan stop. -/
theorem no_return_of_large (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x) (hmass : 0 ≤ periodMass e p)
    (t : Int) (d d' : Nat) (hbig : (p : Int) + 1 ≤ mass (past e t d))
    (hlt : d < d') : mass (past e t d') ≠ 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, d' = d + m := ⟨d' - d, by omega⟩
  have hsplit := past_append e t d m
  rw [hsplit, mass_append]
  have h2 := mass_past_lower e p hp hper hmass (t - (d : Nat)) m
  omega

/-- Strict positivity of the period mass forces the backward mass to exceed `p`
by lag `p * (p + 1)`. -/
theorem mass_past_large (e : Int → Bool) (p : Nat)
    (hper : ∀ x : Int, e (x + p) = e x) (hmass : 0 < periodMass e p) (t : Int) :
    (p : Int) + 1 ≤ mass (past e t (p * (p+1))) := by
  have hk := mass_past_mul_period e p hper t (p+1)
  rw [Nat.mul_comm (p+1) p] at hk
  have hone : (1 : Int) ≤ periodMass e p := by omega
  have hnn : 0 ≤ ((p+1 : Nat) : Int) * (periodMass e p - 1) :=
    Int.mul_nonneg (Int.natCast_nonneg (p+1)) (by omega)
  have hexp : ((p+1 : Nat) : Int) * (periodMass e p - 1)
      = ((p+1 : Nat) : Int) * periodMass e p - ((p+1 : Nat) : Int) := by
    rw [Int.mul_sub, Int.mul_one]
  have hcast : ((p+1 : Nat) : Int) = (p : Int) + 1 := by omega
  omega

/-! ## The payoff: a finite lag window decides periodic supply -/

/-- With strictly positive period drift, a phase that has a P2 supplier at some
lag already has one at a lag at most `p * (p + 1)`. -/
theorem supply_lag_bound (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x) (hmass : 0 < periodMass e p) (t : Int) :
    (∃ d : Nat, 1 ≤ d ∧ ShortPeriodicSupply.P2 e t d) ↔
      (∃ d : Nat, 1 ≤ d ∧ d ≤ p * (p+1) ∧ ShortPeriodicSupply.P2 e t d) := by
  constructor
  · rintro ⟨d, hd1, hd⟩
    refine ⟨d, hd1, ?_, hd⟩
    by_cases hle : d ≤ p * (p+1)
    · exact hle
    · have hmass1 : mass (past e t d) = 1 := ((past_p2_iff e t d).mpr hd).1
      have hbig := mass_past_large e p hper hmass t
      have hne := no_return_of_large e p hp hper (by omega) t (p*(p+1)) d hbig
        (by omega)
      exact False.elim (hne hmass1)
  · rintro ⟨d, hd1, _, hd⟩
    exact ⟨d, hd1, hd⟩

/-- The practically important direction: a finite scan of the lags `1` through
`p * (p + 1)` that finds no P2 supplier proves that the phase has no supplier at
any lag at all. -/
theorem unsupplied_of_bounded_check (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x) (hmass : 0 < periodMass e p) (t : Int)
    (hcheck : ∀ d : Nat, 1 ≤ d → d ≤ p * (p+1) → ¬ ShortPeriodicSupply.P2 e t d) :
    ∀ d : Nat, 1 ≤ d → ¬ ShortPeriodicSupply.P2 e t d := by
  intro d hd1 hd
  obtain ⟨d', hd1', hd2', hd'⟩ :=
    (supply_lag_bound e p hp hper hmass t).mp ⟨d, hd1, hd⟩
  exact hcheck d' hd1' hd2' hd'

/-- Restatement of the drift hypothesis in the form the searches use: the period
mass is the signed sum of the period read backwards from any phase. -/
theorem periodMass_eq_window (e : Int → Bool) (p : Nat)
    (hper : ∀ x : Int, e (x + p) = e x) (t : Int) :
    periodMass e p = mass (past e t p) := (period_mass_const e p hper t).symm

/-! ## Semantic guard

The hypotheses are satisfiable, and the finite lag window is genuinely wider
than the short-lag window of `ShortPeriodicSupply`. The control word of that
module has period twelve and period mass two, and its phase seven is supplied
only at lag eleven, which the window `d ≤ 12 * 13` contains and the short rule
`d ≤ 7` misses. So the bound below is not an empty statement about an empty
hypothesis set. -/

theorem longLagControl_periodic (x : Int) :
    ShortPeriodicSupply.longLagControl (x + ((12 : Nat) : Int))
      = ShortPeriodicSupply.longLagControl x := by
  simp [ShortPeriodicSupply.longLagControl]

theorem longLagControl_periodMass :
    periodMass ShortPeriodicSupply.longLagControl 12 = 2 := by decide

theorem longLagControl_supply_in_window :
    ∃ d : Nat, 1 ≤ d ∧ d ≤ 12 * (12+1) ∧
      ShortPeriodicSupply.P2 ShortPeriodicSupply.longLagControl 7 d :=
  (supply_lag_bound ShortPeriodicSupply.longLagControl 12 (by omega)
      longLagControl_periodic (by rw [longLagControl_periodMass]; omega) 7).mp
    ⟨11, by omega, ShortPeriodicSupply.lag_eleven_survives_short_exclusion.1⟩

end Recaman.PeriodicSupplyBound
