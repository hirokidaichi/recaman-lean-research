import Recaman.PeriodicSupplyBound
import Recaman.EndpointRepetitionBudget

namespace Recaman.WrapSSBound

open LeadingRunSupply PeriodicSupplyBound EndpointRepetitionBudget LowSSEndpoint OneSSMultiplicity

/-!
# Wrap-vs-SS Accounting for Periodic Lag Bounds

In `Recaman.PeriodicSupplyBound`, positive period mass `periodMass e p ≥ 1`
was shown to bound every P2 supplier lag by `p * (p + 1)`. Wrap-vs-SS accounting
sharpens this scan cutoff:

For a periodic sign word `e : Int → Bool` with period `p > 0` and positive period
mass `periodMass e p ≥ 1`, any P2 supplier at lag `d = q * p + r` (with `r < p`) satisfies:

    `q * periodMass e p ≤ ssCount (past e (t - q*p) r) + 2 ≤ ssCount (past e t d) + 2`

and consequently:

    `d / p ≤ ssCount (past e t d) + 2`
    `d ≤ (ssCount (past e t d) + 2) * p + (d % p) < (ssCount (past e t d) + 3) * p`.

The core mechanism is that consecutive negative signs (subtractions) pay for themselves
in the signed sum via `ssCount`:
    `-(ssCount w : Int) - 1 ≤ mass w`
proved by structural induction on `w : List Bool`.
-/

/-- Any sign word `w` satisfies `-(ssCount w) - 1 ≤ mass w`.
Consecutive negative signs pay for themselves through `ssCount`. -/
theorem mass_lower_ssCount (w : List Bool) :
    -(ssCount w : Int) - 1 ≤ mass w := by
  match w with
  | [] =>
    decide
  | true :: w' =>
    have ih := mass_lower_ssCount w'
    simp [mass_cons, ShortPeriodicSupply.sign, ssCount]
    omega
  | false :: [] =>
    decide
  | false :: true :: w'' =>
    have ih := mass_lower_ssCount w''
    simp [mass_cons, ShortPeriodicSupply.sign, ssCount]
    omega
  | false :: false :: w'' =>
    have ih := mass_lower_ssCount (false :: w'')
    have h_ss : ssCount (false :: false :: w'') = ssCount (false :: w'') + 1 := by
      simp [ssCount]; omega
    have h_m : mass (false :: false :: w'') = mass (false :: w'') - 1 := by
      simp [mass_cons, ShortPeriodicSupply.sign]; omega
    omega
termination_by w.length

/-- Right-hand sublist monotonicity of `ssCount`, a direct consequence of superadditivity. -/
theorem ssCount_append_right_le (u v : List Bool) :
    ssCount v ≤ ssCount (u ++ v) := by
  have h := ssCount_append_superadditive u v
  omega

/-- Wrap-vs-SS accounting on the remainder window:
for any periodic sign word `e`, period `p`, and decomposition `q * p + r`,
a P2 supplier at lag `q * p + r` forces the accumulated period mass `q * periodMass e p`
to be bounded by the `ssCount` of the residual window plus 2. -/
theorem wrap_ss_remainder_bound (e : Int → Bool) (p : Nat)
    (hper : ∀ x : Int, e (x + p) = e x) (t : Int) (q r : Nat)
    (hP2 : ShortPeriodicSupply.P2 e t (q * p + r)) :
    (q : Int) * periodMass e p ≤ (ssCount (past e (t - (q * p : Nat)) r) : Int) + 2 := by
  have hsplit : past e t (q * p + r) =
      past e t (q * p) ++ past e (t - (q * p : Nat)) r := past_append e t (q * p) r
  have hp2_full : P2 (past e t (q * p + r)) := (past_p2_iff e t (q * p + r)).mpr hP2
  have hmass_full : mass (past e t (q * p + r)) = 1 := hp2_full.1
  rw [hsplit, mass_append, mass_past_mul_period e p hper t q] at hmass_full
  have hlower := mass_lower_ssCount (past e (t - (q * p : Nat)) r)
  omega

/-- Full Wrap-vs-SS lag bound:
the period mass accumulated across `q` full wraps is bounded by the total `ssCount`
of the full window plus 2. -/
theorem wrap_ss_bound (e : Int → Bool) (p : Nat)
    (hper : ∀ x : Int, e (x + p) = e x) (t : Int) (q r : Nat)
    (hP2 : ShortPeriodicSupply.P2 e t (q * p + r)) :
    (q : Int) * periodMass e p ≤ (ssCount (past e t (q * p + r)) : Int) + 2 := by
  have hrem := wrap_ss_remainder_bound e p hper t q r hP2
  have hsplit : past e t (q * p + r) =
      past e t (q * p) ++ past e (t - (q * p : Nat)) r := past_append e t (q * p) r
  have hmono : ssCount (past e (t - (q * p : Nat)) r) ≤ ssCount (past e t (q * p + r)) := by
    rw [hsplit]
    exact ssCount_append_right_le (past e t (q * p)) (past e (t - (q * p : Nat)) r)
  omega

/-- The two-sided wrap-vs-SS accounting sandwich:
`q * periodMass e p ≤ ssCount (past e (t - q*p) r) + 2 ≤ ssCount (past e t (q*p + r)) + 2`. -/
theorem wrap_ss_accounting (e : Int → Bool) (p : Nat)
    (hper : ∀ x : Int, e (x + p) = e x) (t : Int) (q r : Nat)
    (hP2 : ShortPeriodicSupply.P2 e t (q * p + r)) :
    (q : Int) * periodMass e p ≤ (ssCount (past e (t - (q * p : Nat)) r) : Int) + 2 ∧
    (ssCount (past e (t - (q * p : Nat)) r) : Int) + 2 ≤ (ssCount (past e t (q * p + r)) : Int) + 2 := by
  have hrem := wrap_ss_remainder_bound e p hper t q r hP2
  have hsplit : past e t (q * p + r) =
      past e t (q * p) ++ past e (t - (q * p : Nat)) r := past_append e t (q * p) r
  have hmono : ssCount (past e (t - (q * p : Nat)) r) ≤ ssCount (past e t (q * p + r)) := by
    rw [hsplit]
    exact ssCount_append_right_le (past e t (q * p)) (past e (t - (q * p : Nat)) r)
  exact ⟨hrem, by omega⟩

/-- Form of wrap-vs-SS bound for any lag decomposition `d = q * p + r`. -/
theorem wrap_ss_bound_of_decomp (e : Int → Bool) (p : Nat)
    (hper : ∀ x : Int, e (x + p) = e x) (t : Int) (d q r : Nat)
    (hd : d = q * p + r) (hP2 : ShortPeriodicSupply.P2 e t d) :
    (q : Int) * periodMass e p ≤ (ssCount (past e t d) : Int) + 2 := by
  subst hd
  exact wrap_ss_bound e p hper t q r hP2

/-- Form of wrap-vs-SS bound using Euclidean quotient `d / p`. -/
theorem wrap_ss_bound_of_lag (e : Int → Bool) (p : Nat)
    (hper : ∀ x : Int, e (x + p) = e x) (t : Int) (d : Nat)
    (hP2 : ShortPeriodicSupply.P2 e t d) :
    ((d / p : Nat) : Int) * periodMass e p ≤ (ssCount (past e t d) : Int) + 2 := by
  have hd : d = (d / p) * p + (d % p) := by
    have h := (Nat.div_add_mod d p).symm
    rw [Nat.mul_comm p (d / p)] at h
    exact h
  exact wrap_ss_bound_of_decomp e p hper t d (d / p) (d % p) hd hP2

/-- Sharp quotient bound when the period mass is positive:
the number of full wraps `d / p` cannot exceed `ssCount + 2`. -/
theorem quot_le_of_positive_periodMass (e : Int → Bool) (p : Nat)
    (hper : ∀ x : Int, e (x + p) = e x) (hmass : 1 ≤ periodMass e p) (t : Int) (d : Nat)
    (hP2 : ShortPeriodicSupply.P2 e t d) :
    d / p ≤ ssCount (past e t d) + 2 := by
  have hbound := wrap_ss_bound_of_lag e p hper t d hP2
  have hnn : 0 ≤ ((d / p : Nat) : Int) * (periodMass e p - 1) :=
    Int.mul_nonneg (Int.natCast_nonneg (d / p)) (by omega)
  have hexp : ((d / p : Nat) : Int) * (periodMass e p - 1)
      = ((d / p : Nat) : Int) * periodMass e p - ((d / p : Nat) : Int) := by
    rw [Int.mul_sub, Int.mul_one]
  omega

/-- Sharp lag bound when the period mass is positive:
any P2 supplier lag `d` satisfies `d ≤ (ssCount + 2) * p + (d % p)`. -/
theorem lag_le_of_positive_periodMass (e : Int → Bool) (p : Nat)
    (hper : ∀ x : Int, e (x + p) = e x) (hmass : 1 ≤ periodMass e p) (t : Int) (d : Nat)
    (hP2 : ShortPeriodicSupply.P2 e t d) :
    d ≤ (ssCount (past e t d) + 2) * p + (d % p) := by
  have hq := quot_le_of_positive_periodMass e p hper hmass t d hP2
  have hd : d = (d / p) * p + (d % p) := by
    have h := (Nat.div_add_mod d p).symm
    rw [Nat.mul_comm p (d / p)] at h
    exact h
  have hmul := Nat.mul_le_mul_right p hq
  omega

/-- Sharp strict lag bound when the period mass is positive:
any P2 supplier lag `d` satisfies `d < (ssCount + 3) * p`. -/
theorem lag_lt_of_positive_periodMass (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x) (hmass : 1 ≤ periodMass e p) (t : Int) (d : Nat)
    (hP2 : ShortPeriodicSupply.P2 e t d) :
    d < (ssCount (past e t d) + 3) * p := by
  have hle := lag_le_of_positive_periodMass e p hper hmass t d hP2
  have hmod : d % p < p := Nat.mod_lt d hp
  have hdist : (ssCount (past e t d) + 3) * p = (ssCount (past e t d) + 2) * p + p := by
    have : ssCount (past e t d) + 3 = (ssCount (past e t d) + 2) + 1 := rfl
    rw [this, Nat.add_mul, Nat.one_mul]
  omega

end Recaman.WrapSSBound
