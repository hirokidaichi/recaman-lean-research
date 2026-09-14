import Recaman.LeastTailLedgerMinimum
import Recaman.OrbitBounds
import Recaman.SubtractionLedger
import Recaman.ExactOrbitNonperiodicity
import Recaman.FiniteBlockCapacity
import Recaman.LagElevenPeriodic

/-!
# Corridor Density and Supply Obstruction

This module formalizes density inequalities and supply obstructions within the
permanent-above corridor of a hypothetical least missing target.

Key results:
1. `subCount_lower_bound_of_ledger_corridor`:
   In any ledger corridor satisfying `upperTri time < 2 * subSum time + 2 * time`,
   subtractions satisfy a strict linear lower bound: `time ≤ 4 * subCount time + 2`.
   Consequently, subtractions cannot be sparse (density at least 1/4).
2. `subCount_upper_bound_of_ledger_corridor`:
   In any ledger corridor where `2 * subSum time < upperTri time`,
   subtractions satisfy a quadratic upper bound:
   `2 * (subCount time * (subCount time + 1)) < time * (time + 1)`.
   Consequently, additions also cannot die out (density at least 1 - 1/√2).
3. `tail_minimum_subCount_bounds`:
   At the canonical tail minimum of any least missing target, the subtraction count
   is strictly positive and bounded on both sides.
4. `corridor_tail_not_eventual_low_ss_periodic`:
   The canonical orbit within the corridor cannot enter an eventual low-SS periodic sign pattern.
5. `corridor_tail_not_eventual_periodic_of_capacity_induction`:
   The canonical orbit within the corridor cannot enter an eventual periodic sign pattern under capacity induction.
6. `corridor_finite_block_capacity`:
   Across any interval within the corridor, short supplied additions cannot exceed subtractions plus 2.
7. `corridor_unsupplied_of_drift`:
   Any interval within the corridor with net upward drift `signSum ≥ 3` must contain at least one unsupplied addition.
-/

namespace Recaman.CorridorDensityObstruction

open Recaman
open Recaman.ExactOrbitNonperiodicity
open Recaman.FiniteBlockCapacity

/-- In any ledger corridor satisfying `upperTri time < 2 * subSum time + 2 * time`,
the number of subtractions satisfies a linear lower bound: `time ≤ 4 * subCount time + 2`. -/
theorem subCount_lower_bound_of_ledger_corridor (time : Nat) (_htime : 0 < time)
    (hledger : upperTri time < 2 * subSum time + 2 * time) :
    time ≤ 4 * subCount time + 2 := by
  have htri := two_mul_upperTri time
  have hsum_le := subSum_le_mul_subCount time
  have h1 : 2 * upperTri time < 4 * subSum time + 4 * time := by omega
  rw [htri] at h1
  have hcomm : 4 * (time * subCount time) = time * (4 * subCount time) := by
    rw [← Nat.mul_assoc 4 time (subCount time), Nat.mul_comm 4 time, Nat.mul_assoc time 4 (subCount time)]
  have h2 : 4 * subSum time ≤ time * (4 * subCount time) := by
    calc
      4 * subSum time ≤ 4 * (time * subCount time) := Nat.mul_le_mul_left 4 hsum_le
      _ = time * (4 * subCount time) := hcomm
  have h3 : time * (time + 1) < time * (4 * subCount time + 4) := by
    have hsum4 : 4 * subSum time + 4 * time ≤ time * (4 * subCount time) + time * 4 := by
      have : 4 * time = time * 4 := by rw [Nat.mul_comm]
      rw [this]
      exact Nat.add_le_add h2 (Nat.le_refl (time * 4))
    have hdistr : time * (4 * subCount time) + time * 4 = time * (4 * subCount time + 4) := by
      rw [← Nat.mul_add]
    calc
      time * (time + 1) < 4 * subSum time + 4 * time := h1
      _ ≤ time * (4 * subCount time) + time * 4 := hsum4
      _ = time * (4 * subCount time + 4) := hdistr
  have hcancel : time + 1 < 4 * subCount time + 4 :=
    Nat.lt_of_mul_lt_mul_left h3
  omega

/-- In any ledger corridor where `2 * subSum time < upperTri time`,
the number of subtractions satisfies a quadratic upper bound:
`2 * (subCount time * (subCount time + 1)) < time * (time + 1)`. -/
theorem subCount_upper_bound_of_ledger_corridor (time : Nat)
    (hlower : 2 * subSum time < upperTri time) :
    2 * (subCount time * (subCount time + 1)) < time * (time + 1) := by
  have htri_time := two_mul_upperTri time
  have htri_sub := two_mul_upperTri (subCount time)
  have hsub_tri := upperTri_subCount_le_subSum time
  have h1 : 2 * upperTri (subCount time) ≤ 2 * subSum time := by omega
  have h2 : 2 * (2 * upperTri (subCount time)) < 2 * upperTri time := by omega
  rw [htri_sub] at h2
  rw [htri_time] at h2
  exact h2

/-- Combined corridor bounds for a hypothetical least missing target:
at the canonical tail minimum, the subtraction count is strictly positive and
satisfies both linear lower and quadratic upper bounds. -/
theorem tail_minimum_subCount_bounds
    {target : Nat} (h : LeastMissingTarget target) :
    ∃ start time,
      MissingStrictAboveTail target start ∧
      0 < time ∧
      time ≤ 4 * subCount time + 2 ∧
      2 * (subCount time * (subCount time + 1)) < time * (time + 1) := by
  rcases h.exists_leastTailLedgerMinimum with
    ⟨start, time, firstTime, q, r, htail, hleast, hminimum,
     hcoordinates, htargetMinimum, hminimumUpper, hminimumTwice,
     hquotient, hpotential, hledgerLower, hledgerUpper⟩
  have hstartPos := missingStrictAboveTail_pos htail
  have hstartTime := hminimum.minimum.start_le_time
  have htimePos : 0 < time := Nat.lt_of_lt_of_le hstartPos hstartTime
  have hlower_strict : 2 * subSum time < upperTri time := by omega
  have h_lb := subCount_lower_bound_of_ledger_corridor time htimePos hledgerUpper
  have h_ub := subCount_upper_bound_of_ledger_corridor time hlower_strict
  exact ⟨start, time, htail, htimePos, h_lb, h_ub⟩

/-- In any least missing target tail, the tail starting at `start` cannot be eventual low-SS periodic. -/
theorem corridor_tail_not_eventual_low_ss_periodic {target : Nat} (_h : LeastMissingTarget target) :
    ∀ p : Nat, 0 < p →
    ¬ (∃ start : Nat,
        MissingStrictAboveTail target start ∧
        (∀ n : Nat, start ≤ n → CanonicalSSFreeSupply.canonicalSign ((n + p : Nat) : Int) = CanonicalSSFreeSupply.canonicalSign (n : Int)) ∧
        (∀ u : Nat, u < p →
          (PeriodicTailRepresentation.extension (fun n => CanonicalSSFreeSupply.canonicalSign (n : Int)) start p) (u : Int) = true →
          ∃ d : Nat, ShortPeriodicSupply.P2 (PeriodicTailRepresentation.extension (fun n => CanonicalSSFreeSupply.canonicalSign (n : Int)) start p) (u : Int) d ∧
            OneSSMultiplicity.ssCount (LeadingRunSupply.past (PeriodicTailRepresentation.extension (fun n => CanonicalSSFreeSupply.canonicalSign (n : Int)) start p) (u : Int) d) ≤ 1)) := by
  intro p hp ⟨start, _htail, hper, hlow⟩
  exact canonical_orbit_not_eventual_low_ss_periodic start p hp hper hlow

/-- In any least missing target tail, the tail starting at `start` cannot be eventual periodic
under capacity induction. -/
theorem corridor_tail_not_eventual_periodic_of_capacity_induction {target : Nat} (_h : LeastMissingTarget target) :
    ∀ p : Nat, 0 < p →
    ¬ (∃ (start : Nat) (k : Nat),
        MissingStrictAboveTail target start ∧
        (∀ n : Nat, start ≤ n → CanonicalSSFreeSupply.canonicalSign ((n + p : Nat) : Int) = CanonicalSSFreeSupply.canonicalSign (n : Int)) ∧
        k ≤ ShortPeriodicSupply.additionCount (PeriodicTailRepresentation.extension (fun n => CanonicalSSFreeSupply.canonicalSign (n : Int)) start p) 0 p ∧
        k ≤ (LagElevenPeriodic.subPhases (PeriodicTailRepresentation.extension (fun n => CanonicalSSFreeSupply.canonicalSign (n : Int)) start p) 0 p).length ∧
        ShortPeriodicSupply.additionCount (PeriodicTailRepresentation.extension (fun n => CanonicalSSFreeSupply.canonicalSign (n : Int)) start p) 0 p - k ≤
          (LagElevenPeriodic.subPhases (PeriodicTailRepresentation.extension (fun n => CanonicalSSFreeSupply.canonicalSign (n : Int)) start p) 0 p).length - k) := by
  intro p hp ⟨start, k, _htail, hper, hkU, hkD, h_rem⟩
  exact canonical_orbit_not_eventual_periodic_of_capacity_induction start p hp hper k hkU hkD h_rem

/-- Finite block capacity holds for any interval in the corridor. -/
theorem corridor_finite_block_capacity (t : Int) (n : Nat) :
    ShortPeriodicSupply.suppliedCount CanonicalSSFreeSupply.canonicalSign t n ≤
    ShortPeriodicSupply.subtractionCount CanonicalSSFreeSupply.canonicalSign t n + 2 :=
  canonical_orbit_finite_block_capacity t n

/-- Net drift ≥ 3 forces at least one unsupplied addition across any corridor interval. -/
theorem corridor_unsupplied_of_drift (t : Int) (n : Nat)
    (hdrift : 3 ≤ ShortPeriodicSupply.signSum CanonicalSSFreeSupply.canonicalSign t n) :
    ShortPeriodicSupply.suppliedCount CanonicalSSFreeSupply.canonicalSign t n <
    ShortPeriodicSupply.additionCount CanonicalSSFreeSupply.canonicalSign t n :=
  canonical_orbit_unsupplied_of_drift t n hdrift

end Recaman.CorridorDensityObstruction
