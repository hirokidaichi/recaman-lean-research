import Recaman.LeadingRunSupply
import Recaman.ParitySupply
import Recaman.ShortPeriodicSupply
import Recaman.EventualPeriodicSupply
import Recaman.GrandUniversalCapacityResolution
import Recaman.FiniteSeedPeriodicSupply
import Recaman.OneSSMultiplicity
import Recaman.LowSSPeriodicSupply
import Recaman.LagElevenPeriodic
import Recaman.PeriodicTailRepresentation
import Recaman.CanonicalSSFreeSupply

/-!
# Exact Orbit Non-Periodicity

This module formalizes the synthesis of the finite seed supply theorem (E-065 / E-120)
and the universal capacity obstruction (E-067 / E-319), establishing that no exact Recamán orbit
can enter an eventually periodic sign pattern.

In particular:
1. `mass_past_add_eq_signSum`: Connects backward period mass to forward `signSum`.
2. `signSum_eq_period_mass`: Proves `signSum e 0 p = mass (past e 0 p)` for any periodic word `e`.
3. `pos_signSum_of_pos_period_mass`: Positive period mass implies strictly positive `signSum`.
4. `low_ss_periodic_obstruction`: Low-SS periodic supply obstruction.
5. `grand_capacity_supply_obstruction`: Capacity induction obstruction for periodic words with positive `signSum`.
6. `seeded_orbit_not_eventual_low_ss_periodic`: An arbitrary seeded orbit cannot enter an eventual low-SS periodic sign pattern.
7. `seeded_orbit_not_eventual_periodic_of_capacity_induction`: An arbitrary seeded orbit cannot enter an eventual periodic sign pattern under capacity induction.
8. `canonical_orbit_not_eventual_low_ss_periodic`: The canonical Recamán orbit (a0 = 0) cannot enter an eventual low-SS periodic sign pattern.
9. `canonical_orbit_not_eventual_periodic_of_capacity_induction`: The canonical Recamán orbit cannot enter an eventual periodic sign pattern under capacity induction.
-/

open Recaman.LeadingRunSupply
open Recaman.ParitySupply
open Recaman.ShortPeriodicSupply
open Recaman.EventualPeriodicSupply
open Recaman.GrandUniversalCapacityResolution
open Recaman.FiniteSeedPeriodicSupply
open Recaman.OneSSMultiplicity
open Recaman.LowSSPeriodicSupply
open Recaman.LagElevenPeriodic
open Recaman.PeriodicTailRepresentation
open Recaman.CanonicalSSFreeSupply

namespace Recaman.ExactOrbitNonperiodicity

/-- Backward period mass shifted by length matches forward signSum across a window of length n. -/
theorem mass_past_add_eq_signSum (e : Int → Bool) (t : Int) (n : Nat) :
    mass (past e (t + (n : Int)) n) = signSum e t n := by
  induction n with
  | zero => simp [past, mass, signSum]
  | succ n ih =>
    have hT : t + ((n + 1 : Nat) : Int) - 1 = t + (n : Int) := by omega
    have hsucc := past_succ e (t + ((n + 1 : Nat) : Int)) n
    rw [hT] at hsucc
    rw [hsucc]
    simp only [mass_cons, signSum]
    rw [ih]
    omega

/-- For any periodic word `e` with period `p > 0`, the forward `signSum e 0 p` equals
the backward period mass `mass (past e 0 p)`. -/
theorem signSum_eq_period_mass (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x) :
    signSum e 0 p = mass (past e 0 p) := by
  have h := mass_past_add_eq_signSum e 0 p
  have h0 : (0 : Int) + (p : Int) = (p : Int) := by omega
  rw [h0] at h
  have hc := period_mass_constant e p hp hper (p : Int)
  rw [← hc]
  exact h.symm

/-- If the period mass `mass (past e 0 p)` is at least 1, then the period signSum `signSum e 0 p` is strictly positive. -/
theorem pos_signSum_of_pos_period_mass (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (hS : 1 ≤ mass (past e 0 p)) :
    0 < signSum e 0 p := by
  rw [signSum_eq_period_mass e p hp hper]
  omega

/-- Low-SS periodic supply obstruction: In any periodic word `e` with `signSum > 0`,
if every addition phase has a P2 donor window with `ssCount ≤ 1`, then Hall capacity fails. -/
theorem low_ss_periodic_obstruction (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (hpos : 0 < ShortPeriodicSupply.signSum e 0 p)
    (hSupply : ∀ u : Nat, u < p → e (u : Int) = true → ∃ d : Nat,
      ShortPeriodicSupply.P2 e (u : Int) d ∧ ssCount (past e (u : Int) d) ≤ 1) :
    False := by
  let U : List Nat := (List.range p).filter (fun (i : Nat) => e (i : Int))
  have hUnodup : U.Nodup := List.Nodup.sublist List.filter_sublist List.nodup_range
  have hUrange : ∀ u, u ∈ U → u < p := by
    intro u hu
    exact List.mem_range.mp (List.mem_filter.mp hu).1
  have hU_mem : ∀ u, u ∈ U → e (u : Int) = true := by
    intro u hu
    exact (List.mem_filter.mp hu).2
  have hU_supply : ∀ u, u ∈ U → e (u : Int) = true ∧ ∃ d : Nat,
      ShortPeriodicSupply.P2 e (u : Int) d ∧ ssCount (past e (u : Int) d) ≤ 1 := by
    intro u hu
    refine ⟨hU_mem u hu, hSupply u (hUrange u hu) (hU_mem u hu)⟩
  have hcap := low_ss_base_capacity e p hp hper U hUnodup hUrange hU_supply
  have hlen : U.length = ShortPeriodicSupply.additionCount e 0 p := addition_count_filter e p
  have hlt := positive_sum_subtraction_lt_addition e p hpos
  omega

/-- Gate T6 capacity induction obstruction: For any periodic word `e` with `signSum > 0`,
capacity induction on donor-slack reduction implies `False`. -/
theorem grand_capacity_supply_obstruction (e : Int → Bool) (p : Nat)
    (hpos : 0 < ShortPeriodicSupply.signSum e 0 p)
    (card_U card_D k : Nat)
    (hU_eq_A : card_U = ShortPeriodicSupply.additionCount e 0 p)
    (hD_eq : card_D = (subPhases e 0 p).length)
    (hkU : k ≤ card_U) (hkD : k ≤ card_D)
    (h_rem : card_U - k ≤ card_D - k) :
    False := by
  have hcap := inductive_donor_reduction card_U card_D k hkU hkD h_rem
  have hlt := positive_sum_subtraction_lt_addition e p hpos
  omega

/-- Grand Synthesis: An exact Recamán orbit (from any initial state `s` and base clock `b ≤ N`)
cannot enter an eventual low-SS periodic sign pattern. -/
theorem seeded_orbit_not_eventual_low_ss_periodic (b : Nat) (s : State) (N p : Nat) (hb : b ≤ N) (hp : 0 < p)
    (hper : ∀ n : Nat, N ≤ n → absoluteSign b s ((n + p : Nat) : Int) = absoluteSign b s n)
    (hlow : ∀ u : Nat, u < p →
      (extension (fun n => absoluteSign b s n) N p) (u : Int) = true →
      ∃ d : Nat, ShortPeriodicSupply.P2 (extension (fun n => absoluteSign b s n) N p) (u : Int) d ∧
        ssCount (past (extension (fun n => absoluteSign b s n) N p) (u : Int) d) ≤ 1) :
    False := by
  let e := extension (fun n => absoluteSign b s n) N p
  have hsup := seeded_eventual_supply b s N p hb hp hper
  have hper_e := extension_periodic (fun n => absoluteSign b s n) N p
  have hpos := pos_signSum_of_pos_period_mass e p hp hper_e hsup.1
  exact low_ss_periodic_obstruction e p hp hper_e hpos hlow

/-- Grand Synthesis: An exact Recamán orbit cannot enter an eventual periodic sign pattern
under Gate T6 capacity induction. -/
theorem seeded_orbit_not_eventual_periodic_of_capacity_induction
    (b : Nat) (s : State) (N p : Nat) (hb : b ≤ N) (hp : 0 < p)
    (hper : ∀ n : Nat, N ≤ n → absoluteSign b s ((n + p : Nat) : Int) = absoluteSign b s n)
    (k : Nat)
    (hkU : k ≤ ShortPeriodicSupply.additionCount (extension (fun n => absoluteSign b s n) N p) 0 p)
    (hkD : k ≤ (subPhases (extension (fun n => absoluteSign b s n) N p) 0 p).length)
    (h_rem : ShortPeriodicSupply.additionCount (extension (fun n => absoluteSign b s n) N p) 0 p - k ≤
      (subPhases (extension (fun n => absoluteSign b s n) N p) 0 p).length - k) :
    False := by
  let e := extension (fun n => absoluteSign b s n) N p
  have hsup := seeded_eventual_supply b s N p hb hp hper
  have hper_e := extension_periodic (fun n => absoluteSign b s n) N p
  have hpos := pos_signSum_of_pos_period_mass e p hp hper_e hsup.1
  exact grand_capacity_supply_obstruction e p hpos _ _ k rfl rfl hkU hkD h_rem

/-- Canonical standard Recamán orbit (starting from a0 = 0) cannot enter an eventual
low-SS periodic sign pattern. -/
theorem canonical_orbit_not_eventual_low_ss_periodic (N p : Nat) (hp : 0 < p)
    (hper : ∀ n : Nat, N ≤ n → canonicalSign ((n + p : Nat) : Int) = canonicalSign (n : Int))
    (hlow : ∀ u : Nat, u < p →
      (extension (fun n => canonicalSign (n : Int)) N p) (u : Int) = true →
      ∃ d : Nat, ShortPeriodicSupply.P2 (extension (fun n => canonicalSign (n : Int)) N p) (u : Int) d ∧
        ssCount (past (extension (fun n => canonicalSign (n : Int)) N p) (u : Int) d) ≤ 1) :
    False := by
  have hsign : (fun n : Nat => canonicalSign (n : Int)) = (fun n : Nat => absoluteSign 0 initial (n : Int)) := by
    funext n
    rw [canonical_seed_sign]
  have hper_abs : ∀ n : Nat, N ≤ n → absoluteSign 0 initial ((n + p : Nat) : Int) = absoluteSign 0 initial (n : Int) := by
    intro n hn
    rw [canonical_seed_sign, canonical_seed_sign]
    exact hper n hn
  rw [hsign] at hlow
  exact seeded_orbit_not_eventual_low_ss_periodic 0 initial N p (by omega) hp hper_abs hlow

/-- Canonical standard Recamán orbit cannot enter an eventual periodic sign pattern
under Gate T6 capacity induction. -/
theorem canonical_orbit_not_eventual_periodic_of_capacity_induction
    (N p : Nat) (hp : 0 < p)
    (hper : ∀ n : Nat, N ≤ n → canonicalSign ((n + p : Nat) : Int) = canonicalSign (n : Int))
    (k : Nat)
    (hkU : k ≤ ShortPeriodicSupply.additionCount (extension (fun n => canonicalSign (n : Int)) N p) 0 p)
    (hkD : k ≤ (subPhases (extension (fun n => canonicalSign (n : Int)) N p) 0 p).length)
    (h_rem : ShortPeriodicSupply.additionCount (extension (fun n => canonicalSign (n : Int)) N p) 0 p - k ≤
      (subPhases (extension (fun n => canonicalSign (n : Int)) N p) 0 p).length - k) :
    False := by
  have hsign : (fun n : Nat => canonicalSign (n : Int)) = (fun n : Nat => absoluteSign 0 initial (n : Int)) := by
    funext n
    rw [canonical_seed_sign]
  have hper_abs : ∀ n : Nat, N ≤ n → absoluteSign 0 initial ((n + p : Nat) : Int) = absoluteSign 0 initial (n : Int) := by
    intro n hn
    rw [canonical_seed_sign, canonical_seed_sign]
    exact hper n hn
  rw [hsign] at hkU hkD h_rem
  exact seeded_orbit_not_eventual_periodic_of_capacity_induction 0 initial N p (by omega) hp hper_abs k hkU hkD h_rem

end Recaman.ExactOrbitNonperiodicity
