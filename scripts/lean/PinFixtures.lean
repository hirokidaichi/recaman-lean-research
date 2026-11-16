import ProtectedStatements
import Recaman.LowSSPeriodicSupply
import Recaman.LineCapacityPeriodic
import Recaman.Coverage

/-!
# Regression fixtures for G6 (not research claims, not human pins)

Restricted versions of the pins that existing partial theorems must prove, and a
vacuous theorem in the pins' vocabulary. `scripts/test_lean_gates.py` runs the
cases in `pin_cases.tsv` against these and the real pins.
-/

namespace PinFixtures

open Recaman

/-- E-067 restricted to lags `d ≤ 7`: what E-071 proves. -/
def E067_lag7 : Prop :=
  ∀ (e : Int → Bool) (p : Nat), (∀ x : Int, e (x + p) = e x) → ∀ t : Int,
    0 < ShortPeriodicSupply.signSum e t p →
    ∃ i : Nat, i < p ∧ e (t + i) = true ∧
      ¬ ∃ d : Nat, 1 ≤ d ∧ d ≤ 7 ∧ ShortPeriodicSupply.P2 e (t + i) d

/-- E-070 restricted to supply windows with at most one SS: what E-128 proves. -/
def E070_lowSS : Prop :=
  ∀ (e : Int → Bool) (p : Nat), 0 < p → (∀ x : Int, e (x + p) = e x) →
    0 < ShortPeriodicSupply.signSum e 0 p →
    ∀ U : List Nat, U.Nodup → (∀ u, u ∈ U → u < p) →
    (∀ u, u ∈ U → e u = true ∧ ∃ d : Nat, ShortPeriodicSupply.P2 e u d ∧
      OneSSMultiplicity.ssCount (LeadingRunSupply.past e u d) ≤ 1) →
    U.length ≤ (LagElevenPeriodic.subPhases e 0 p).length

/-- The 2026-09-15 shape in the pins' vocabulary: the conclusion is a hypothesis. -/
theorem vacuous_capacity (e : Int → Bool) (p : Nat) (U : List Nat)
    (h : U.length ≤ (LagElevenPeriodic.subPhases e 0 p).length) :
    U.length ≤ (LagElevenPeriodic.subPhases e 0 p).length := h

end PinFixtures
