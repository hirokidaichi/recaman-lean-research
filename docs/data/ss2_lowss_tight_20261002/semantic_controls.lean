import Recaman.SS2LowSSTight

open Recaman.LeadingRunSupply
open Recaman.OneSSMultiplicity (ssCount)
open Recaman.LagSevenDonorCoverage (oldestOffset)
open Recaman.SharpPeriodicSupply (phase)
open Recaman.TwoSSTightDisjoint (neighborhood)
open Recaman.SS2LowSSTight

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

def signs (s : String) : List Bool := s.toList.map (fun c => c == 'A')
def e26 (t : Int) : Bool := (signs "SASASASSAAASSAAASASAASAAAA").getD (t % 26).toNat true

-- Directly consumes the all-length theorem at donor d19, nonempty tight B.
theorem p26_application :
    phase 26 (19 - (oldestOffset (past e26 19 19) : Int)) ∉
      neighborhood e26 26 [24] (fun _ => 3) := by
  apply lowSS_tight_avoids_donor e26 26 (by decide)
    (by intro t; simp [e26]) [24] (fun _ => 3)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    19 19 (by decide) (by decide)
  intro j hj hd
  have h : ∀ j ∈ List.range 19, 0 < j → ¬ P2 ((past e26 19 19).take j) := by decide
  exact h j (List.mem_range.mpr hd) hj

-- Empty/all-A input cannot fake the positive-offset hypothesis.
example : oldestOffset [] = 0 ∧ oldestOffset (signs "AAAA") = 0 ∧
    oldestOffset (signs "ASAA") = 2 ∧ ssCount (signs "SSS") = 2 := by decide
example : (signs "ASAA").getD (oldestOffset (signs "ASAA") - 1) true = false :=
  oldestOffset_getD _ (by decide)

-- Donor minimality is substantive: the final conclusion fails without it.
def e16 (t : Int) : Bool := (signs "SAAASSSASASASAAA").getD (t % 16).toNat true
example (t : Int) : e16 (t+16) = e16 t := by simp [e16]
example : e16 3 = true ∧ P2 (past e16 3 3) ∧ ssCount (past e16 3 3) ≤ 1 ∧
    P2 (past e16 15 15) ∧ ssCount (past e16 15 15) = 2 ∧
    P2 ((past e16 15 15).take 3) ∧
    neighborhood e16 16 [3] (fun _ => 3) = [0] ∧
    phase 16 (15 - (oldestOffset (past e16 15 15) : Int)) = 0 := by decide

#print axioms p26_application
#print axioms lowSS_tight_avoids_donor
#print axioms lowSS_strict_capacity
