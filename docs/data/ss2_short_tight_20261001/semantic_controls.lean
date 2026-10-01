import Recaman.SS2ShortTight

open Recaman.LeadingRunSupply
open Recaman.OneSSMultiplicity (ssCount)
open Recaman.LagSevenDonorCoverage (oldestOffset)
open Recaman.SharpPeriodicSupply (phase)
open Recaman.TwoSSTightDisjoint (neighborhood)

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

def signs (s : String) : List Bool := s.toList.map (fun c => c == 'A')
def e16 (t : Int) : Bool := (signs "SAAASSSASASASAAA").getD (t % 16).toNat true
def e18 (t : Int) : Bool := (signs "AAAASSAAAASAAASASS").getD (t % 18).toNat true
def e26 (t : Int) : Bool := (signs "SASASASSAAASSAAASASAASAAAA").getD (t % 26).toNat true
def lag18 (b : Nat) : Nat := if b = 11 then 7 else 3

-- Independent true-oldest, overlapping SS and terminal-A=1 controls.
example : oldestOffset (signs "AAASSSASASA") = 10 ∧
    (signs "AAASSSASASA").length = 11 ∧
    ssCount (signs "SSS") = 2 := by decide

-- Counterfactual: dropping donor minimality makes the final statement false.
example : e16 15 = true ∧ P2 (past e16 15 15) ∧ ssCount (past e16 15 15) = 2 ∧
    P2 ((past e16 15 15).take 3) ∧
    oldestOffset (past e16 15 15) = 15 ∧
    neighborhood e16 16 [3] (fun _ => 3) = [0] ∧
    phase 16 (15 - (oldestOffset (past e16 15 15) : Int)) = 0 := by decide
example : e16 3 = true ∧ P2 (past e16 3 3) ∧
    (∀ j ∈ List.range 3, 0 < j → ¬ P2 ((past e16 3 3).take j)) := by decide
example (t : Int) : e16 (t + 16) = e16 t := by simp [e16]

-- Nonempty tight subset including w1.
example : (neighborhood e18 18 [2,8,11,13] lag18).length = 4 ∧
    past e18 11 7 = signs "SAAAASS" ∧ e18 7 = true ∧
    P2 (past e18 7 11) ∧ ssCount (past e18 7 11) = 2 ∧
    oldestOffset (past e18 7 11) = 11 ∧
    (∀ j ∈ List.range 11, 0 < j → ¬ P2 ((past e18 7 11).take j)) := by decide

-- All assumptions of the arbitrary-length theorem realized with d=19 > 11.
theorem p26_application :
    phase 26 (19 - (oldestOffset (past e26 19 19) : Int)) ∉
      neighborhood e26 26 [24] (fun _ => 3) := by
  apply Recaman.SS2ShortTight.short_tight_avoids_donor e26 26 (by decide)
    (by intro t; simp [e26]) [24] (fun _ => 3)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  · intro b hb j hj hd
    have hb0 : b = 24 := by simpa using hb
    subst b
    have h : ∀ j ∈ List.range 3, 0 < j → ¬ P2 ((past e26 24 3).take j) := by decide
    exact h j (List.mem_range.mpr hd) hj
  · decide
  · decide
  · decide
  · decide
  · intro j hj hd
    have h : ∀ j ∈ List.range 19, 0 < j → ¬ P2 ((past e26 19 19).take j) := by decide
    exact h j (List.mem_range.mpr hd) hj

#print axioms Recaman.SS2ShortTight.short_tight_avoids_donor
#print axioms Recaman.SS2ShortTight.owner_member_avoids_oldest
#print axioms Recaman.SS2ShortTight.ss2_intervening_prefix
#print axioms Recaman.SS2ShortTight.short_window_hall
#print axioms Recaman.PeriodicOwnerFamilyLagEleven.tight_owner_family
#print axioms p26_application

-- The w1 positive control also consumes the final theorem itself.
theorem p18_application :
    phase 18 (7 - (oldestOffset (past e18 7 11) : Int)) ∉
      neighborhood e18 18 [2,8,11,13] lag18 := by
  apply Recaman.SS2ShortTight.short_tight_avoids_donor e18 18 (by decide)
    (by intro t; simp [e18]) [2,8,11,13] lag18
    (by decide) (by decide) (by decide) (by decide) (by decide)
  · intro b hb j hj hd
    have hl : lag18 b ≤ 7 := by simp only [lag18]; split <;> omega
    have h : ∀ b ∈ [2,8,11,13], ∀ j ∈ List.range 7,
        0 < j → j < lag18 b → ¬ P2 ((past e18 b (lag18 b)).take j) := by decide
    exact h b hb j (List.mem_range.mpr (by omega)) hj hd
  · decide
  · decide
  · decide
  · decide
  · intro j hj hd
    have h : ∀ j ∈ List.range 11, 0 < j → ¬ P2 ((past e18 7 11).take j) := by decide
    exact h j (List.mem_range.mpr hd) hj
#print axioms p18_application

-- Additional audit counterfactual: SS=2 is essential to the asserted scope.
def e4 (t : Int) : Bool := (signs "SAAA").getD (t % 4).toNat true
example (t : Int) : e4 (t + 4) = e4 t := by simp [e4]
example : e4 3 = true ∧ P2 (past e4 3 3) ∧ ssCount (past e4 3 3) = 0 ∧
    (∀ j ∈ List.range 3, 0 < j → ¬ P2 ((past e4 3 3).take j)) ∧
    neighborhood e4 4 [3] (fun _ => 3) = [0] ∧
    phase 4 (3 - (oldestOffset (past e4 3 3) : Int)) = 0 := by decide

-- Additional audit counterfactual: dropping tightness permits isolated w1.
def e17 (t : Int) : Bool := (signs "ASSAAAASASASSSAAA").getD (t % 17).toNat true
example (t : Int) : e17 (t + 17) = e17 t := by simp [e17]
example : e17 0 = true ∧ e17 8 = true ∧
    past e17 0 11 = signs "AAASSSASASA" ∧
    P2 (past e17 0 11) ∧ ssCount (past e17 0 11) = 2 ∧
    (∀ j ∈ List.range 11, 0 < j → ¬ P2 ((past e17 0 11).take j)) ∧
    past e17 8 7 = signs "SAAAASS" ∧ P2 (past e17 8 7) ∧
    (∀ j ∈ List.range 7, 0 < j → ¬ P2 ((past e17 8 7).take j)) ∧
    neighborhood e17 17 [8] (fun _ => 7) = [1,2,7] ∧
    phase 17 (0 - (oldestOffset (past e17 0 11) : Int)) = 7 := by decide
