import Recaman.SS2LowSSTight
open Recaman.LeadingRunSupply
open Recaman.OneSSMultiplicity (ssCount)
open Recaman.LagSevenDonorCoverage (oldestOffset)
open Recaman.SharpPeriodicSupply (phase)
open Recaman.LowSSPeriodicSupply (endpointPhase)
open Recaman.TwoSSTightDisjoint (neighborhood)
open Recaman.SS2LowSSTight

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

def signs (s : String) : List Bool := s.toList.map (fun c => c == 'A')
def e18 (t : Int) := (signs "AAAASSAAAASAAASASS").getD (t % 18).toNat true
def lag18 (b : Nat) := if b = 11 then 7 else 3

theorem p18_tight_application :
    phase 18 (7-oldestOffset (past e18 7 11)) ∉ neighborhood e18 18 [2,8,11,13] lag18 := by
  apply lowSS_tight_avoids_donor e18 18 (by decide) (by intro x; simp [e18])
    [2,8,11,13] lag18 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) 7 11 (by decide) (by decide)
  intro j hj hd
  have h : ∀ j ∈ List.range 11, 0 < j → ¬ P2 ((past e18 7 11).take j) := by decide
  exact h j (List.mem_range.mpr hd) hj

def e36 (t : Int) := (signs "SASASASSAAAASASASASASASSAAASSAAASASA").getD (t % 36).toNat true
example : past e36 15 15 = signs "SASAAAASSASASAS" ∧
    past e36 35 19 = signs "SASAAASSAAASSASASAS" ∧
    (Recaman.LagElevenPeriodic.subPhases e36 0 36).length = 16 := by decide

theorem p36_long_supplier_slack :
    ([15] : List Nat).length+1 ≤ (Recaman.LagElevenPeriodic.subPhases e36 0 36).length := by
  apply lowSS_strict_capacity e36 36 (by decide) (by intro x; simp [e36])
    [15] (fun _ => 15) (by decide) (by decide) (by decide) (by decide) (by decide)
    35 19 (by decide) (by decide)
  intro j hj hd
  have h : ∀ j ∈ List.range 19, 0 < j → ¬ P2 ((past e36 35 19).take j) := by decide
  exact h j (List.mem_range.mpr hd) hj

theorem p36_endpoint_application :
    endpointPhase 36 15 15 ≠ phase 36 (35-oldestOffset (past e36 35 19)) := by
  apply oldest_phase_ne_lowSS_endpoint e36 36 (by decide) (by intro x; simp [e36])
    35 19 (by decide) (by decide)
  · intro j hj hd
    have h : ∀ j ∈ List.range 19, 0 < j → ¬ P2 ((past e36 35 19).take j) := by decide
    exact h j (List.mem_range.mpr hd) hj
  · decide
  · decide
  · decide

-- A singleton low-SS window need not avoid a donor's oldest interior S.
def e17 (t : Int) := (signs "ASSAAAASASASSSAAA").getD (t % 17).toNat true
example : e17 8 = true ∧ P2 (past e17 8 7) ∧ ssCount (past e17 8 7) = 1 ∧
    P2 (past e17 0 11) ∧ ssCount (past e17 0 11) = 2 ∧
    (∀ j ∈ List.range 11, 0 < j → ¬ P2 ((past e17 0 11).take j)) ∧
    neighborhood e17 17 [8] (fun _ => 7) = [1,2,7] ∧
    phase 17 (0-oldestOffset (past e17 0 11)) = 7 ∧
    (neighborhood e17 17 [8] (fun _ => 7)).length ≠ ([8] : List Nat).length := by decide

#print axioms p18_tight_application
#print axioms p36_long_supplier_slack
#print axioms p36_endpoint_application

-- The new normalization scope is exercised by an A-ended, nonminimal member.
def e28 (t : Int) := (signs "ASSASAAASASASASSAAASSAAASASA").getD (t % 28).toNat true
example : past e28 7 7 = signs "AASASSA" ∧ P2 (past e28 7 7) ∧
    ssCount (past e28 7 7) = 1 ∧ P2 ((past e28 7 7).take 3) ∧
    e28 0 = true ∧ neighborhood e28 28 [7] (fun _ => 7) = [1,2,4] := by decide

theorem p28_normalization : ∃ f : Nat → Nat,
    f 7 = 3 ∧ endpointPhase 28 7 (f 7) ∈ neighborhood e28 28 [7] (fun _ => 7) := by
  obtain ⟨f, hn, hf, hs⟩ := lowSS_endpoint_image e28 28 (by decide)
    (by intro x; simp [e28]) [7] (fun _ => 7)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  have hh := hf 7 (by simp)
  have honly : ∀ j ∈ List.range 8, P2 (past e28 7 j) → e28 (7-j) = false → j = 3 := by decide
  refine ⟨f, honly (f 7) (List.mem_range.mpr (by omega)) hh.2.2.1 hh.2.2.2.2, ?_⟩
  apply hs
  exact List.mem_map.mpr ⟨7, by simp, rfl⟩

theorem p28_nonminimal_supplier_slack :
    ([7] : List Nat).length+1 ≤ (Recaman.LagElevenPeriodic.subPhases e28 0 28).length := by
  apply lowSS_strict_capacity e28 28 (by decide) (by intro x; simp [e28])
    [7] (fun _ => 7) (by decide) (by decide) (by decide) (by decide) (by decide)
    27 19 (by decide) (by decide)
  intro j hj hd
  have h : ∀ j ∈ List.range 19, 0 < j → ¬ P2 ((past e28 27 19).take j) := by decide
  exact h j (List.mem_range.mpr hd) hj

-- Last-A donor makes true-oldest different from the full-word endpoint.
example : oldestOffset (signs "AAASSSASASA") = 10 ∧
    (signs "AAASSSASASA").getD (oldestOffset (signs "AAASSSASASA")-1) true = false := by decide
example : (signs "AAASSSASASA").getD (oldestOffset (signs "AAASSSASASA")-1) true = false :=
  oldestOffset_getD _ (oldestOffset_pos_of_ss_pos _ (by decide))

#print axioms p28_normalization
#print axioms p28_nonminimal_supplier_slack

-- The structural lemma has satisfiable premises; it finds a prefix in a nonminimal word.
example : ∃ a z : List Bool,
    ((signs "AASASASASSS" ++ [true]) ++ signs "AAS") ++ List.replicate 0 true =
      (a ++ [false]) ++ z ∧ P2 (a ++ [false]) ∧ z ≠ [] :=
  ss2_P2_suffix_has_prefix (signs "AASASASASSS") (signs "AAS") 0
    (by decide) (by decide) (by decide)

-- Donor current A is genuinely unnecessary: flip only that current sign.
def e36S (t : Int) := if t % 36 = 35 then false else e36 t
example : e36S 35 = false := by decide
theorem p36_current_S_donor_slack :
    ([15] : List Nat).length+1 ≤ (Recaman.LagElevenPeriodic.subPhases e36S 0 36).length := by
  apply lowSS_strict_capacity e36S 36 (by decide) (by intro x; simp [e36S, e36])
    [15] (fun _ => 15) (by decide) (by decide) (by decide) (by decide) (by decide)
    35 19 (by decide) (by decide)
  intro j hj hd
  have h : ∀ j ∈ List.range 19, 0 < j → ¬ P2 ((past e36S 35 19).take j) := by decide
  exact h j (List.mem_range.mpr hd) hj
#print axioms p36_current_S_donor_slack
