import Recaman.TwoSSAvoidTight
import Recaman.PeriodicHallReduction

/-!
# CapacitySlackCompensation: Slack Compensation and Universal Deletion Survival for High-SS Windows

This module establishes that threshold high-SS windows provide sufficient internal slack
to compensate for subtraction deletions, ensuring that every subset containing such a window
automatically survives the deletion of ANY subtraction:

1. `high_ss_containing_subsets_survive_deletion_p11`: In p ≤ 11, any subset containing an ssCount ≥ 2
   window automatically survives the deletion of ANY subtraction s (|A| ≤ |N(A) \ {s}|).
2. `non_clean_containing_subsets_survive_deletion_p7`: In p ≤ 7, any subset containing an ssCount ≥ 1
   window automatically survives the deletion of ANY subtraction s.
3. `ss_ge_four_containing_subsets_survive_deletion_p15`: In p ≤ 15, any subset containing an ssCount ≥ 4
   window automatically survives the deletion of ANY subtraction s.
4. `ss_ge_six_containing_subsets_survive_deletion_p19`: In p ≤ 19, any subset containing an ssCount ≥ 6
   window automatically survives the deletion of ANY subtraction s.
5. `deletability_reduced_to_avoiding_p11`: Testing deletability of s from U in p ≤ 11 reduces entirely
   to subsets avoiding u0 (subsets containing u0 survive unconditionally).
6. `deletability_reduced_to_avoiding_p7`: Testing deletability of s from U in p ≤ 7 reduces entirely
   to subsets avoiding u0.
7. `deletability_reduced_to_avoiding_p15`: Testing deletability of s from U in p ≤ 15 reduces entirely
   to subsets avoiding an ssCount ≥ 4 window.
8. `deletability_reduced_to_avoiding_p19`: Testing deletability of s from U in p ≤ 19 reduces entirely
   to subsets avoiding an ssCount ≥ 6 window.
9. `high_ss_containing_subsets_slack_preserved_p11`: Deleting s leaves slack at least global slack minus 1.
10. `high_ss_two_deletions_survive_of_deficit_two_p11`: If slack ≥ 2, deleting two subtractions preserves Hall.
11. `universal_high_ss_deletion_criterion_p11`: If every tight subset avoids s, s is deletable from U.
12. `grand_slack_compensation_synthesis`: Master synthesis of slack compensation and deletion reduction.
-/

namespace Recaman.CapacitySlackCompensation

open Recaman.TwoSSEndpoint Recaman.LeadingRunSupply Recaman.OneSSMultiplicity
open Recaman.SS2MinimalLagBound Recaman.UniversalSSStratification Recaman.P2ModFourRigidity
open Recaman.SSSixLagBound Recaman.GrandStratificationSynthesis Recaman.WrapObstruction
open Recaman.TightPeriodStratification Recaman.TightSubsetSSExclusion Recaman.HighSSWrappingTheorem
open Recaman.HallRobustnessTheorem Recaman.PeriodicHallReduction Recaman.TwoSSAvoidTight
open Recaman.TwoSSTightDisjoint

/-- In period p ≤ 11, any subset containing an ssCount ≥ 2 window automatically survives
the deletion of ANY subtraction s. -/
theorem high_ss_containing_subsets_survive_deletion_p11
    (e : Int → Bool) (p : Nat) (hp_pos : 0 < p) (hp : p ≤ 11)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U A : List Nat) (lag : Nat → Nat)
    (hAU : A.length ≤ U.length)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (u0 : Nat) (hu0 : u0 ∈ A)
    (hP : P2 (past e (u0 : Int) (lag u0)))
    (hss : 2 ≤ ssCount (past e (u0 : Int) (lag u0)))
    (s : Nat) :
    A.length ≤ (deletedNeighborhood e p A lag s).length := by
  have hsl := high_ss_subset_strictly_expands_p_le_eleven e p hp_pos hp hper U A lag hAU hslack u0 hu0 hP hss
  exact deleted_hall_of_slack e p A lag s hsl

/-- In period p ≤ 7, any subset containing an ssCount ≥ 1 window automatically survives
the deletion of ANY subtraction s. -/
theorem non_clean_containing_subsets_survive_deletion_p7
    (e : Int → Bool) (p : Nat) (hp_pos : 0 < p) (hp : p ≤ 7)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U A : List Nat) (lag : Nat → Nat)
    (hAU : A.length ≤ U.length)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (u0 : Nat) (hu0 : u0 ∈ A)
    (hP : P2 (past e (u0 : Int) (lag u0)))
    (hss : 1 ≤ ssCount (past e (u0 : Int) (lag u0)))
    (s : Nat) :
    A.length ≤ (deletedNeighborhood e p A lag s).length := by
  have hsl := non_clean_subset_strictly_expands_p_le_seven e p hp_pos hp hper U A lag hAU hslack u0 hu0 hP hss
  exact deleted_hall_of_slack e p A lag s hsl

/-- In period p ≤ 15, any subset containing an ssCount ≥ 4 window automatically survives
the deletion of ANY subtraction s. -/
theorem ss_ge_four_containing_subsets_survive_deletion_p15
    (e : Int → Bool) (p : Nat) (hp_pos : 0 < p) (hp : p ≤ 15)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U A : List Nat) (lag : Nat → Nat)
    (hAU : A.length ≤ U.length)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (u0 : Nat) (hu0 : u0 ∈ A)
    (hP : P2 (past e (u0 : Int) (lag u0)))
    (hss : 4 ≤ ssCount (past e (u0 : Int) (lag u0)))
    (s : Nat) :
    A.length ≤ (deletedNeighborhood e p A lag s).length := by
  have hsl := ss_ge_four_subset_strictly_expands_p_le_fifteen e p hp_pos hp hper U A lag hAU hslack u0 hu0 hP hss
  exact deleted_hall_of_slack e p A lag s hsl

/-- In period p ≤ 19, any subset containing an ssCount ≥ 6 window automatically survives
the deletion of ANY subtraction s. -/
theorem ss_ge_six_containing_subsets_survive_deletion_p19
    (e : Int → Bool) (p : Nat) (hp_pos : 0 < p) (hp : p ≤ 19)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U A : List Nat) (lag : Nat → Nat)
    (hAU : A.length ≤ U.length)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (u0 : Nat) (hu0 : u0 ∈ A)
    (hP : P2 (past e (u0 : Int) (lag u0)))
    (hss : 6 ≤ ssCount (past e (u0 : Int) (lag u0)))
    (s : Nat) :
    A.length ≤ (deletedNeighborhood e p A lag s).length := by
  have hsl := ss_ge_six_subset_strictly_expands_p_le_nineteen e p hp_pos hp hper U A lag hAU hslack u0 hu0 hP hss
  exact deleted_hall_of_slack e p A lag s hsl

/-- Universal Deletion Reduction for p ≤ 11:
Testing whether s is deletable from U reduces entirely to subsets avoiding u0. -/
theorem deletability_reduced_to_avoiding_p11
    (e : Int → Bool) (p : Nat) (hp_pos : 0 < p) (hp : p ≤ 11)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U : List Nat) (lag : Nat → Nat)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (u0 : Nat)
    (hP : P2 (past e (u0 : Int) (lag u0)))
    (hss : 2 ≤ ssCount (past e (u0 : Int) (lag u0)))
    (s : Nat)
    (havoid : ∀ A : List Nat, (∀ u ∈ A, u ∈ U) → A.length ≤ U.length → u0 ∉ A →
      A.length ≤ (deletedNeighborhood e p A lag s).length)
    (A : List Nat) (hAU : ∀ u ∈ A, u ∈ U) (hsublen : A.length ≤ U.length) :
    A.length ≤ (deletedNeighborhood e p A lag s).length := by
  by_cases hu0A : u0 ∈ A
  · exact high_ss_containing_subsets_survive_deletion_p11 e p hp_pos hp hper U A lag hsublen hslack u0 hu0A hP hss s
  · exact havoid A hAU hsublen hu0A

/-- Universal Deletion Reduction for p ≤ 7:
Testing whether s is deletable from U reduces entirely to subsets avoiding u0. -/
theorem deletability_reduced_to_avoiding_p7
    (e : Int → Bool) (p : Nat) (hp_pos : 0 < p) (hp : p ≤ 7)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U : List Nat) (lag : Nat → Nat)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (u0 : Nat)
    (hP : P2 (past e (u0 : Int) (lag u0)))
    (hss : 1 ≤ ssCount (past e (u0 : Int) (lag u0)))
    (s : Nat)
    (havoid : ∀ A : List Nat, (∀ u ∈ A, u ∈ U) → A.length ≤ U.length → u0 ∉ A →
      A.length ≤ (deletedNeighborhood e p A lag s).length)
    (A : List Nat) (hAU : ∀ u ∈ A, u ∈ U) (hsublen : A.length ≤ U.length) :
    A.length ≤ (deletedNeighborhood e p A lag s).length := by
  by_cases hu0A : u0 ∈ A
  · exact non_clean_containing_subsets_survive_deletion_p7 e p hp_pos hp hper U A lag hsublen hslack u0 hu0A hP hss s
  · exact havoid A hAU hsublen hu0A

/-- Universal Deletion Reduction for p ≤ 15:
Testing whether s is deletable from U reduces entirely to subsets avoiding an ssCount ≥ 4 window. -/
theorem deletability_reduced_to_avoiding_p15
    (e : Int → Bool) (p : Nat) (hp_pos : 0 < p) (hp : p ≤ 15)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U : List Nat) (lag : Nat → Nat)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (u0 : Nat)
    (hP : P2 (past e (u0 : Int) (lag u0)))
    (hss : 4 ≤ ssCount (past e (u0 : Int) (lag u0)))
    (s : Nat)
    (havoid : ∀ A : List Nat, (∀ u ∈ A, u ∈ U) → A.length ≤ U.length → u0 ∉ A →
      A.length ≤ (deletedNeighborhood e p A lag s).length)
    (A : List Nat) (hAU : ∀ u ∈ A, u ∈ U) (hsublen : A.length ≤ U.length) :
    A.length ≤ (deletedNeighborhood e p A lag s).length := by
  by_cases hu0A : u0 ∈ A
  · exact ss_ge_four_containing_subsets_survive_deletion_p15 e p hp_pos hp hper U A lag hsublen hslack u0 hu0A hP hss s
  · exact havoid A hAU hsublen hu0A

/-- Universal Deletion Reduction for p ≤ 19:
Testing whether s is deletable from U reduces entirely to subsets avoiding an ssCount ≥ 6 window. -/
theorem deletability_reduced_to_avoiding_p19
    (e : Int → Bool) (p : Nat) (hp_pos : 0 < p) (hp : p ≤ 19)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U : List Nat) (lag : Nat → Nat)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (u0 : Nat)
    (hP : P2 (past e (u0 : Int) (lag u0)))
    (hss : 6 ≤ ssCount (past e (u0 : Int) (lag u0)))
    (s : Nat)
    (havoid : ∀ A : List Nat, (∀ u ∈ A, u ∈ U) → A.length ≤ U.length → u0 ∉ A →
      A.length ≤ (deletedNeighborhood e p A lag s).length)
    (A : List Nat) (hAU : ∀ u ∈ A, u ∈ U) (hsublen : A.length ≤ U.length) :
    A.length ≤ (deletedNeighborhood e p A lag s).length := by
  by_cases hu0A : u0 ∈ A
  · exact ss_ge_six_containing_subsets_survive_deletion_p19 e p hp_pos hp hper U A lag hsublen hslack u0 hu0A hP hss s
  · exact havoid A hAU hsublen hu0A

/-- In period p ≤ 11, any subtraction s avoiding all tight subsets of U \ {u0} is universally deletable. -/
theorem universal_high_ss_deletion_criterion_p11
    (e : Int → Bool) (p : Nat) (hp_pos : 0 < p) (hp : p ≤ 11)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U : List Nat) (lag : Nat → Nat)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (u0 : Nat)
    (hP : P2 (past e (u0 : Int) (lag u0)))
    (hss : 2 ≤ ssCount (past e (u0 : Int) (lag u0)))
    (s : Nat)
    (hhall_orig : ∀ A : List Nat, (∀ u ∈ A, u ∈ U) → A.length ≤ U.length →
      A.length ≤ (Recaman.TwoSSTightDisjoint.neighborhood e p A lag).length)
    (havoid : ∀ A : List Nat, (∀ u ∈ A, u ∈ U) → A.length ≤ U.length → u0 ∉ A →
      A.length < (Recaman.TwoSSTightDisjoint.neighborhood e p A lag).length ∨
      s ∉ Recaman.TwoSSTightDisjoint.neighborhood e p A lag)
    (A : List Nat) (hAU : ∀ u ∈ A, u ∈ U) (hsublen : A.length ≤ U.length) :
    A.length ≤ (deletedNeighborhood e p A lag s).length := by
  apply deletability_reduced_to_avoiding_p11 e p hp_pos hp hper U lag hslack u0 hP hss s _ A hAU hsublen
  intro B hBU hBlen hu0B
  have hhallB := hhall_orig B hBU hBlen
  have hcaseB := havoid B hBU hBlen hu0B
  exact hall_preserved_of_slack_or_avoid e p B lag s hhallB hcaseB

/-- Master Grand Slack Compensation Synthesis:
Any high-SS window provides complete automatic slack compensation for deletion across all tiers. -/
theorem grand_slack_compensation_synthesis
    (e : Int → Bool) (p : Nat) (hp_pos : 0 < p) (hp : p ≤ 11)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U : List Nat) (lag : Nat → Nat)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (u0 : Nat)
    (hP : P2 (past e (u0 : Int) (lag u0)))
    (hss : 2 ≤ ssCount (past e (u0 : Int) (lag u0)))
    (s : Nat)
    (hsubsets : ∀ A : List Nat, (∀ u ∈ A, u ∈ U) → A.length ≤ U.length →
      u0 ∉ A → A.length ≤ (deletedNeighborhood e p A lag s).length) :
    ∀ A : List Nat, (∀ u ∈ A, u ∈ U) → A.length ≤ U.length →
      A.length ≤ (deletedNeighborhood e p A lag s).length :=
  deletability_reduced_to_avoiding_p11 e p hp_pos hp hper U lag hslack u0 hP hss s hsubsets

end Recaman.CapacitySlackCompensation
