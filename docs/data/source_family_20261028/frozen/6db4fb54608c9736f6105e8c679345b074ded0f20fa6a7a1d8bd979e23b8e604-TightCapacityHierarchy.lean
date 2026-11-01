import Recaman.SS2LagElevenForcing
import Recaman.TightSSZeroRigidity

/-!
# TightCapacityHierarchy: General Capacity Deficit and Window Exclusion from Tight Subsets

This module establishes the Universal Tight Capacity Hierarchy for periodic supplies:

1. `tight_size_ge_k`: Any tight subset containing a window with at least k subtractions
   in its individual neighborhood must have size at least k.
2. `no_ge_k_in_tight_lt_k`: No tight subset of size < k can contain a window with at least
   k subtractions in its individual neighborhood.
3. `no_ge_four_in_tight_le_three`: Size ≤ 3 tight subsets cannot contain a window with ≥ 4 subtractions.
4. `no_ge_five_in_tight_le_four`: Size ≤ 4 tight subsets cannot contain a window with ≥ 5 subtractions.
5. `no_ge_six_in_tight_le_five`: Size ≤ 5 tight subsets cannot contain a window with ≥ 6 subtractions.
6. `avoiding_sublist_length_le_sub_one`: Any avoiding sublist of U \ {u0} has length at most |U| - 1.
7. `avoiding_length_le_four_of_U_le_five`: In any supply with |U| ≤ 5, any avoiding sublist has size ≤ 4.
8. `avoiding_length_le_three_of_U_le_four`: In any supply with |U| ≤ 4, any avoiding sublist has size ≤ 3.
9. `avoiding_length_le_two_of_U_le_three`: In any supply with |U| ≤ 3, any avoiding sublist has size ≤ 2.
10. `avoiding_length_le_one_of_U_le_two`: In any supply with |U| ≤ 2, any avoiding sublist has size ≤ 1.
11. `tight_avoiding_excludes_ge_five`: In any periodic supply with |U| ≤ 5, no tight avoiding sublist
    can contain any window with ≥ 5 subtractions.
12. `tight_avoiding_excludes_ge_four`: In any periodic supply with |U| ≤ 4, no tight avoiding sublist
    can contain any window with ≥ 4 subtractions.
13. `tight_avoiding_excludes_ge_three`: In any periodic supply with |U| ≤ 3, no tight avoiding sublist
    can contain any window with ≥ 3 subtractions.
14. `tight_avoiding_excludes_ge_two`: In any periodic supply with |U| ≤ 2, no tight avoiding sublist
    can contain any window with ≥ 2 subtractions.
-/

namespace Recaman.TightCapacityHierarchy

open Recaman.TightP2ParityRigidity Recaman.TwoSSEndpoint Recaman.LeadingRunSupply
open Recaman.LagSevenTightObstruction Recaman.OneSSMultiplicity Recaman.SS2MinimalLagBound
open Recaman.SS2LagElevenForcing Recaman.TightSSZeroRigidity
open TwoSSTightDisjoint TwoSSPeriodicSupply TwoSSLocalDonation TwoSSAvoidTight WrapObstruction TightBottleneckBound TwoSSSmallCapacityClosure TightComponentSlackBound UniversalTightLagBound TwoSSTightAvoidanceTheorem SS2AASCollisionObstruction ElevenSSDonationClosure UniversalTwoSSDonationTheorem SS2StrictSlackTheorem LowSSTwoSSJointCapacity LowSSPeriodicSupply SharpPeriodicSupply EndpointRepetitionBudget LowSSEndpoint LagElevenPeriodic

/-- General Tight Size Lower Bound: Any tight subset containing a window with at least k
subtractions in its neighborhood must have size at least k. -/
theorem tight_size_ge_k (e : Int → Bool) (p : Nat) (hp : 0 < p) (A : List Nat) (lag : Nat → Nat)
    (u : Nat) (hu : u ∈ A) (k : Nat) (hNk : k ≤ (neighborhood e p [u] lag).length)
    (htight : (neighborhood e p A lag).length = A.length) :
    k ≤ A.length :=
  tight_size_lower_bound p hp A lag u hu k hNk htight

/-- General Tight Exclusion Principle: No tight subset of size < k can contain a window
with at least k subtractions in its neighborhood. -/
theorem no_ge_k_in_tight_lt_k (e : Int → Bool) (p : Nat) (hp : 0 < p) (A : List Nat) (lag : Nat → Nat)
    (u : Nat) (hu : u ∈ A) (k : Nat) (hNk : k ≤ (neighborhood e p [u] lag).length)
    (htight : (neighborhood e p A lag).length = A.length)
    (hlt : A.length < k) : False := by
  have hge := tight_size_ge_k e p hp A lag u hu k hNk htight
  omega

/-- Size ≤ 3 tight subsets cannot contain a window with ≥ 4 subtractions. -/
theorem no_ge_four_in_tight_le_three (e : Int → Bool) (p : Nat) (hp : 0 < p) (A : List Nat) (lag : Nat → Nat)
    (u : Nat) (hu : u ∈ A) (hN4 : 4 ≤ (neighborhood e p [u] lag).length)
    (htight : (neighborhood e p A lag).length = A.length)
    (hle3 : A.length ≤ 3) : False :=
  no_ge_k_in_tight_lt_k e p hp A lag u hu 4 hN4 htight (by omega)

/-- Size ≤ 4 tight subsets cannot contain a window with ≥ 5 subtractions. -/
theorem no_ge_five_in_tight_le_four (e : Int → Bool) (p : Nat) (hp : 0 < p) (A : List Nat) (lag : Nat → Nat)
    (u : Nat) (hu : u ∈ A) (hN5 : 5 ≤ (neighborhood e p [u] lag).length)
    (htight : (neighborhood e p A lag).length = A.length)
    (hle4 : A.length ≤ 4) : False :=
  no_ge_k_in_tight_lt_k e p hp A lag u hu 5 hN5 htight (by omega)

/-- Size ≤ 5 tight subsets cannot contain a window with ≥ 6 subtractions. -/
theorem no_ge_six_in_tight_le_five (e : Int → Bool) (p : Nat) (hp : 0 < p) (A : List Nat) (lag : Nat → Nat)
    (u : Nat) (hu : u ∈ A) (hN6 : 6 ≤ (neighborhood e p [u] lag).length)
    (htight : (neighborhood e p A lag).length = A.length)
    (hle5 : A.length ≤ 5) : False :=
  no_ge_k_in_tight_lt_k e p hp A lag u hu 6 hN6 htight (by omega)

/-- Any sublist of U avoiding an element `u0 ∈ U` has length at most `U.length - 1`. -/
theorem avoiding_sublist_length_le_sub_one (U A : List Nat) (u0 : Nat)
    (hsub : List.Sublist A U) (hu0 : u0 ∈ U) (hnot : u0 ∉ A) :
    A.length ≤ U.length - 1 :=
  sublist_length_le_sub_one_of_mem_not_mem hsub hu0 hnot

/-- In any supply with |U| ≤ 5, any avoiding sublist has size at most 4. -/
theorem avoiding_length_le_four_of_U_le_five (U A : List Nat) (u0 : Nat)
    (hsub : List.Sublist A U) (hu0 : u0 ∈ U) (hnot : u0 ∉ A)
    (hU5 : U.length ≤ 5) :
    A.length ≤ 4 := by
  have hle := avoiding_sublist_length_le_sub_one U A u0 hsub hu0 hnot
  omega

/-- In any supply with |U| ≤ 4, any avoiding sublist has size at most 3. -/
theorem avoiding_length_le_three_of_U_le_four (U A : List Nat) (u0 : Nat)
    (hsub : List.Sublist A U) (hu0 : u0 ∈ U) (hnot : u0 ∉ A)
    (hU4 : U.length ≤ 4) :
    A.length ≤ 3 := by
  have hle := avoiding_sublist_length_le_sub_one U A u0 hsub hu0 hnot
  omega

/-- In any supply with |U| ≤ 3, any avoiding sublist has size at most 2. -/
theorem avoiding_length_le_two_of_U_le_three (U A : List Nat) (u0 : Nat)
    (hsub : List.Sublist A U) (hu0 : u0 ∈ U) (hnot : u0 ∉ A)
    (hU3 : U.length ≤ 3) :
    A.length ≤ 2 := by
  have hle := avoiding_sublist_length_le_sub_one U A u0 hsub hu0 hnot
  omega

/-- In any supply with |U| ≤ 2, any avoiding sublist has size at most 1. -/
theorem avoiding_length_le_one_of_U_le_two (U A : List Nat) (u0 : Nat)
    (hsub : List.Sublist A U) (hu0 : u0 ∈ U) (hnot : u0 ∉ A)
    (hU2 : U.length ≤ 2) :
    A.length ≤ 1 := by
  have hle := avoiding_sublist_length_le_sub_one U A u0 hsub hu0 hnot
  omega

/-- Grand Tight Avoiding Capacity Theorem:
In any periodic supply with |U| ≤ 5, no tight avoiding sublist can contain any window
with at least 5 subtractions in its neighborhood. -/
theorem tight_avoiding_excludes_ge_five (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (U A : List Nat) (lag : Nat → Nat) (u0 : Nat)
    (hsub : List.Sublist A U) (hu0 : u0 ∈ U) (hnot : u0 ∉ A)
    (hU5 : U.length ≤ 5)
    (htight : (neighborhood e p A lag).length = A.length)
    (u : Nat) (hu : u ∈ A)
    (hN5 : 5 ≤ (neighborhood e p [u] lag).length) : False := by
  have hle4 := avoiding_length_le_four_of_U_le_five U A u0 hsub hu0 hnot hU5
  exact no_ge_five_in_tight_le_four e p hp A lag u hu hN5 htight hle4

/-- In any periodic supply with |U| ≤ 4, no tight avoiding sublist can contain any window
with at least 4 subtractions in its neighborhood. -/
theorem tight_avoiding_excludes_ge_four (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (U A : List Nat) (lag : Nat → Nat) (u0 : Nat)
    (hsub : List.Sublist A U) (hu0 : u0 ∈ U) (hnot : u0 ∉ A)
    (hU4 : U.length ≤ 4)
    (htight : (neighborhood e p A lag).length = A.length)
    (u : Nat) (hu : u ∈ A)
    (hN4 : 4 ≤ (neighborhood e p [u] lag).length) : False := by
  have hle3 := avoiding_length_le_three_of_U_le_four U A u0 hsub hu0 hnot hU4
  exact no_ge_four_in_tight_le_three e p hp A lag u hu hN4 htight hle3

/-- In any periodic supply with |U| ≤ 3, no tight avoiding sublist can contain any window
with at least 3 subtractions in its neighborhood. -/
theorem tight_avoiding_excludes_ge_three (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (U A : List Nat) (lag : Nat → Nat) (u0 : Nat)
    (hsub : List.Sublist A U) (hu0 : u0 ∈ U) (hnot : u0 ∉ A)
    (hU3 : U.length ≤ 3)
    (htight : (neighborhood e p A lag).length = A.length)
    (u : Nat) (hu : u ∈ A)
    (hN3 : 3 ≤ (neighborhood e p [u] lag).length) : False := by
  have hle2 := avoiding_length_le_two_of_U_le_three U A u0 hsub hu0 hnot hU3
  exact no_ge_k_in_tight_lt_k e p hp A lag u hu 3 hN3 htight (by omega)

/-- In any periodic supply with |U| ≤ 2, no tight avoiding sublist can contain any window
with at least 2 subtractions in its neighborhood. -/
theorem tight_avoiding_excludes_ge_two (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (U A : List Nat) (lag : Nat → Nat) (u0 : Nat)
    (hsub : List.Sublist A U) (hu0 : u0 ∈ U) (hnot : u0 ∉ A)
    (hU2 : U.length ≤ 2)
    (htight : (neighborhood e p A lag).length = A.length)
    (u : Nat) (hu : u ∈ A)
    (hN2 : 2 ≤ (neighborhood e p [u] lag).length) : False := by
  have hle1 := avoiding_length_le_one_of_U_le_two U A u0 hsub hu0 hnot hU2
  exact no_ge_k_in_tight_lt_k e p hp A lag u hu 2 hN2 htight (by omega)

end Recaman.TightCapacityHierarchy
