import Recaman.UnitTargetZeroCross

namespace Recaman.FirstRayBoundaryControl

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.BlockOldRay Recaman.RunSupplyKeys
open Recaman.RunSupplyBudget Recaman.TwoRunSupply Recaman.CapacityEqualityInduction

/-- A concrete local control for the tempting h=R+1 first-ray shortcut.
It refutes a helper bound, not the parent actual free-gap conjecture. -/
theorem first_ray_two_control :
    rayCount ([false,true,true,true,true]++List.replicate 6 false) 6=2 := by
  have h0 : Recaman.ThreeNonsuppliedData.localSupply ([false,true,true,true,true]++List.replicate 6 false++List.replicate 0 true)=false := by decide
  have h1 : Recaman.ThreeNonsuppliedData.localSupply ([false,true,true,true,true]++List.replicate 6 false++List.replicate 1 true)=false := by decide
  have h2 : Recaman.ThreeNonsuppliedData.localSupply ([false,true,true,true,true]++List.replicate 6 false++List.replicate 2 true)=true := by decide
  have h3 : Recaman.ThreeNonsuppliedData.localSupply ([false,true,true,true,true]++List.replicate 6 false++List.replicate 3 true)=false := by decide
  have h4 : Recaman.ThreeNonsuppliedData.localSupply ([false,true,true,true,true]++List.replicate 6 false++List.replicate 4 true)=true := by decide
  have h5 : Recaman.ThreeNonsuppliedData.localSupply ([false,true,true,true,true]++List.replicate 6 false++List.replicate 5 true)=false := by decide
  simp only [rayCount, Recaman.SingleWindowEquality.cN, Nat.add_zero, Nat.zero_add]
  simp only [h0,h1,h2,h3,h4,h5,Bool.false_eq_true,ite_false,ite_true]

end Recaman.FirstRayBoundaryControl
