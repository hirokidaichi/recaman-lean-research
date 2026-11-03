import Recaman.UnitTargetZeroCross

namespace Recaman.FirstRayBoundaryControl

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.BlockOldRay Recaman.RunSupplyKeys
open Recaman.RunSupplyBudget Recaman.TwoRunSupply Recaman.CapacityEqualityInduction

/-- A concrete local control for the tempting h=R+1 first-ray shortcut.
It refutes a helper bound, not the parent actual free-gap conjecture. -/
theorem first_ray_two_control :
    rayCount ([false,true,true,true,true]++List.replicate 6 false) 6=2 := by
  simp [rayCount, Recaman.SingleWindowEquality.cN]

end Recaman.FirstRayBoundaryControl
