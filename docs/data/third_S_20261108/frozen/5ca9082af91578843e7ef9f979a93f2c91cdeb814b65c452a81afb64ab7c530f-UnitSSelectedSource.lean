import Recaman.SecondAStartRayBudget

namespace Recaman.UnitSSelectedSource

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.AdjacentRunSupply Recaman.FourthSourceFamilies

/-- A selected residual-one S target excludes its entire S-source family,
for arbitrary mixed future and all larger S depths. -/
theorem unit_S_target_excludes_source (x : List Bool) (s R i : Nat) (hR : 2≤R)
    (htarget : runKey (List.replicate 1 false++x)= -2*(R : Int)^2) :
    ¬sourceAt false s x i := by
  rintro ⟨k,hk,hks,hm,hkey⟩
  rw [runKey_prepend_S] at hkey htarget
  have hsq:=Recaman.ShortCounterFactorBounds.square_lower (k : Int) 1 (by decide) (by omega)
  have hr:=Recaman.ShortCounterFactorBounds.square_lower (R : Int) 2 (by decide) (by omega)
  have hp:=Int.mul_nonneg (show 0≤(k : Int)-1 by omega) (show 0≤(cntF x : Int) by omega)
  grind only

theorem unit_S_prefix_saving (x : List Bool) (s R K : Nat) (hR : 2≤R)
    (htarget : runKey (List.replicate 1 false++x)= -2*(R : Int)^2) :
    rayCount (List.replicate s false++x) K≤rayCount x K := by
  unfold rayCount
  apply cN_mono
  intro i hi hiK he
  rcases (local_const_split false s x i).mp he with hs|hx
  · exact False.elim (unit_S_target_excludes_source x s R i hR htarget hs)
  · exact hx

/-- At gap zero the selected suffix can be its own primitive source. -/
theorem zero_gap_control : runKey (List.replicate 1 false)= -2 ∧
    sourceAt false 1 [] 2 := by decide

end Recaman.UnitSSelectedSource
