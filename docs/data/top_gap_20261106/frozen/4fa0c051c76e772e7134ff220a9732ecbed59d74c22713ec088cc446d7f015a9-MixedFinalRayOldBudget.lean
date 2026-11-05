import Recaman.BlockOldRay
import Recaman.ClockCountSaturation

namespace Recaman.MixedFinalRayOldBudget

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.ClockCountSaturation

/-- The common old history contributes at most one clock. In particular
it cannot fill both of the first two clocks if neither is local. -/
theorem actual_mixed_ray_old_budget (f : Nat → Bool) (n B T : Nat) (w y : List Bool)
    (hw : BlockWord w) (hpre : seg f 0 n=w) (hword : seg f n B=y) (hy : 3≤cntF y)
    (hA : ∀ i, i<T → f (n+B+i)=true) :
    cN (EndN f 0) (n+B) T≤1+rayCount y T ∧
    (2≤T → (∀ i, i≤1 →
      ¬Recaman.ThreeNonsuppliedData.localSupply (y++List.replicate i true)=true) →
      cN (EndN f 0) (n+B) T<T) := by
  have hz : seg f 0 (n+B)=w++y := by rw [seg_add,Nat.zero_add,hpre,hword]
  rw [endable_A_run_count f (n+B) T _ hz hA]
  refine ⟨block_rayCount_append hw y hy T,?_⟩
  intro hT hnone
  by_cases h : rayCount (w++y) T<T
  · exact h
  · exfalso
    let P:=fun i=>Recaman.ThreeNonsuppliedData.localSupply ((w++y)++List.replicate i true)=true
    have hall : ∀ i, i<T → P i := by
      intro i hi
      have he:=full_count_at P 0 T (by change T≤rayCount (w++y) T; omega) i hi
      simpa only [Nat.zero_add] using he
    have hold (i : Nat) (hi : i≤1) : tailOldRay w y i := by
      rcases (ray_supply_append_iff w y i).mp (hall i (by omega)) with ho|hl
      · exact ho
      · exact False.elim (hnone i hi hl)
    have heq:=tailOldRay_clock_unique hw y hy 0 1 (hold 0 (by omega)) (hold 1 (by omega))
    omega

end Recaman.MixedFinalRayOldBudget
