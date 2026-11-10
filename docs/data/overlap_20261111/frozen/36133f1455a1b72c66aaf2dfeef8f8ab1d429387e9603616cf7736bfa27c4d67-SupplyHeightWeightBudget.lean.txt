import Recaman.SupplyDescentWeight
import Recaman.LowTargetWeightedGap

namespace Recaman.SupplyHeightWeightBudget

open Recaman.SupplyDescentWeight Recaman.LevelTriangleArea Recaman.LowTargetWeightedGap
open Recaman.AdditionRankSlack Recaman.BlockSuffixPositivity
open Recaman.SingleWindowEquality Recaman.CapacityEqualityInduction

/-- Every original interval and supplied height has a low-addition
weight budget. Neither endpoint height, floor nor run count is restricted. -/
theorem same_height_supply_weight_budget (f : Nat → Bool) (n a K : Nat) (r : Int)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n=w++List.replicate a true) :
    (cN (fun t => Fw f t=r+1 ∧ EndN f 0 t) n K : Int)≤
      lowAdditionWeights f n r K := by
  let P := fun t => Fw f t=r+1 ∧ EndN f 0 t
  obtain ⟨d,hd,hlast,hafter⟩ := last_markN P n K
  have htail : cN P (n+d) (K-d)=0 := by
    apply cN_zero_of
    intro i hi hiK
    have h := hafter (i-n) (by omega) (by omega)
    rwa [show n+(i-n)=i by omega] at h
  have hc := cN_add P n d (K-d)
  rw [show d+(K-d)=K by omega,htail,Nat.add_zero] at hc
  by_cases hz : d=0
  · rw [hz] at hc
    change cN P n K=0 at hc
    change (cN P n K : Int)≤_
    rw [hc]
    exact low_weights_nonnegative f n r K
  · have hp := hlast.resolve_left hz
    have htA := hp.2.1
    have hend : r≤Fw f (n+d) := by
      rcases fw_cases f (n+d-1) with ⟨h,_⟩ | ⟨_,h⟩
      · rw [show n+d-1+1=n+d by omega] at h
        have := hp.1
        omega
      · rw [htA] at h
        cases h
    have hbound := same_height_suppliers_le_low_additions f n a d r hw hpre hend
    have hsplit := low_weights_append f n r d (K-d)
    rw [show d+(K-d)=K by omega] at hsplit
    have hnonneg := low_weights_nonnegative f (n+d) r (K-d)
    change (cN P n d : Int)≤_ at hbound
    change (cN P n K : Int)≤_
    omega

/-- Original suppliers four levels above a whole-tail floor are bounded
by six times the original free count, with arbitrary high excursions. -/
theorem actual_floor_plus_four_count (f : Nat → Bool) (n a K : Nat) (m : Int)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n=w++List.replicate a true)
    (hfloor : ∀ i, n≤i → i≤n+K → m≤Fw f i) :
    cN (fun t => Fw f t=m+4 ∧ EndN f 0 t) n K≤6*free f n K := by
  have hb := same_height_supply_weight_budget f n a K (m+3) hw hpre
  have hW := low_weights_le_six_free f n a K m (m+3) hw hpre hfloor (by omega)
  have heq : cN (fun t => Fw f t=m+4 ∧ EndN f 0 t) n K=
      cN (fun t => Fw f t=m+3+1 ∧ EndN f 0 t) n K := by
    rw [show m+3+1=m+4 by omega]
  rw [heq]
  omega

end Recaman.SupplyHeightWeightBudget
