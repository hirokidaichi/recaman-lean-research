import Recaman.SupplyDescentSlots
import Recaman.LevelTriangleArea

namespace Recaman.SupplyDescentWeight

open Recaman.SupplyDescentSlots Recaman.LevelTriangleArea Recaman.BlockSuffixPositivity
open Recaman.SingleWindowEquality Recaman.CapacityEqualityInduction

private theorem negative_step (f : Nat → Bool) (r : Int) (t : Nat) :
    2*((r-Fw f (t+1)).toNat : Int)=
      2*lowAdditionWeight f r t+
        belowTriangle r (Fw f (t+1))-belowTriangle r (Fw f t) := by
  rcases fw_cases f t with ⟨hstep,hA⟩ | ⟨hstep,hS⟩
  · by_cases h : r≤Fw f t
    · have w0 : lowAdditionWeight f r t=0 := by
        simp [lowAdditionWeight,hA,show ¬Fw f t<r by omega]
      have hz : (r-Fw f (t+1)).toNat=0 := by omega
      rw [w0,hz,hstep]
      unfold belowTriangle
      rw [Int.max_eq_left (show r-(Fw f t+1)≤0 by omega),
        Int.max_eq_left (show r-Fw f t≤0 by omega)]
      simp
    · have hw : lowAdditionWeight f r t=2*(r-Fw f t)-1 := by
        simp [lowAdditionWeight,hA,show Fw f t<r by omega]
      have hz : ((r-Fw f (t+1)).toNat : Int)=r-Fw f (t+1) :=
        Int.toNat_of_nonneg (by omega)
      rw [hw,hz,hstep]
      unfold belowTriangle
      rw [Int.max_eq_right (show 0≤r-(Fw f t+1) by omega),
        Int.max_eq_right (show 0≤r-Fw f t by omega)]
      grind
  · have w0 : lowAdditionWeight f r t=0 := by simp [lowAdditionWeight,hS]
    by_cases h : Fw f t≤r
    · have hz : ((r-Fw f (t+1)).toNat : Int)=r-Fw f (t+1) :=
        Int.toNat_of_nonneg (by omega)
      rw [w0,hz,hstep]
      unfold belowTriangle
      rw [Int.max_eq_right (show 0≤r-(Fw f t-1) by omega),
        Int.max_eq_right (show 0≤r-Fw f t by omega)]
      grind
    · have hz : (r-Fw f (t+1)).toNat=0 := by omega
      rw [w0,hz,hstep]
      unfold belowTriangle
      rw [Int.max_eq_left (show r-(Fw f t-1)≤0 by omega),
        Int.max_eq_left (show r-Fw f t≤0 by omega)]
      simp

/-- The original downward area slots telescope exactly to the low-A
weights and a lower-triangle endpoint correction. -/
theorem descent_slots_exact_weight (f : Nat → Bool) (n : Nat) (r : Int) :
    ∀ K, 2*((descentSlots f n r K).length : Int)=
      2*lowAdditionWeights f n r K+
        belowTriangle r (Fw f (n+K))-belowTriangle r (Fw f n)
  | 0 => by simp [descentSlots,lowAdditionWeights]
  | k+1 => by
    have ih := descent_slots_exact_weight f n r k
    have hs := negative_step f r (n+k)
    simp only [descentSlots,List.length_append,List.length_map,List.length_range,
      Int.natCast_add,lowAdditionWeights,show n+(k+1)=n+k+1 by omega]
    omega

/-- A count at any supplied height is paid by actual low additions when
the end of the whole interval is at least its source height. The odd
weights count additions with their original EndN status unchanged. -/
theorem same_height_suppliers_le_low_additions (f : Nat → Bool) (n a K : Nat) (r : Int)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n=w++List.replicate a true)
    (hend : r≤Fw f (n+K)) :
    (cN (fun t => Fw f t=r+1 ∧ EndN f 0 t) n K : Int)≤
      lowAdditionWeights f n r K := by
  have hcount := actual_same_height_supply_slots f n a K r hw hpre
  have hsum := descent_slots_exact_weight f n r K
  have h0 : 0≤belowTriangle r (Fw f n) := by
    unfold belowTriangle
    exact Int.mul_nonneg (Int.le_max_left _ _) (by have := Int.le_max_left 0 (r-Fw f n); omega)
  have h1 : belowTriangle r (Fw f (n+K))=0 := by
    simp [belowTriangle,Int.max_eq_left (show r-Fw f (n+K)≤0 by omega)]
  rw [h1] at hsum
  omega

end Recaman.SupplyDescentWeight
