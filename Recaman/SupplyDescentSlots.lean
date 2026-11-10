import Recaman.FloorSupplyFreeBudget
import Recaman.SupplyAreaCrossings

namespace Recaman.SupplyDescentSlots

open Recaman.FloorSupplyFreeBudget Recaman.FloorSupplyPotential Recaman.SupplyAreaCrossings
open Recaman.BlockSuffixPositivity Recaman.SingleWindowEquality Recaman.CapacityEqualityInduction
open Classical

/-- The actual downward area units of the source-level potential, retaining
their original clock and integer potential value. -/
def descentSlots (f : Nat → Bool) (n : Nat) (r : Int) : Nat → List (Nat × Int)
  | 0 => []
  | k+1 => descentSlots f n r k++
      (List.range ((r-Fw f (n+k+1)).toNat)).map
        (fun (i : Nat) => (n+k+1,floorPotential f n (r-1) (n+k+1)+(i : Int)+1))

theorem crossing_mem_descent_slots (f : Nat → Bool) (n K q : Nat) (r v : Int)
    (hnq : n<q) (hqK : q≤n+K)
    (hcross : areaCrossesDown (floorPotential f n (r-1)) v q) :
    (q,v)∈descentSlots f n r K := by
  induction K with
  | zero => omega
  | succ k ih =>
    rw [descentSlots,List.mem_append]
    by_cases hq : q≤n+k
    · exact Or.inl (ih hq)
    · right
      have heq : q=n+k+1 := by omega
      rw [←heq]
      have hs := floor_potential_step f n (q-1) (r-1) (by omega)
      rw [show q-1+1=q by omega] at hs
      have h1 := hcross.1
      have h2 := hcross.2
      let d := v-floorPotential f n (r-1) q-1
      have hd : 0≤d := by dsimp [d]; omega
      apply List.mem_map.mpr
      refine ⟨d.toNat,?_,?_⟩
      · apply List.mem_range.mpr
        dsimp [d] at hd ⊢
        omega
      · rw [Int.toNat_of_nonneg hd]
        dsimp [d]
        congr 1
        omega

/-- Every original same-height supplier occupies a distinct downward
area unit, for arbitrary old histories, run counts and heights. -/
theorem actual_same_height_supply_slots (f : Nat → Bool) (n a K : Nat) (r : Int)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n=w++List.replicate a true) :
    cN (fun t => Fw f t=r+1 ∧ EndN f 0 t) n K≤(descentSlots f n r K).length := by
  let P := fun t => n≤t ∧ t<n+K ∧ Fw f t=r+1 ∧ EndN f 0 t
  have hq (t : Nat) (ht : P t) :
      ∃ q, n<q ∧ q<t ∧ Fw f q<r ∧
        areaCrossesDown (floorPotential f n (r-1)) (floorPotential f n (r-1) t) q ∧
        ∀ u, q<u → u<t →
          ¬areaCrossesDown (floorPotential f n (r-1)) (floorPotential f n (r-1) t) u :=
    latest_actual_supply_area_crossing f n a t r hw hpre ht.1 ht.2.2.1 ht.2.2.2
  let q := fun t => if ht : P t then Classical.choose (hq t ht) else n
  have hqSpec (t : Nat) (ht : P t) :
      n<q t ∧ q t<t ∧ Fw f (q t)<r ∧
        areaCrossesDown (floorPotential f n (r-1)) (floorPotential f n (r-1) t) (q t) ∧
        ∀ u, q t<u → u<t →
          ¬areaCrossesDown (floorPotential f n (r-1)) (floorPotential f n (r-1) t) u := by
    dsimp only [q]
    rw [dif_pos ht]
    exact Classical.choose_spec (hq t ht)
  apply count_le_of_list_injection _ n K (descentSlots f n r K)
    (fun t => (q t,floorPotential f n (r-1) t))
  · intro t hnt htK ht
    have h := hqSpec t ⟨hnt,htK,ht⟩
    exact crossing_mem_descent_slots f n K (q t) r _ h.1 (by omega) h.2.2.2.1
  · intro t u hnt htu huK ht hu he
    have ht' := hqSpec t ⟨hnt,by omega,ht⟩
    have hu' := hqSpec u ⟨by omega,huK,hu⟩
    have hqeq : q t=q u := congrArg Prod.fst he
    have hPeq : floorPotential f n (r-1) t=floorPotential f n (r-1) u := congrArg Prod.snd he
    have hspace := supply_potential_spacing_after_last_crossing f n t u (q u) r hnt htu
      (by omega) ht.1 hu.1 ht.2.1 hu'.2.2.2.2
    omega

end Recaman.SupplyDescentSlots
