import Recaman.InitialSTargetTwoShapes

namespace Recaman.InitialSTargetCountCharge

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.ASourceReuse
open Recaman.RunClockClassifier Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.SourceFamilyFreeCount Recaman.OldTargetLocalTail Recaman.OldTargetClockCollision
open Recaman.OldTargetMiddleCharge Recaman.InitialSTargetBounds Recaman.InitialSTargetTail
open Recaman.InitialSTargetTwoShapes
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

private theorem cntF_A (k : Nat) : cntF (List.replicate k true)=0 := by
  have hc := cntF_int (List.replicate k true)
  rw [List.length_replicate,ones_replicate_A] at hc
  omega

/-- The actual first-two budgets are explicit inputs here; the next
module supplies them from the same original0 history. -/
theorem initial_S_target_count_charge (w : List Bool) (hw : BlockWord w)
    (h q M m L s T j F F3 : Nat) (hqh : q≤h)
    (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hj : 4≤j)
    (hbudget : M+L+T≤j+10)
    (hmt : mass (List.replicate q false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate T true++List.replicate j false)=1)
    (hat : areaW (List.replicate q false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate T true++List.replicate j false)=0)
    (hhead : M+L≤2*F+1) (hhead5 : M+L≤F+5)
    (hpart : T≤F3+rayCount (w++(List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false)) T) : j+1≤F+F3 := by
  let v := List.replicate h false++List.replicate M true++List.replicate m false++List.replicate L true++
    List.replicate s false
  have ht := initial_S_target_equations q M m L s T j hM hm hmt hat
  have hbound := initial_S_ray_bounds w hw h q M m L s T j hqh hM hm hL hs hj hbudget hmt hat
  rcases hbound with ⟨hfive,hthree,hsmall,hoff,hshort⟩
  change rayCount (w++v) T≤5 at hfive
  change rayCount (w++v) T≤T-j+3 at hthree
  change M≤j → rayCount (w++v) T≤T-j+2 at hsmall
  change M≤j → j+3≤T → rayCount (w++v) T≤T-j+1 at hoff
  change T≤3 → L≤3 → rayCount (w++v) T≤T-j+2 at hshort
  change T≤F3+rayCount (w++v) T at hpart
  by_cases hgood : j+1≤F+F3
  · exact hgood
  · exfalso
    by_cases hT : j≤T
    · by_cases hMj : M≤j
      · by_cases hhead6 : 6≤M+L
        · have hb := hsmall hMj
          omega
        · by_cases hhead4 : 4≤M+L
          · have hb := hoff hMj (by omega)
            omega
          · omega
      · by_cases hhead8 : 8≤M+L
        · omega
        · have hshape := large_first_two_shapes q M m L s T j (by omega) hm hL hs hj (by omega) hbudget hmt hat
          have hS : 3≤cntF v := by
            simp only [v,cntF_append,cntF_replicate_S,cntF_A]
            omega
          have hold := block_rayCount_append hw v hS T
          rcases hshape with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩|⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
          · have hl := (two_shape_local_count h 5).1
            change rayCount v 5≤1 at hl
            omega
          · have hl := (two_shape_local_count h 8).2
            change rayCount v 8≤1 at hl
            omega
    · have hj4 : j=4 := by omega
      have hA12 : M+L+T=12 := by omega
      have ht3 : T≤3 := by omega
      have hlarge : 5≤M := by
        by_cases hh : 5≤M
        · exact hh
        · have hb := hsmall (by omega)
          omega
      have hsum : (q : Int)+(m : Int)+(s : Int)=7 := by omega
      have hI : (M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int)=12 := by
        have he := ht.2.1
        rw [hsum,hj4] at he
        simp only [Int.reduceAdd,Int.reducePow,Int.reduceSub] at he
        grind
      have hpM := Int.mul_nonneg (show 0≤(M : Int) by omega) (show 0≤(m : Int)+(s : Int)-2 by omega)
      have hpL := Int.mul_nonneg (show 0≤(L : Int) by omega) (show 0≤(s : Int)-1 by omega)
      have hL3 : L≤3 := by grind
      have hb := hshort ht3 hL3
      omega

end Recaman.InitialSTargetCountCharge
