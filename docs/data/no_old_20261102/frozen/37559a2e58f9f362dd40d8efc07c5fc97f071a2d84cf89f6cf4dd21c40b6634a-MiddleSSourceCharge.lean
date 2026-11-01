import Recaman.LocalSourcePrefixBudget
import Recaman.LowSeparatorCounterCritical

namespace Recaman.MiddleSSourceCharge

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.FourthSourceFamilies

/-- A middle-S supplier has exactly M earlier tail A signs. The same
old target's source-prefix cut therefore charges R to M, not to free. -/
theorem middle_S_source_A_cut (u : List Bool) (hu : BlockWord u)
    (h M m L s U v T j i q : Nat) (hq : 1≤q) (hqm : q≤m) (hj : 2≤j) (hband : T≤i+j)
    (hm : mass (List.replicate q false++List.replicate L true++List.replicate s false++
      List.replicate U true++List.replicate v false)+(i : Int)=1)
    (hk : runKey (List.replicate q false++List.replicate L true++List.replicate s false++
      List.replicate U true++List.replicate v false)= -2)
    (hmt : mass (u++List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false++
      List.replicate T true++List.replicate j false)=1)
    (hat : areaW (u++List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false++
      List.replicate T true++List.replicate j false)=0) : j+1≤M := by
  let b:=List.replicate h false++List.replicate M true++List.replicate (m-q) false
  let x:=List.replicate q false++List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false
  have hsrep : List.replicate m false=List.replicate (m-q) false++List.replicate q false := by
    rw [←List.replicate_add,Nat.sub_add_cancel hqm]
  have hcat : b++x=List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false := by
    simp only [b,x,hsrep,List.append_assoc]
  have hlmass : mass (x++List.replicate i true)=1 := by
    rw [mass_append,mass_replicate_A]
    exact hm
  have hlkey : runKey (x++List.replicate i true)= -2 := by
    rw [runKey_append_A]
    exact hk
  have hlarea : areaW (x++List.replicate i true)=0 := by
    unfold runKey at hlkey
    rw [hlmass] at hlkey
    omega
  have hsrc:=Recaman.LocalSourcePrefixBudget.local_source_prefix_A u b x hu i T j hj hband hlmass hlarea
    (by rw [List.append_assoc u b x,hcat]; simpa only [List.append_assoc] using hmt)
    (by rw [List.append_assoc u b x,hcat]; simpa only [List.append_assoc] using hat)
  have hon : ones b=(M : Int) := by simp [b,ones_append]
  rw [hon] at hsrc
  omega

end Recaman.MiddleSSourceCharge
