import Recaman.FourCrossExact
import Recaman.FourthSourceFamilies

namespace Recaman.FourthUnitSeparators

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.AdjacentRunSupply Recaman.FourthSourceFamilies Recaman.UnitTargetSASProfile

/-- With three unit separators, no nonempty first-A suffix can have
the key required for supply on the fourth ray. -/
theorem unit_separators_first_A_absent (L U i : Nat) (hL : 1≤L) (hU : 1≤U) (M : Nat) :
    ¬sourceAt true M (List.replicate 1 false++List.replicate L true++
      List.replicate 1 false++List.replicate U true++List.replicate 1 false) i := by
  rintro ⟨e,he,_,_,hk⟩
  have h:=Recaman.FourCrossExact.four_cross_exact 0 e 1 L 1 U 1 0
  dsimp only at h
  simp only [List.replicate_zero,List.nil_append,List.append_nil,cntF_append,
    cntF_replicate_S,cntF_A,Nat.zero_add,Nat.add_zero] at h
  rw [show runKey (List.replicate e true++List.replicate 1 false++List.replicate L true++
      List.replicate 1 false++List.replicate U true++List.replicate 1 false)= -2 by
    simpa only [List.append_assoc] using hk] at h
  grind only

theorem unit_separators_after_initial_four (M L U T : Nat) (hL : 1≤L) (hU : 1≤U) :
    rayCount (List.replicate M true++List.replicate 1 false++List.replicate L true++
      List.replicate 1 false++List.replicate U true++List.replicate 1 false) T≤4 := by
  let z:=List.replicate U true++List.replicate 1 false
  let r:=[(false,1),(true,L),(false,1)]
  let x:=runWord r++z
  have hrest:=run_prefix_ray_budget r z T
  change rayCount x T≤3+rayCount z T at hrest
  have hpair : rayCount z T≤1 := rayCount_A_S_le_one U 1 T (by omega)
  have he : rayCount (List.replicate M true++x) T=rayCount x T := by
    apply cN_congr
    intro i _ _
    rw [local_const_split]
    apply or_iff_right
    simpa only [x,r,z,runWord,List.append_nil,List.append_assoc] using
      unit_separators_first_A_absent L U i hL hU M
  have h : rayCount (List.replicate M true++x) T≤4 := by omega
  simpa only [x,r,z,runWord,List.append_nil,List.append_assoc] using h

end Recaman.FourthUnitSeparators
