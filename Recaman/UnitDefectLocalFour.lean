import Recaman.UnitOneEarlySourceCollision
import Recaman.UnitDefectInitialSource

namespace Recaman.UnitDefectLocalFour

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.FourthSourceFamilies Recaman.UnitTargetSASProfile

private theorem source_clock_unique (b : Bool) (N : Nat) (x : List Bool) (i k : Nat)
    (hi : sourceAt b N x i) (hk : sourceAt b N x k) : i=k := by
  obtain ⟨q,hq,hqN,hmq,hkq⟩:=hi
  obtain ⟨r,hr,hrN,hmr,hkr⟩:=hk
  have hqr:=Recaman.RunSupplyBudget.constant_run_root_unique b q r x hq hr hkq hkr
  subst r
  omega

/-- The joint same-target source collision pays one unit for the union
of the first-A and middle-S families, with no assumption of five suppliers. -/
theorem early_union_count (x : List Bool) (h M m K j : Nat)
    (hN : 1≤cntF x) (hj : 2≤j) (hM0 : 1≤M) (hM : M≤j+2)
    (hmt : mass ([true]++List.replicate h false++List.replicate M true++List.replicate m false++x++
      List.replicate (j+1) true++List.replicate j false)=1)
    (hat : areaW ([true]++List.replicate h false++List.replicate M true++List.replicate m false++x++
      List.replicate (j+1) true++List.replicate j false)=0) :
    cN (fun i=>sourceAt true M (List.replicate m false++x) i ∨ sourceAt false m x i) 0 K≤1 := by
  apply cN_le_one_of_unique
  intro i hi k hk hsi hsk
  rcases hsi with ha|hs
  · rcases hsk with hb|ht
    · exact source_clock_unique true M _ i k ha hb
    · exact Recaman.UnitOneEarlySourceCollision.early_source_clocks_equal x h M m i k j hN hj hM0 hM hmt hat ha ht
  · rcases hsk with hb|ht
    · exact (Recaman.UnitOneEarlySourceCollision.early_source_clocks_equal x h M m k i j hN hj hM0 hM hmt hat hb hs).symm
    · exact source_clock_unique false m _ i k hs ht

/-- A unit mass defect and the same mass-one target bound the complete local
last ray by four; every local source family remains in the classification. -/
theorem fourth_local_four (h M m L s U v K j : Nat) (hv : 1≤v) (hj : 2≤j) (hM0 : 1≤M) (hM : M≤j+2)
    (hmz : mass (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true)+1=(v : Int))
    (hmt : mass ([true]++List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false++
      List.replicate (j+1) true++List.replicate j false)=1)
    (hat : areaW ([true]++List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false++
      List.replicate (j+1) true++List.replicate j false)=0) :
    rayCount (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false) K≤4 := by
  let x:=List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false
  let P:=fun i=>sourceAt true M (List.replicate m false++x) i ∨ sourceAt false m x i
  let Q:=sourceAt true L (List.replicate s false++List.replicate U true++List.replicate v false)
  let A:=sourceAt false s (List.replicate U true++List.replicate v false)
  have hN : 1≤cntF x := by simp only [x,cntF_append,cntF_A,cntF_replicate_S]; omega
  have hPQ : cN P 0 K≤1 := early_union_count x h M m K j hN hj hM0 hM
    (by simpa only [x,List.append_assoc] using hmt) (by simpa only [x,List.append_assoc] using hat)
  have hnone (i : Nat) : ¬sourceAt false h (List.replicate M true++List.replicate m false++x) i := by
    simpa only [x,List.append_assoc] using Recaman.UnitDefectInitialSource.unit_defect_initial_excluded
      (List.replicate M true++List.replicate m false++List.replicate L true++List.replicate s false++List.replicate U true)
      h i (j+1) j v hj
      (by simpa only [List.append_assoc] using hmz)
      (by simpa only [List.append_assoc] using hmt)
      (by simpa only [List.append_assoc] using hat)
  have hc : rayCount (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false) K≤
      cN (fun i=>P i ∨ Q i ∨ A i ∨ i=2) 0 K := by
    apply cN_mono
    intro i _ _ he
    have hf:=(local_fourth_sources h M m L s U v i hv).mp he
    rcases hf with h0|h1|h2|h3|h4|h5
    · exact False.elim (hnone i (by simpa only [x,List.append_assoc] using h0))
    · exact Or.inl (Or.inl (by simpa only [x,List.append_assoc] using h1))
    · exact Or.inl (Or.inr (by simpa only [x,List.append_assoc] using h2))
    · exact Or.inr (Or.inl h3)
    · exact Or.inr (Or.inr (Or.inl h4))
    · exact Or.inr (Or.inr (Or.inr h5))
  have hQ : cN Q 0 K≤1 := sourceAt_count_le_one true L _ K
  have hA : cN A 0 K≤1 := sourceAt_count_le_one false s _ K
  have h2 : cN (fun i=>i=2) 0 K≤1 := by apply cN_le_one_of_unique; intros; omega
  have ho1:=cN_or_le P (fun i=>Q i ∨ A i ∨ i=2) K
  have ho2:=cN_or_le Q (fun i=>A i ∨ i=2) K
  have ho3:=cN_or_le A (fun i=>i=2) K
  omega

end Recaman.UnitDefectLocalFour
