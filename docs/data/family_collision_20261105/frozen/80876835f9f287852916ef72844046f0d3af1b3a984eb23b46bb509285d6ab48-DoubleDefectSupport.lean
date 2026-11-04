import Recaman.DoubleDefectInitial
import Recaman.UnitEarlyClockBound

namespace Recaman.DoubleDefectSupport

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.FourthSourceFamilies Recaman.UnitTargetSASProfile

theorem three_clock_count (K : Nat) : cN (fun i=>i≤2) 0 K≤3 := by
  have h0 : cN (fun i=>i=0) 0 K≤1 := by apply cN_le_one_of_unique; intros; omega
  have h1 : cN (fun i=>i=1) 0 K≤1 := by apply cN_le_one_of_unique; intros; omega
  have h2 : cN (fun i=>i=2) 0 K≤1 := by apply cN_le_one_of_unique; intros; omega
  have hc : cN (fun i=>i≤2) 0 K≤cN (fun i=>i=0 ∨ i=1 ∨ i=2) 0 K := by
    apply cN_mono; intros; omega
  have ho1:=cN_or_le (fun i=>i=0) (fun i=>i=1 ∨ i=2) K
  have ho2:=cN_or_le (fun i=>i=1) (fun i=>i=2) K
  omega

/-- Initial-S, first-A, middle-S and final-S sources share three clocks.
The two remaining families each cost one, giving a complete local bound. -/
theorem double_defect_local_support (h M m L s U v j : Nat) (hv : 1≤v) (hj : 2≤j) (hM0 : 1≤M) (hM : M≤j+2)
    (hmz : mass (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true)+2=(v : Int))
    (hmt : mass ([true]++List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false++
      List.replicate (j+2) true++List.replicate j false)=1)
    (hat : areaW ([true]++List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false++
      List.replicate (j+2) true++List.replicate j false)=0) : ∀ i, Recaman.ThreeNonsuppliedData.localSupply
      (List.replicate h false++List.replicate M true++List.replicate m false++
        List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false++
        List.replicate i true)=true →
      i≤2 ∨ sourceAt true L (List.replicate s false++List.replicate U true++List.replicate v false) i ∨
        sourceAt false s (List.replicate U true++List.replicate v false) i := by
  let x:=List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false
  let Q:=sourceAt true L (List.replicate s false++List.replicate U true++List.replicate v false)
  let A:=sourceAt false s (List.replicate U true++List.replicate v false)
  have hN : 1≤cntF x := by simp only [x,cntF_append,cntF_A,cntF_replicate_S]; omega
  have hNm : 1≤cntF (List.replicate m false++x) := by rw [cntF_append,cntF_replicate_S]; omega
  intro i he
  change i≤2 ∨ Q i ∨ A i
  have hf:=(local_fourth_sources h M m L s U v i hv).mp he
  rcases hf with h0|h1|h2|h3|h4|h5
  · have hz:=Recaman.DoubleDefectInitial.initial_two_clock_zero
      (List.replicate M true++List.replicate m false++List.replicate L true++List.replicate s false++List.replicate U true)
      h i (j+2) j v hj (by simpa only [List.append_assoc] using hmz)
      (by simpa only [List.append_assoc] using hmt) (by simpa only [List.append_assoc] using hat)
      (by simpa only [List.append_assoc] using h0)
    exact Or.inl (by omega)
  · apply Or.inl
    by_cases hi : 2≤i
    · have hb:=Recaman.UnitEarlyClockBound.first_clock_above_separator (List.replicate m false++x)
        h M i j 2 hNm hj hM hi (by simpa only [x,List.append_assoc] using hmt)
        (by simpa only [x,List.append_assoc] using hat) (by simpa only [x,List.append_assoc] using h1)
      omega
    · omega
  · apply Or.inl
    by_cases hi : 2≤i
    · have hb:=Recaman.UnitEarlyClockBound.middle_clock_above_separator x h M m i j 2 hN hj hM0 hM hi
        (by simpa only [x,List.append_assoc] using hmt) (by simpa only [x,List.append_assoc] using hat)
        (by simpa only [x,List.append_assoc] using h2)
      omega
    · omega
  · exact Or.inr (Or.inl h3)
  · exact Or.inr (Or.inr h4)
  · exact Or.inl (by omega)

end Recaman.DoubleDefectSupport
