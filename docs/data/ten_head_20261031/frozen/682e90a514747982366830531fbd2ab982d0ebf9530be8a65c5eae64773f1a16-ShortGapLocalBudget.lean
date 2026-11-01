import Recaman.FourthSourceFamilies

namespace Recaman.ShortGapLocalBudget

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.FourthSourceFamilies Recaman.ShortGapSourceClocks Recaman.OneGapInteriorA

/-- Uniform local budget4/5 for final S lengths1/2 in every zero-mass
moment-band three-A-run head. All head lengths and future A clocks are
unbounded; overlapping clocks0/2 are counted only once. -/
theorem short_gap_local_budget (h M m L s U v K : Nat) (hs : 1≤s)
    (hmz : mass (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true)=0)
    (B : Int)
    (haz : areaW (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true)= -B)
    (hS : 3≤cntF (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true))
    (hlo : 4*(cntF (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true) : Int)+6≤B)
    (hhi : B≤6*(cntF (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true) : Int)+4)
    (hv : v=1 ∨ v=2) :
    rayCount (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false) K≤v+3 := by
  let x:=List.replicate M true++List.replicate m false++List.replicate L true++
    List.replicate s false++List.replicate U true
  let P:=fun i : Nat=>i=0 ∨ i=2
  let Q:=sourceAt true M (List.replicate m false++List.replicate L true++List.replicate s false++
    List.replicate U true++List.replicate v false)
  let R:=sourceAt false m (List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false)
  let D:=sourceAt true L (List.replicate s false++List.replicate U true++List.replicate v false)
  have hvpos : 1≤v := by omega
  have hv3 : v≤3 := by omega
  have hpoint : ∀ i, Recaman.ThreeNonsuppliedData.localSupply
      (List.replicate h false++List.replicate M true++List.replicate m false++
        List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false++
        List.replicate i true)=true → P i ∨ Q i ∨ R i ∨ (v=2 ∧ D i) := by
    intro i hi
    rcases (local_fourth_sources h M m L s U v i hvpos).mp hi with h0|h1|h2|h3|h4|h5
    · have hx:=initial_family_small_clock h v i x B
        (by simpa only [x,List.append_assoc] using hmz)
        (by simpa only [x,List.append_assoc] using haz)
        (by simpa only [x,List.append_assoc] using hS)
        (by simpa only [x,List.append_assoc] using hlo)
        (by simpa only [x,List.append_assoc] using hhi) hvpos hv3
        (by simpa only [x,List.append_assoc] using h0)
      left
      change i=0 ∨ i=2
      rcases hx with hx|hx <;> omega
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl h2))
    · by_cases hv2 : v=2
      · exact Or.inr (Or.inr (Or.inr ⟨hv2,h3⟩))
      · have hv1 : v=1 := by omega
        subst v
        obtain ⟨e,he,heL,hbal,hkey⟩:=h3
        have hi2:=interior_A_one_gap_clock e s U i he hs
          (by simpa only [List.replicate_one,List.append_assoc] using hbal)
          (by simpa only [List.replicate_one,List.append_assoc] using hkey)
        exact Or.inl (Or.inr hi2)
    · obtain ⟨q,hq,hqs,hbal,hkey⟩:=h4
      have hi02:=tail_S_small_gap_clock q U v i hq hvpos hv3
        (by simpa only [List.append_assoc] using hbal)
        (by simpa only [List.append_assoc] using hkey)
      exact Or.inl hi02
    · exact Or.inl (Or.inr h5)
  have hlocal : rayCount (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false) K≤
      cN (fun i=>P i ∨ Q i ∨ R i ∨ (v=2 ∧ D i)) 0 K := by
    apply cN_mono
    intro i _ _ hi
    exact hpoint i hi
  have hP : cN P 0 K≤2 := zero_two_count K
  have hQ : cN Q 0 K≤1 := sourceAt_count_le_one true M _ K
  have hR : cN R 0 K≤1 := sourceAt_count_le_one false m _ K
  have hD : cN (fun i=>v=2 ∧ D i) 0 K≤v-1 := by
    by_cases hv2 : v=2
    · have hh : cN (fun i=>v=2 ∧ D i) 0 K≤cN D 0 K := by
        apply cN_mono
        intro i _ _ hi
        exact hi.2
      have hd : cN D 0 K≤1 := sourceAt_count_le_one true L _ K
      omega
    · have hz : cN (fun i=>v=2 ∧ D i) 0 K=0 := by
        apply cN_zero_of
        intro i _ _ hi
        exact hv2 hi.1
      rw [hz]
      omega
  have h1:=cN_or_le P (fun i=>Q i ∨ R i ∨ (v=2 ∧ D i)) K
  have h2:=cN_or_le Q (fun i=>R i ∨ (v=2 ∧ D i)) K
  have h3:=cN_or_le R (fun i=>v=2 ∧ D i) K
  omega

end Recaman.ShortGapLocalBudget
