import Recaman.UnitTargetTwoS
import Recaman.FourthSourceFamilies

namespace Recaman.UnitOneInitialSource

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.FourthSourceFamilies

theorem unit_one_initial_excluded (x : List Bool) (h i T j : Nat) (hj : 2≤j)
    (hmz : mass (List.replicate h false++x)=0)
    (hmt : mass ([true]++(List.replicate h false++x)++List.replicate 1 false++
      List.replicate T true++List.replicate j false)=1)
    (hat : areaW ([true]++(List.replicate h false++x)++List.replicate 1 false++
      List.replicate T true++List.replicate j false)=0) :
    ¬sourceAt false h (x++List.replicate 1 false) i := by
  rintro ⟨q,hq,hqh,hbal,hkey⟩
  let d:=h-q
  let r:=List.replicate q false++x
  have hsplit : List.replicate h false++x=List.replicate d false++r := by
    dsimp [r]
    have hd : d≤h := by dsimp [d]; omega
    have ht : (List.replicate h false).take d=List.replicate d false := by
      rw [List.take_replicate,Nat.min_eq_left hd]
    have hh : (List.replicate h false).drop d=List.replicate q false := by
      rw [List.drop_replicate,show h-d=q by dsimp [d]; omega]
    rw [←ht,←hh,←List.append_assoc,List.take_append_drop]
  have hmr : mass r=(d : Int) := by
    rw [hsplit,mass_append,mass_rep_false] at hmz
    omega
  have hlm : mass ((r++List.replicate 1 false)++List.replicate i true)=1 := by
    simp only [mass_append,hmr,mass_rep_false,mass_replicate_A]
    have hh : mass (r++List.replicate 1 false)+(i : Int)=1 := by
      simpa only [r,List.append_assoc] using hbal
    rw [mass_append,hmr,mass_rep_false] at hh
    omega
  have hd2 : d≤2 := by
    rw [mass_append,mass_append,hmr,mass_rep_false,mass_replicate_A] at hlm
    omega
  have hlk : runKey ((r++List.replicate 1 false)++List.replicate i true)= -2 := by
    rw [runKey_append_A]
    simpa only [r,List.append_assoc] using hkey
  have hla : areaW ((r++List.replicate 1 false)++List.replicate i true)=0 := by
    unfold runKey at hlk
    rw [hlm] at hlk
    omega
  rw [hsplit] at hmt hat
  exact Recaman.UnitTargetTwoS.two_S_source_excluded (r++List.replicate 1 false) d i T j hd2 hj hlm hla
    (by simpa only [List.append_assoc] using hmt)
    (by simpa only [List.append_assoc] using hat)

theorem fourth_local_five (h M m L s U v K : Nat) (hv : 1≤v)
    (hnone : ∀ i, ¬sourceAt false h (List.replicate M true++List.replicate m false++List.replicate L true++
      List.replicate s false++List.replicate U true++List.replicate v false) i) :
    rayCount (List.replicate h false++List.replicate M true++List.replicate m false++List.replicate L true++
      List.replicate s false++List.replicate U true++List.replicate v false) K≤5 := by
  let x:=List.replicate M true++List.replicate m false++List.replicate L true++List.replicate s false++List.replicate U true
  let z:=List.replicate h false++x
  let P:=sourceAt true M (List.replicate m false++List.replicate L true++
    List.replicate s false++List.replicate U true++List.replicate v false)
  let Q:=sourceAt false m (List.replicate L true++List.replicate s false++
    List.replicate U true++List.replicate v false)
  let R:=sourceAt true L (List.replicate s false++List.replicate U true++List.replicate v false)
  let A:=sourceAt false s (List.replicate U true++List.replicate v false)
  have hpnt : ∀ i, Recaman.ThreeNonsuppliedData.localSupply
      (z++List.replicate v false++List.replicate i true)=true → P i ∨ Q i ∨ R i ∨ A i ∨ i=2 := by
    intro i hi
    have hi0 : Recaman.ThreeNonsuppliedData.localSupply
        (List.replicate h false++List.replicate M true++List.replicate m false++
          List.replicate L true++List.replicate s false++List.replicate U true++
          List.replicate v false++List.replicate i true)=true := by
      simpa only [z,x,List.append_assoc] using hi
    rcases (local_fourth_sources h M m L s U v i hv).mp hi0 with h0|h1|h2|h3|h4|h5
    · exact False.elim (hnone i (by simpa only [x,List.append_assoc] using h0))
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr (Or.inl h3))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h4)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h5)))
  have hc : rayCount (z++List.replicate v false) K≤cN (fun i=>P i ∨ Q i ∨ R i ∨ A i ∨ i=2) 0 K := by
    apply cN_mono
    intro i _ _ hi
    exact hpnt i hi
  have hp : cN P 0 K≤1 := sourceAt_count_le_one true M _ K
  have hq : cN Q 0 K≤1 := sourceAt_count_le_one false m _ K
  have hr : cN R 0 K≤1 := sourceAt_count_le_one true L _ K
  have ha : cN A 0 K≤1 := sourceAt_count_le_one false s _ K
  have h2 : cN (fun i=>i=2) 0 K≤1 := by apply cN_le_one_of_unique; intros; omega
  have ho1:=cN_or_le P (fun i=>Q i ∨ R i ∨ A i ∨ i=2) K
  have ho2:=cN_or_le Q (fun i=>R i ∨ A i ∨ i=2) K
  have ho3:=cN_or_le R (fun i=>A i ∨ i=2) K
  have ho4:=cN_or_le A (fun i=>i=2) K
  have hlocal5 : rayCount (z++List.replicate v false) K≤5 := by omega
  simpa only [z,x,List.append_assoc] using hlocal5

end Recaman.UnitOneInitialSource
