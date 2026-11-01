import Recaman.NoOldInitialSource
import Recaman.FirstATargetSquare

namespace Recaman.NoOldLocalFive

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.FourthSourceFamilies

theorem target_local_five_sources (u : List Bool) (hu : BlockWord u) (hcu : mass u=3)
    (h M m L s U R i : Nat) (hR : 5≤R) (hzero : M+L+U=h+m+s)
    (hS15 : h+m+s≤15) (hbudget : M≤R+1) (B : Int)
    (hB : runKey (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true)= -2*B)
    (hkeyTarget : runKey u=2*B-12*((h : Int)+(m : Int)+(s : Int))-18-2*(R : Int)^2)
    (hi : Recaman.ThreeNonsuppliedData.localSupply
      (List.replicate h false++List.replicate M true++List.replicate m false++
        List.replicate L true++List.replicate s false++List.replicate U true++
        List.replicate 3 false++List.replicate i true)=true) :
    i=0 ∨
    sourceAt false m (List.replicate L true++List.replicate s false++List.replicate U true++List.replicate 3 false) i ∨
    sourceAt true L (List.replicate s false++List.replicate U true++List.replicate 3 false) i ∨
    sourceAt false s (List.replicate U true++List.replicate 3 false) i ∨ i=2 := by
  let x:=List.replicate M true++List.replicate m false++List.replicate L true++
    List.replicate s false++List.replicate U true
  have hmz : mass (List.replicate h false++x)=0 := by
    simp only [x,mass_append,mass_rep_false,mass_replicate_A]
    omega
  have hc : cntF (List.replicate h false++x)=h+m+s := by
    have hm:=mass_cntF (List.replicate h false++x)
    have hl : (List.replicate h false++x).length=h+M+m+L+s+U := by
      simp only [x,List.length_append,List.length_replicate,Nat.add_assoc]
    rw [hmz,hl] at hm
    omega
  have hBx : runKey (List.replicate h false++x)= -2*B := by
    simpa only [x,List.append_assoc] using hB
  rcases (local_fourth_sources h M m L s U 3 i (by decide)).mp hi with h0|h1|h2|h3|h4|h5
  · have he:=Recaman.NoOldInitialSource.target_initial_S_excluded u x hu h R i hR hmz (by omega)
      (by rw [hBx,hc]; simp only [Int.natCast_add]; omega)
    exact False.elim (he (by simpa only [x,List.append_assoc] using h0))
  · left
    exact Recaman.FirstATargetSquare.first_A_source_zero u hu hcu h M m L s U R i hzero hbudget B hB hkeyTarget h1
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr (Or.inl h3))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h4)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h5)))

theorem target_local_count_five (u : List Bool) (hu : BlockWord u) (hcu : mass u=3)
    (h M m L s U R K : Nat) (hR : 5≤R) (hzero : M+L+U=h+m+s)
    (hS15 : h+m+s≤15) (hbudget : M≤R+1) (B : Int)
    (hB : runKey (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true)= -2*B)
    (hkeyTarget : runKey u=2*B-12*((h : Int)+(m : Int)+(s : Int))-18-2*(R : Int)^2) :
    rayCount (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true++List.replicate 3 false) K≤5 := by
  let P:=sourceAt false m (List.replicate L true++List.replicate s false++List.replicate U true++List.replicate 3 false)
  let Q:=sourceAt true L (List.replicate s false++List.replicate U true++List.replicate 3 false)
  let A:=sourceAt false s (List.replicate U true++List.replicate 3 false)
  have hc : rayCount (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true++List.replicate 3 false) K≤
      cN (fun i=>i=0 ∨ P i ∨ Q i ∨ A i ∨ i=2) 0 K := by
    apply cN_mono
    intro i _ _ hi
    exact target_local_five_sources u hu hcu h M m L s U R i hR hzero hS15 hbudget B hB hkeyTarget
      (by simpa only [List.append_assoc] using hi)
  have hp : cN P 0 K≤1 := sourceAt_count_le_one false m _ K
  have hq : cN Q 0 K≤1 := sourceAt_count_le_one true L _ K
  have ha : cN A 0 K≤1 := sourceAt_count_le_one false s _ K
  have h0 : cN (fun i=>i=0) 0 K≤1 := by apply cN_le_one_of_unique; intros; omega
  have h2 : cN (fun i=>i=2) 0 K≤1 := by apply cN_le_one_of_unique; intros; omega
  have ho1:=cN_or_le (fun i=>i=0) (fun i=>P i ∨ Q i ∨ A i ∨ i=2) K
  have ho2:=cN_or_le P (fun i=>Q i ∨ A i ∨ i=2) K
  have ho3:=cN_or_le Q (fun i=>A i ∨ i=2) K
  have ho4:=cN_or_le A (fun i=>i=2) K
  omega

end Recaman.NoOldLocalFive
