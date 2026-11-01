import Recaman.EqualTargetLocalFive
import Recaman.EqualTargetMiddleSquare

namespace Recaman.EqualTargetLocalFour

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.FourthSourceFamilies

theorem equal_target_local_four (u : List Bool) (hu : BlockWord u) (C : Nat)
    (hcu : mass u=(C : Int)) (hC4 : 4≤C)
    (h M m L s U v T j K : Nat) (hh : 1≤h) (hv : v=C) (hT : T=j+1)
    (hR : 5≤j+1) (hM6 : M≤6) (hzero : M+L+U=h+m+s) (hS15 : h+m+s≤15)
    (B : Int)
    (hB : runKey (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true)= -2*B)
    (hkeyTarget : runKey u=2*B-4*(v : Int)*((h : Int)+(m : Int)+(s : Int)+(v : Int))+
      2*(v : Int)^2-2*((j : Int)+1)^2)
    (hmt : mass (u++List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false++
      List.replicate T true++List.replicate j false)=1)
    (hat : areaW (u++List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false++
      List.replicate T true++List.replicate j false)=0) :
    rayCount (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false) K≤4 := by
  let x:=List.replicate M true++List.replicate m false++List.replicate L true++List.replicate s false++List.replicate U true
  let A:=sourceAt true L (List.replicate s false++List.replicate U true++List.replicate v false)
  let D:=sourceAt false s (List.replicate U true++List.replicate v false)
  have hmz : mass (List.replicate h false++x)=0 := by
    simp only [x,mass_append,mass_rep_false,mass_replicate_A]
    omega
  have hSz : cntF (List.replicate h false++x)=h+m+s := by
    have hc:=mass_cntF (List.replicate h false++x)
    have hl : (List.replicate h false++x).length=h+M+m+L+s+U := by simp [x,Nat.add_assoc]
    rw [hmz,hl] at hc
    omega
  have hBx : runKey (List.replicate h false++x)= -2*B := by simpa only [x,List.append_assoc] using hB
  have hkeyRaw : runKey u= -runKey (List.replicate h false++x)-4*(v : Int)*
      ((cntF (List.replicate h false++x) : Int)+(v : Int))+2*(v : Int)^2-2*((j : Int)+1)^2 := by
    rw [hBx,hSz]
    simp only [Int.natCast_add]
    omega
  have hc : rayCount (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false) K≤
      cN (fun i=>i=0 ∨ A i ∨ D i ∨ i=2) 0 K := by
    apply cN_mono
    intro i _ _ hi
    have hf:=(local_fourth_sources h M m L s U v i (by omega)).mp (by simpa only [List.append_assoc] using hi)
    rcases hf with h0|h1|h2|h3|h4|h5
    · exact False.elim (Recaman.EqualTargetInitialS.equal_target_initial_excluded u x hu h (j+1) i v hR
        (by omega) hmz (by omega) (by simpa only [Int.natCast_add,Int.natCast_one] using hkeyRaw)
        (by simpa only [x,List.append_assoc] using h0))
    · have hi0:=Recaman.EqualTargetFirstA.equal_target_first_A_zero u hu h M m L s U (j+1) i v
        (by omega) hzero (by omega) B hB
        (by simpa only [Int.natCast_add,Int.natCast_one] using hkeyTarget) h1
      exact Or.inl hi0
    · by_cases hi0 : i=0
      · exact Or.inl hi0
      · obtain ⟨q,hq,hqm,hbal,hkey⟩:=h2
        exact False.elim (Recaman.EqualTargetMiddleSquare.equal_target_middle_positive_excluded u hu C hcu hC4
          h M m L s U v T j i q hh hM6 hR (by omega) hv hT hq hqm
          (by simpa only [List.append_assoc] using hbal)
          (by simpa only [List.append_assoc] using hkey) hmt hat)
    · exact Or.inr (Or.inl h3)
    · exact Or.inr (Or.inr (Or.inl h4))
    · exact Or.inr (Or.inr (Or.inr h5))
  have ha : cN A 0 K≤1 := sourceAt_count_le_one true L _ K
  have hd : cN D 0 K≤1 := sourceAt_count_le_one false s _ K
  have h0 : cN (fun i=>i=0) 0 K≤1 := by apply cN_le_one_of_unique; intros; omega
  have h2 : cN (fun i=>i=2) 0 K≤1 := by apply cN_le_one_of_unique; intros; omega
  have ho1:=cN_or_le (fun i=>i=0) (fun i=>A i ∨ D i ∨ i=2) K
  have ho2:=cN_or_le A (fun i=>D i ∨ i=2) K
  have ho3:=cN_or_le D (fun i=>i=2) K
  omega

end Recaman.EqualTargetLocalFour
