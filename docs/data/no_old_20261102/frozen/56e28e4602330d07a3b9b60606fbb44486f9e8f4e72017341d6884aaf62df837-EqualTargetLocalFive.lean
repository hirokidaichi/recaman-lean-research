import Recaman.InitialFirstParityCollision
import Recaman.EqualTargetInitialS
import Recaman.EqualTargetFirstA

namespace Recaman.EqualTargetLocalFive

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.FourthSourceFamilies

/-- After all initial-S sources are excluded, the first-A, middle-S, second-A, third-S and fixed clock2 families cost at most five. This is a raw same-target count bound. -/
theorem equal_target_local_five (u : List Bool) (hu : BlockWord u)
    (h M m L s U R K v : Nat) (hv : 4≤v) (hR : 5≤R) (hzero : M+L+U=h+m+s)
    (hS15 : h+m+s≤15) (hbudget : M≤R+1) (B : Int)
    (hB : runKey (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true)= -2*B)
    (hkeyTarget : runKey u=2*B-4*(v : Int)*((h : Int)+(m : Int)+(s : Int)+(v : Int))+2*(v : Int)^2-2*(R : Int)^2) :
    rayCount (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false) K≤5 := by
  classical
  let x:=List.replicate M true++List.replicate m false++List.replicate L true++List.replicate s false++List.replicate U true
  let I:=sourceAt false h (x++List.replicate v false)
  let F:=sourceAt true M (List.replicate m false++List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false)
  let P:=fun i=>I i ∨ F i
  let Q:=sourceAt false m (List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false)
  let A:=sourceAt true L (List.replicate s false++List.replicate U true++List.replicate v false)
  let D:=sourceAt false s (List.replicate U true++List.replicate v false)
  have hmz : mass (List.replicate h false++x)=0 := by
    simp only [x,mass_append,mass_rep_false,mass_replicate_A]
    omega
  have hSz : cntF (List.replicate h false++x)=h+m+s := by
    have hc:=mass_cntF (List.replicate h false++x)
    have hl : (List.replicate h false++x).length=h+M+m+L+s+U := by
      simp only [x,List.length_append,List.length_replicate,Nat.add_assoc]
    rw [hmz,hl] at hc
    omega
  have hBx : runKey (List.replicate h false++x)= -2*B := by
    simpa only [x,List.append_assoc] using hB
  have hkeyRaw : runKey u= -runKey (List.replicate h false++x)-4*(v : Int)*((cntF (List.replicate h false++x) : Int)+(v : Int))+2*(v : Int)^2-2*(R : Int)^2 := by
    rw [hBx,hSz]
    simp only [Int.natCast_add]
    omega
  have hI : ∀ i, ¬I i := by
    intro i hi
    exact Recaman.EqualTargetInitialS.equal_target_initial_excluded u x hu h R i v hR hv hmz (by omega) hkeyRaw hi
  have hP : cN P 0 K≤1 := by
    have hb : cN P 0 K≤cN F 0 K := by
      apply cN_mono
      intro i _ _ hi
      rcases hi with hi|hi
      · exact False.elim (hI i hi)
      · exact hi
    have hf : cN F 0 K≤1 := sourceAt_count_le_one true M _ K
    omega
  have hc : rayCount (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false) K≤
      cN (fun i=>P i ∨ Q i ∨ A i ∨ D i ∨ i=2) 0 K := by
    apply cN_mono
    intro i _ _ hi
    have hh:=(local_fourth_sources h M m L s U v i (by omega)).mp (by simpa only [List.append_assoc] using hi)
    rcases hh with h0|h1|h2|h3|h4|h5
    · exact Or.inl (Or.inl (by simpa only [I,x,List.append_assoc] using h0))
    · exact Or.inl (Or.inr h1)
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr (Or.inl h3))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h4)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h5)))
  have hq : cN Q 0 K≤1 := sourceAt_count_le_one false m _ K
  have ha : cN A 0 K≤1 := sourceAt_count_le_one true L _ K
  have hd : cN D 0 K≤1 := sourceAt_count_le_one false s _ K
  have h2 : cN (fun i=>i=2) 0 K≤1 := by apply cN_le_one_of_unique; intros; omega
  have ho1:=cN_or_le P (fun i=>Q i ∨ A i ∨ D i ∨ i=2) K
  have ho2:=cN_or_le Q (fun i=>A i ∨ D i ∨ i=2) K
  have ho3:=cN_or_le A (fun i=>D i ∨ i=2) K
  have ho4:=cN_or_le D (fun i=>i=2) K
  omega

end Recaman.EqualTargetLocalFive
