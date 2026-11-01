import Recaman.InitialFirstParityCollision
import Recaman.OffsetOneInitialSource
import Recaman.OffsetOneFirstASource

namespace Recaman.OffsetOneLocalFive

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.FourthSourceFamilies

/-- For separator v>=5 and the stated same-target key, the initial-S and first-A families jointly cost at most one clock. The other three families and fixed clock2 remain. -/
theorem offset_one_local_five (u : List Bool) (hu : BlockWord u)
    (h M m L s U R K v : Nat) (hv : 5≤v) (hR : 5≤R) (hzero : M+L+U=h+m+s)
    (hS15 : h+m+s≤15) (hbudget : M≤R+1) (B : Int)
    (hB : runKey (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true)= -2*B)
    (hkeyTarget : runKey u=2*B-4*((v : Int)-1)*((h : Int)+(m : Int)+(s : Int)+(v : Int))+2*(v : Int)^2-2*(R : Int)^2) :
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
  have hkeyRaw : runKey u= -runKey (List.replicate h false++x)-4*((v : Int)-1)*((cntF (List.replicate h false++x) : Int)+(v : Int))+2*(v : Int)^2-2*(R : Int)^2 := by
    rw [hBx,hSz]
    simp only [Int.natCast_add]
    omega
  have hiZero : ∀ i, I i → i=0 := by
    intro i hi
    exact Recaman.OffsetOneInitialSource.offset_one_initial_zero u x hu h R i v hR hv hmz (by omega) hkeyRaw hi
  have hP : cN P 0 K≤1 := by
    by_cases hinit : I 0
    · have hfZero : ∀ i, F i → i=0 := by
        intro i hi
        have hb:=Recaman.OffsetOneFirstASource.offset_one_first_A_one u hu h M m L s U R i v hv hzero hbudget B hB hkeyTarget hi
        by_cases hi0 : i=0
        · exact hi0
        · have hi1 : i=1 := by omega
          have hn:=Recaman.InitialFirstParityCollision.initial_zero_first_one_excluded_all_v h M m L s U v hzero
            (by simpa only [I,x,List.append_assoc] using hinit)
          exact False.elim (hn (by simpa only [F,hi1] using hi))
      apply cN_le_one_of_unique
      intro i _ j _ hi hj
      have hi0 : i=0 := by rcases hi with hi|hi; exact hiZero i hi; exact hfZero i hi
      have hj0 : j=0 := by rcases hj with hj|hj; exact hiZero j hj; exact hfZero j hj
      omega
    · have hc : cN P 0 K≤cN F 0 K := by
        apply cN_mono
        intro i _ _ hi
        rcases hi with hi|hi
        · have hi0:=hiZero i hi
          subst i
          exact False.elim (hinit hi)
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

end Recaman.OffsetOneLocalFive
