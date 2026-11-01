import Recaman.FirstATargetSquare
import Recaman.OldZeroInitialSource

namespace Recaman.OldZeroLastFive

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.FourthSourceFamilies

theorem old_zero_target_last_five (w : List Bool) (hw : BlockWord w)
    (h M m L s U K Rgap : Nat) (u : List Bool) (huTarget : BlockWord u)
    (hcu : mass u=3) (hbudget : M≤Rgap+1) (B : Int)
    (hB : runKey (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true)= -2*B)
    (hkeyTarget : runKey u=2*B-12*((h : Int)+(m : Int)+(s : Int))-18-2*(Rgap : Int)^2)
    (hzero : M+L+U=h+m+s)
    (hmz : mass (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true)=0)
    (hS : 1≤cntF (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true))
    (hseed : tailOldRay w (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true++List.replicate 3 false) 0) :
    rayCount (w++(List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true++List.replicate 3 false)) K≤5 := by
  let x:=List.replicate M true++List.replicate m false++List.replicate L true++
    List.replicate s false++List.replicate U true
  let z:=List.replicate h false++x
  have hseed0:=hseed
  obtain ⟨t,ht,hmt,hkt⟩:=hseed
  have hu : BlockWord (w.drop t) :=
    block_suffix hw (w.take t) (w.drop t) (List.take_append_drop t w)
  have hmold : mass (w.drop t)-(3 : Int)=1 := by
    have hmass : mass z=0 := by simpa only [z,x,List.append_assoc] using hmz
    have hh : mass (w.drop t)+mass (z++List.replicate 3 false)+(0 : Int)=1 := by
      simpa only [z,x,List.append_assoc,Int.natCast_zero] using hmt
    simp only [mass_append,hmass,mass_rep_false] at hh
    omega
  have hkold : runKey (w.drop t++z++List.replicate 3 false)= -2 := by
    rw [List.append_assoc,runKey_append]
    simpa only [z,x,List.append_assoc] using hkt
  let Q:=sourceAt false m (List.replicate L true++List.replicate s false++
    List.replicate U true++List.replicate 3 false)
  let R:=sourceAt true L (List.replicate s false++List.replicate U true++List.replicate 3 false)
  let A:=sourceAt false s (List.replicate U true++List.replicate 3 false)
  have hcnt : 3≤cntF (z++List.replicate 3 false) := by
    rw [cntF_append,cntF_replicate_S]
    omega
  have hpnt : ∀ i, Recaman.ThreeNonsuppliedData.localSupply
      ((w++(z++List.replicate 3 false))++List.replicate i true)=true → Q i ∨ R i ∨ A i ∨ i=0 ∨ i=2 := by
    intro i hi
    have hh:=(ray_supply_append_iff w (z++List.replicate 3 false) i).mp (by simpa only [List.append_assoc] using hi)
    rcases hh with hold|hloc
    · have hi0:=tailOldRay_clock_unique hw (z++List.replicate 3 false) hcnt i 0 hold
        (by simpa only [z,x,List.append_assoc] using hseed0)
      exact Or.inr (Or.inr (Or.inr (Or.inl hi0)))
    · have hi0 : Recaman.ThreeNonsuppliedData.localSupply
          (List.replicate h false++List.replicate M true++List.replicate m false++
            List.replicate L true++List.replicate s false++List.replicate U true++
            List.replicate 3 false++List.replicate i true)=true := by
        simpa only [z,x,List.append_assoc] using hloc
      rcases (local_fourth_sources h M m L s U 3 i (by decide)).mp hi0 with h0|h1|h2|h3|h4|h5
      · exact False.elim (Recaman.OldZeroInitialSource.old_zero_initial_source_exclusion (w.drop t) x hu h 3 i (by decide)
          (by simpa only [x,List.append_assoc] using hmz)
          (by simpa only [x,List.append_assoc] using hS) hmold hkold
          (by simpa only [x,List.append_assoc] using h0))
      · have hz:=Recaman.FirstATargetSquare.first_A_source_zero u huTarget hcu h M m L s U Rgap i hzero hbudget B hB hkeyTarget h1
        exact Or.inr (Or.inr (Or.inr (Or.inl hz)))
      · exact Or.inl h2
      · exact Or.inr (Or.inl h3)
      · exact Or.inr (Or.inr (Or.inl h4))
      · exact Or.inr (Or.inr (Or.inr (Or.inr h5)))
  have hc : rayCount (w++(z++List.replicate 3 false)) K≤cN (fun i=>Q i ∨ R i ∨ A i ∨ i=0 ∨ i=2) 0 K := by
    apply cN_mono
    intro i _ _ hi
    exact hpnt i hi
  have hq : cN Q 0 K≤1 := sourceAt_count_le_one false m _ K
  have hr : cN R 0 K≤1 := sourceAt_count_le_one true L _ K
  have ha : cN A 0 K≤1 := sourceAt_count_le_one false s _ K
  have h0 : cN (fun i=>i=0) 0 K≤1 := by apply cN_le_one_of_unique; intros; omega
  have h2 : cN (fun i=>i=2) 0 K≤1 := by apply cN_le_one_of_unique; intros; omega
  have ho1:=cN_or_le Q (fun i=>R i ∨ A i ∨ i=0 ∨ i=2) K
  have ho2:=cN_or_le R (fun i=>A i ∨ i=0 ∨ i=2) K
  have ho3:=cN_or_le A (fun i=>i=0 ∨ i=2) K
  have ho4:=cN_or_le (fun i=>i=0) (fun i=>i=2) K
  have hb : rayCount (w++(z++List.replicate 3 false)) K≤5 := by omega
  simpa only [z,x,List.append_assoc] using hb

end Recaman.OldZeroLastFive
