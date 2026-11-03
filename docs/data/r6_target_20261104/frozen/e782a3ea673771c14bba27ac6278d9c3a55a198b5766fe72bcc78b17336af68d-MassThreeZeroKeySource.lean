import Recaman.OldZeroInitialSource

namespace Recaman.MassThreeZeroKeySource

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.FourthSourceFamilies

theorem initial_source_excluded (u x : List Bool)
    (h v i : Nat) (hv : v=3 ∨ v=4)
    (hmz : mass (List.replicate h false++x)=0)
    (hsum : cntF (List.replicate h false++x)+v=17)
    (hD : mass u=3) (hku0 : runKey u=0)
    (hkold : runKey (u++(List.replicate h false++x)++List.replicate v false)= -2) :
    ¬sourceAt false h (x++List.replicate v false) i := by
  rintro ⟨q,hq,hqh,hbal,hkey⟩
  let d:=h-q
  let r:=List.replicate q false++x
  let S:=(cntF (List.replicate h false++x) : Int)
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
  have hcr : (cntF r : Int)=S-(d : Int) := by
    have hc:=cntF_append (List.replicate d false) r
    rw [←hsplit,cntF_replicate_S] at hc
    dsimp [S]
    omega
  have hkeyr : runKey (r++List.replicate v false)= -2 := by
    simpa only [r,List.append_assoc] using hkey
  rw [runKey_append_S,hmr] at hkeyr
  have hdi : (d : Int)+(i : Int)=(v : Int)+1 := by
    have hbalr : mass (r++List.replicate v false)+(i : Int)=1 := by
      simpa only [r,List.append_assoc] using hbal
    rw [mass_append,hmr,mass_rep_false] at hbalr
    omega
  have hkz : runKey (List.replicate h false++x)=runKey r-4*(d : Int)*(S-(d : Int))-2*(d : Int)^2 := by
    rw [hsplit,runKey_prepend_S,hcr]
  rw [runKey_append_S,runKey_append,mass_append,hmz,hkz,hD] at hkold
  have hku : runKey u=4*((d : Int)-3)*(S+(v : Int))-2*(d : Int)^2 := by grind only
  have hsum17 : S+(v : Int)=17 := by dsimp [S]; omega
  rw [hku0,hsum17] at hku
  have hd5 : d≤5 := by rcases hv with hv|hv <;> omega
  rcases (show d=0 ∨ d=1 ∨ d=2 ∨ d=3 ∨ d=4 ∨ d=5 by omega) with hd|hd|hd|hd|hd|hd <;>
    rw [hd] at hku <;> omega

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

end Recaman.MassThreeZeroKeySource
