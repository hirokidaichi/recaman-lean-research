import Recaman.ShortGapSourceClocks

namespace Recaman.FourthSourceFamilies

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.AdjacentRunSupply Recaman.ShortGapSourceClocks

/-- A concrete suffix source in one constant run. This relation contains
its exact word mass/key, not an independent Endable or supply tag. -/
def sourceAt (b : Bool) (N : Nat) (x : List Bool) (i : Nat) : Prop :=
  ∃ k, 1≤k ∧ k≤N ∧ mass (List.replicate k b++x)+(i : Int)=1 ∧
    runKey (List.replicate k b++x)= -2

theorem sourceAt_count_le_one (b : Bool) (N : Nat) (x : List Bool) (K : Nat) :
    cN (sourceAt b N x) 0 K≤1 := by
  apply cN_le_one_of_unique
  intro i hi j hj hsi hsj
  obtain ⟨k,hk,hkN,hmk,hkk⟩:=hsi
  obtain ⟨l,hl,hlN,hml,hkl⟩:=hsj
  have hkl':=constant_run_root_unique b k l x hk hl hkk hkl
  subst l
  omega

private theorem local_const_split (b : Bool) (N : Nat) (x : List Bool) (i : Nat) :
    Recaman.ThreeNonsuppliedData.localSupply ((List.replicate N b++x)++List.replicate i true)=true ↔
      sourceAt b N x i ∨ Recaman.ThreeNonsuppliedData.localSupply (x++List.replicate i true)=true := by
  let P:=fun y : List Bool=>mass y+(i : Int)=1 ∧ runKey y= -2
  have h1 : Recaman.ThreeNonsuppliedData.localSupply ((List.replicate N b++x)++List.replicate i true)=true ↔
      ∃ t, t<(List.replicate N b++x).length ∧ P ((List.replicate N b++x).drop t) := by
    simpa [P] using localSupply_A_S_iff (List.replicate N b++x) i 0
  have h2 : Recaman.ThreeNonsuppliedData.localSupply (x++List.replicate i true)=true ↔
      ∃ t, t<x.length ∧ P (x.drop t) := by
    simpa [P] using localSupply_A_S_iff x i 0
  rw [h1,exists_drop_append,←h2]
  apply or_congr
  · simp only [sourceAt,P,List.length_replicate,List.drop_replicate]
    constructor
    · rintro ⟨t,ht,hm,hk⟩
      exact ⟨N-t,by omega,by omega,hm,hk⟩
    · rintro ⟨k,hk,hkN,hm,he⟩
      exact ⟨N-k,by omega,by simpa only [show N-(N-k)=k by omega] using hm,
        by simpa only [show N-(N-k)=k by omega] using he⟩
  · rfl

/-- Exact decomposition of local supply into five earlier source
families and the last A/S pair's single clock2. -/
theorem local_fourth_sources (h M m L s U v i : Nat) (hv : 1≤v) :
    Recaman.ThreeNonsuppliedData.localSupply
      (List.replicate h false++List.replicate M true++List.replicate m false++
        List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false++
        List.replicate i true)=true ↔
    sourceAt false h (List.replicate M true++List.replicate m false++List.replicate L true++
      List.replicate s false++List.replicate U true++List.replicate v false) i ∨
    sourceAt true M (List.replicate m false++List.replicate L true++List.replicate s false++
      List.replicate U true++List.replicate v false) i ∨
    sourceAt false m (List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false) i ∨
    sourceAt true L (List.replicate s false++List.replicate U true++List.replicate v false) i ∨
    sourceAt false s (List.replicate U true++List.replicate v false) i ∨ i=2 := by
  have h0:=local_const_split false h (List.replicate M true++List.replicate m false++List.replicate L true++
    List.replicate s false++List.replicate U true++List.replicate v false) i
  have h1:=local_const_split true M (List.replicate m false++List.replicate L true++List.replicate s false++
    List.replicate U true++List.replicate v false) i
  have h2:=local_const_split false m (List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false) i
  have h3:=local_const_split true L (List.replicate s false++List.replicate U true++List.replicate v false) i
  have h4:=local_const_split false s (List.replicate U true++List.replicate v false) i
  have h5:=local_A_S_clock_iff U v i hv
  simp only [List.append_assoc] at h0 h1 h2 h3 h4 h5
  rw [h1,h2,h3,h4,h5] at h0
  simpa only [List.append_assoc] using h0

/-- A source in the initial S run obeys the short-gap moment rule while
the entire original head remains the word used to measure the band. -/
theorem initial_family_small_clock (h v i : Nat) (x : List Bool) (B : Int)
    (hm : mass (List.replicate h false++x)=0)
    (ha : areaW (List.replicate h false++x)= -B)
    (hS : 3≤cntF (List.replicate h false++x))
    (hlo : 4*(cntF (List.replicate h false++x) : Int)+6≤B)
    (hhi : B≤6*(cntF (List.replicate h false++x) : Int)+4)
    (hv : 1≤v) (hv3 : v≤3)
    (he : sourceAt false h (x++List.replicate v false) i) :
    (v=2 ∧ i=0) ∨ (v=3 ∧ i=1) := by
  obtain ⟨q,hq,hqh,hbal,hkey⟩:=he
  let d:=h-q
  have hd : d≤h := by dsimp [d]; omega
  have heq : List.replicate h false++x=List.replicate d false++(List.replicate q false++x) := by
    have htake : (List.replicate h false).take d=List.replicate d false := by
      rw [List.take_replicate,Nat.min_eq_left hd]
    have hdrop : (List.replicate h false).drop d=List.replicate q false := by
      rw [List.drop_replicate,show h-d=q by dsimp [d]; omega]
    rw [←htake,←hdrop,←List.append_assoc,List.take_append_drop]
  have hc:=initial_S_small_gap_clock d v i (List.replicate q false++x) B
    (by rw [←heq]; exact hm) (by rw [←heq]; exact ha)
    (by rw [←heq]; exact hS) (by rw [←heq]; exact hlo) (by rw [←heq]; exact hhi) hv hv3
    (by simpa only [List.append_assoc] using hbal) (by simpa only [List.append_assoc] using hkey)
  rcases hc with h|h
  · exact Or.inl ⟨h.1,h.2.1⟩
  · exact Or.inr ⟨h.1,h.2.1⟩

theorem zero_two_count (K : Nat) : cN (fun i=>i=0 ∨ i=2) 0 K≤2 := by
  have h0 : cN (fun i=>i=0) 0 K≤1 := by apply cN_le_one_of_unique; intros; omega
  have h2 : cN (fun i=>i=2) 0 K≤1 := by apply cN_le_one_of_unique; intros; omega
  have hh:=cN_or_le (fun i=>i=0) (fun i=>i=2) K
  omega

end Recaman.FourthSourceFamilies
