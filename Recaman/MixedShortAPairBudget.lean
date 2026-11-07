import Recaman.MixedThreeFamilyBudget

namespace Recaman.MixedShortAPairBudget

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.AdjacentRunSupply Recaman.FourthSourceFamilies Recaman.ThirdSeparatorClock

theorem pair_count_one (x : List Bool) (h M K : Nat) (hM : M≤8) :
    cN (fun i=>sourceAt false h (List.replicate M true++x) i ∨ sourceAt true M x i) 0 K≤1 := by
  apply cN_le_one_of_unique
  intro i hi j hj hsi hsj
  rcases hsi with hs|ha
  · rcases hsj with ht|hb
    · exact same_family_clock false h h i j _ hs ht
    · exact False.elim (Recaman.MixedShortASources.short_A_S_A_collision x h M i j hM hs hb)
  · rcases hsj with ht|hb
    · exact False.elim (Recaman.MixedShortASources.short_A_S_A_collision x h M j i hM ht ha)
    · exact same_family_clock true M M i j _ ha hb

/-- A short A and its preceding S cost one beyond their unchanged future. -/
theorem pair_prefix_saving (x : List Bool) (h M K : Nat) (hM : M≤8) :
    rayCount (List.replicate h false++(List.replicate M true++x)) K≤1+rayCount x K := by
  let P:=fun i=>sourceAt false h (List.replicate M true++x) i ∨ sourceAt true M x i
  let PX:=fun i=>Recaman.ThreeNonsuppliedData.localSupply (x++List.replicate i true)=true
  have hp : cN P 0 K≤1 := pair_count_one x h M K hM
  have hu:=cN_or_le P PX K
  have hx : cN PX 0 K=rayCount x K := rfl
  have hle : rayCount (List.replicate h false++(List.replicate M true++x)) K≤
      cN (fun i=>P i ∨ PX i) 0 K := by
    unfold rayCount
    apply cN_mono
    intro i hi hiK he
    rcases (local_const_split false h _ i).mp he with hs|hl
    · exact Or.inl (Or.inl hs)
    · rcases (local_const_split true M x i).mp hl with ha|hx
      · exact Or.inl (Or.inr ha)
      · exact Or.inr hx
  omega

theorem fourth_local_bounds (h M m L s U v K : Nat) (hM : M≤8) (hL : L≤8) (hv : 1≤v) :
    rayCount (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false) K≤4 ∧
    (L≤3 → rayCount (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false) K≤3) := by
  let x:=List.replicate U true++List.replicate v false
  let y:=List.replicate m false++(List.replicate L true++(List.replicate s false++x))
  have hF : 1≤cntF x := by simp only [x,cntF_append,Recaman.UnitTargetSASProfile.cntF_A,cntF_replicate_S]; omega
  have htail : rayCount x K≤1 := rayCount_A_S_le_one U v K hv
  have hp:=pair_prefix_saving y h M K hM
  have hm:=pair_prefix_saving (List.replicate s false++x) m L K hL
  have hs:=rayCount_const_append false s x K
  have hshort (hL3 : L≤3) : rayCount y K≤1+rayCount x K :=
    Recaman.MixedThreeFamilyBudget.suffix_one_saving x m L s K hF hL3
  simp only [x,y,List.append_assoc] at hp hm hs htail ⊢
  refine ⟨by omega,?_⟩
  intro hL3
  have hb:=hshort hL3
  simp only [x,y,List.append_assoc] at hb
  omega

/-- Both bounds are counts at the original base with every old supplier retained. -/
theorem actual_fourth_bounds (f : Nat → Bool) (n B T h M m L s U v : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w)
    (hword : seg f n B=List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false)
    (hm : 1≤m) (hs : 1≤s) (hv : 1≤v) (hM : M≤8) (hL : L≤8)
    (hA : ∀ i, i<T → f (n+B+i)=true) :
    cN (EndN f 0) (n+B) T≤5 ∧ (L≤3 → cN (EndN f 0) (n+B) T≤4) := by
  let y:=List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false
  have hy : 3≤cntF y := by
    simp only [y,cntF_append,cntF_replicate_S,Recaman.UnitTargetSASProfile.cntF_A]
    omega
  have ho:=(Recaman.MixedFinalRayOldBudget.actual_mixed_ray_old_budget f n B T w y hw hpre hword hy hA).1
  obtain ⟨h5,h4⟩:=fourth_local_bounds h M m L s U v T hM hL hv
  change rayCount y T≤4 at h5
  change L≤3 → rayCount y T≤3 at h4
  exact ⟨by omega,fun hL3=>by have hh:=h4 hL3; omega⟩

end Recaman.MixedShortAPairBudget
