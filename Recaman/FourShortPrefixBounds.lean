import Recaman.MixedShortAPairBudget

namespace Recaman.FourShortPrefixBounds

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.AdjacentRunSupply

theorem local_one_short_bound (h M m L s U v K : Nat) (hv : 1≤v) :
    (M≤8 → rayCount (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false) K≤5) ∧
    (L≤3 → rayCount (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false) K≤4) := by
  let x:=List.replicate U true++List.replicate v false
  let y:=List.replicate m false++(List.replicate L true++(List.replicate s false++x))
  have hx : rayCount x K≤1 := rayCount_A_S_le_one U v K hv
  have hF : 1≤cntF x := by simp only [x,cntF_append,Recaman.UnitTargetSASProfile.cntF_A,cntF_replicate_S]; omega
  constructor
  · intro hM
    have he:=Recaman.MixedShortAPairBudget.pair_prefix_saving y h M K hM
    have hp:=run_prefix_ray_budget [(false,m),(true,L),(false,s)] x K
    simp only [runWord,List.length_cons,List.length_nil,List.append_nil,Nat.reduceAdd,
      List.append_assoc] at hp
    simp only [x,y,List.append_assoc] at he hp hx ⊢
    omega
  · intro hL
    have he:=Recaman.MixedThreeFamilyBudget.suffix_one_saving x m L s K hF hL
    have hp:=run_prefix_ray_budget [(false,h),(true,M)] y K
    simp only [runWord,List.length_cons,List.length_nil,List.append_nil,Nat.reduceAdd,
      List.append_assoc] at hp
    simp only [x,y,List.append_assoc] at he hp hx ⊢
    omega

theorem actual_one_short_bound (f : Nat → Bool) (n B T h M m L s U v : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w)
    (hword : seg f n B=List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false)
    (hm : 1≤m) (hs : 1≤s) (hv : 1≤v) (hA : ∀ i, i<T → f (n+B+i)=true) :
    (M≤8 → cN (EndN f 0) (n+B) T≤6) ∧
    (L≤3 → cN (EndN f 0) (n+B) T≤5) := by
  let y:=List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false
  have hy : 3≤cntF y := by
    simp only [y,cntF_append,cntF_replicate_S,Recaman.UnitTargetSASProfile.cntF_A]
    omega
  have ho:=(Recaman.MixedFinalRayOldBudget.actual_mixed_ray_old_budget f n B T w y hw hpre hword hy hA).1
  obtain ⟨h6,h5⟩:=local_one_short_bound h M m L s U v T hv
  change M≤8 → rayCount y T≤5 at h6
  change L≤3 → rayCount y T≤4 at h5
  exact ⟨fun hM=>by have he:=h6 hM; omega,fun hL=>by have he:=h5 hL; omega⟩

end Recaman.FourShortPrefixBounds
