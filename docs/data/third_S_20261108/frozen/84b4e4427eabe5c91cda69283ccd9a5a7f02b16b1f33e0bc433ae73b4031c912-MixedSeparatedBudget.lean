import Recaman.MixedSeparatedSources
import Recaman.MixedFinalRayOldBudget

namespace Recaman.MixedSeparatedBudget

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.AdjacentRunSupply Recaman.FourthSourceFamilies Recaman.ThirdSeparatorClock

theorem mixed_S_union_one (x : List Bool) (m L s K : Nat) (hF : 1≤cntF x) (hL : L≤4) :
    cN (fun i=>sourceAt false m (List.replicate L true++(List.replicate s false++x)) i ∨
      sourceAt false s x i) 0 K≤1 := by
  apply cN_le_one_of_unique
  intro i hi j hj hsi hsj
  rcases hsi with he|hl
  · rcases hsj with hE|hL'
    · exact same_family_clock false m m i j _ he hE
    · exact Recaman.MixedSeparatedSources.short_A_same_clock_mixed x m L s i j hF hL he hL'
  · rcases hsj with hE|hL'
    · exact (Recaman.MixedSeparatedSources.short_A_same_clock_mixed x m L s j i hF hL hE hl).symm
    · exact same_family_clock false s s i j _ hl hL'

/-- Three constant intervals cost two beyond their unchanged mixed future.
This is a supply-count saving, not a bound on actual free or rank. -/
theorem suffix_count_saving (x : List Bool) (m L s K : Nat) (hF : 1≤cntF x) (hL : L≤4) :
    rayCount (List.replicate m false++(List.replicate L true++(List.replicate s false++x))) K≤
      2+rayCount x K := by
  let PS:=fun i=>sourceAt false m (List.replicate L true++(List.replicate s false++x)) i ∨
    sourceAt false s x i
  let PA:=sourceAt true L (List.replicate s false++x)
  let PX:=fun i=>Recaman.ThreeNonsuppliedData.localSupply (x++List.replicate i true)=true
  have hPS : cN PS 0 K≤1 := mixed_S_union_one x m L s K hF hL
  have hPA : cN PA 0 K≤1 := sourceAt_count_le_one true L _ K
  have ho:=cN_or_le PS PA K
  have ht:=cN_or_le (fun i=>PS i ∨ PA i) PX K
  have hc : cN PX 0 K=rayCount x K := rfl
  have hle : rayCount (List.replicate m false++(List.replicate L true++(List.replicate s false++x))) K≤
      cN (fun i=>(PS i ∨ PA i) ∨ PX i) 0 K := by
    unfold rayCount
    apply cN_mono
    intro i hi hik he
    rcases (local_const_split false m _ i).mp he with hm|hl
    · exact Or.inl (Or.inl (Or.inl hm))
    · rcases (local_const_split true L _ i).mp hl with ha|hs
      · exact Or.inl (Or.inr ha)
      · rcases (local_const_split false s x i).mp hs with hs|hx
        · exact Or.inl (Or.inl (Or.inr hs))
        · exact Or.inr hx
  omega

/-- An arbitrary number of earlier intervals is retained, with no bound
on the mixed future's run count or on the old BlockWord suppliers. -/
theorem actual_prefix_saving (f : Nat → Bool) (n B T m L s : Nat) (rs : List (Bool × Nat))
    (x w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w)
    (hword : seg f n B=runWord rs++
      (List.replicate m false++(List.replicate L true++(List.replicate s false++x))))
    (hm : 1≤m) (hs : 1≤s) (hF : 1≤cntF x) (hL : L≤4)
    (hA : ∀ i, i<T → f (n+B+i)=true) :
    cN (EndN f 0) (n+B) T≤3+rs.length+rayCount x T := by
  let y:=runWord rs++
    (List.replicate m false++(List.replicate L true++(List.replicate s false++x)))
  have hy : 3≤cntF y := by
    simp only [y,cntF_append,cntF_replicate_S,Recaman.UnitTargetSASProfile.cntF_A]
    omega
  have ho:=(Recaman.MixedFinalRayOldBudget.actual_mixed_ray_old_budget f n B T w y hw hpre hword hy hA).1
  have hp:=run_prefix_ray_budget rs
    (List.replicate m false++(List.replicate L true++(List.replicate s false++x))) T
  have hsuf:=suffix_count_saving x m L s T hF hL
  change rayCount y T≤rs.length+_ at hp
  omega

end Recaman.MixedSeparatedBudget
