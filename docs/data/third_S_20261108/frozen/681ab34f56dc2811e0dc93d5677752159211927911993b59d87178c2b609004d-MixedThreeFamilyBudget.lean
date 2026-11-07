import Recaman.MixedSeparatedBudget
import Recaman.MixedShortASources

namespace Recaman.MixedThreeFamilyBudget

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.AdjacentRunSupply Recaman.FourthSourceFamilies Recaman.ThirdSeparatorClock

private theorem short_A_later_S_collision (x : List Bool) (L s i j : Nat) (hL : L≤3)
    (ha : sourceAt true L (List.replicate s false++x) i)
    (hs : sourceAt false s x j) : False := by
  obtain ⟨a,ha4,haL,_,_,_,_⟩:=Recaman.MixedASQuarterBudget.mixed_A_S_quarter_budget x L s i j ha hs
  omega

/-- The three concrete S/A/S families have at most one supplied clock,
for arbitrary mixed futures containing a subtraction. -/
theorem three_family_one (x : List Bool) (m L s K : Nat) (hF : 1≤cntF x) (hL : L≤3) :
    cN (fun i=>sourceAt false m (List.replicate L true++(List.replicate s false++x)) i ∨
      sourceAt true L (List.replicate s false++x) i ∨ sourceAt false s x i) 0 K≤1 := by
  apply cN_le_one_of_unique
  intro i hi j hj hsi hsj
  rcases hsi with he|ha|hl
  · rcases hsj with hE|hA|hL'
    · exact same_family_clock false m m i j _ he hE
    · exact False.elim (Recaman.MixedShortASources.short_A_S_A_collision
        (List.replicate s false++x) m L i j (by omega) he hA)
    · exact Recaman.MixedSeparatedSources.short_A_same_clock_mixed x m L s i j hF (by omega) he hL'
  · rcases hsj with hE|hA|hL'
    · exact False.elim (Recaman.MixedShortASources.short_A_S_A_collision
        (List.replicate s false++x) m L j i (by omega) hE ha)
    · exact same_family_clock true L L i j _ ha hA
    · exact False.elim (short_A_later_S_collision x L s i j hL ha hL')
  · rcases hsj with hE|hA|hL'
    · exact (Recaman.MixedSeparatedSources.short_A_same_clock_mixed x m L s j i hF (by omega) hE hl).symm
    · exact False.elim (short_A_later_S_collision x L s j i hL hA hl)
    · exact same_family_clock false s s i j _ hl hL'

/-- Compressing three source intervals costs one beyond their unchanged
mixed future. This is a count inequality, without resetting that future. -/
theorem suffix_one_saving (x : List Bool) (m L s K : Nat) (hF : 1≤cntF x) (hL : L≤3) :
    rayCount (List.replicate m false++(List.replicate L true++(List.replicate s false++x))) K≤
      1+rayCount x K := by
  let P:=fun i=>sourceAt false m (List.replicate L true++(List.replicate s false++x)) i ∨
    sourceAt true L (List.replicate s false++x) i ∨ sourceAt false s x i
  let PX:=fun i=>Recaman.ThreeNonsuppliedData.localSupply (x++List.replicate i true)=true
  have hP : cN P 0 K≤1 := three_family_one x m L s K hF hL
  have ho:=cN_or_le P PX K
  have hc : cN PX 0 K=rayCount x K := rfl
  have hle : rayCount (List.replicate m false++(List.replicate L true++(List.replicate s false++x))) K≤
      cN (fun i=>P i ∨ PX i) 0 K := by
    unfold rayCount
    apply cN_mono
    intro i hi hik he
    rcases (local_const_split false m _ i).mp he with hm|hl
    · exact Or.inl (Or.inl hm)
    · rcases (local_const_split true L _ i).mp hl with ha|hs
      · exact Or.inl (Or.inr (Or.inl ha))
      · rcases (local_const_split false s x i).mp hs with hs|hx
        · exact Or.inl (Or.inr (Or.inr hs))
        · exact Or.inr hx
  omega

/-- All earlier intervals and the old history are kept in the original
actual count; the saving applies for every number of future runs. -/
theorem actual_prefix_two_saving (f : Nat → Bool) (n B T m L s : Nat) (rs : List (Bool × Nat))
    (x w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w)
    (hword : seg f n B=runWord rs++
      (List.replicate m false++(List.replicate L true++(List.replicate s false++x))))
    (hm : 1≤m) (hs : 1≤s) (hF : 1≤cntF x) (hL : L≤3)
    (hA : ∀ i, i<T → f (n+B+i)=true) :
    cN (EndN f 0) (n+B) T≤2+rs.length+rayCount x T := by
  let y:=runWord rs++
    (List.replicate m false++(List.replicate L true++(List.replicate s false++x)))
  have hy : 3≤cntF y := by
    simp only [y,cntF_append,cntF_replicate_S,Recaman.UnitTargetSASProfile.cntF_A]
    omega
  have ho:=(Recaman.MixedFinalRayOldBudget.actual_mixed_ray_old_budget f n B T w y hw hpre hword hy hA).1
  have hp:=run_prefix_ray_budget rs
    (List.replicate m false++(List.replicate L true++(List.replicate s false++x))) T
  have hsuf:=suffix_one_saving x m L s T hF hL
  change rayCount y T≤rs.length+_ at hp
  omega

end Recaman.MixedThreeFamilyBudget
