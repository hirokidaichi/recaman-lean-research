import Recaman.ThirdSResidualSquare
import Recaman.MixedFinalRayOldBudget

namespace Recaman.ThirdSPairedSupply

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.AdjacentRunSupply Recaman.FourthSourceFamilies Recaman.ThirdSeparatorClock

/-- The two concrete source families share one budget even though their
clock parameters are independent in the key collision theorem. -/
theorem paired_source_count (L s U v K : Nat) (hL : L≤3) (hlen : 12≤s+v) :
    cN (fun i => sourceAt true L
      (List.replicate s false++(List.replicate U true++List.replicate v false)) i ∨
      sourceAt false s (List.replicate U true++List.replicate v false) i) 0 K≤1 := by
  apply cN_le_one_of_unique
  intro i hi j hj hsi hsj
  rcases hsi with ha|hs
  · rcases hsj with hb|ht
    · exact same_family_clock true L L i j _ ha hb
    · exact False.elim (Recaman.ThirdSResidualSquare.second_A_third_S_key_collision
        L s U v i j hL hlen ha ht)
  · rcases hsj with hb|ht
    · exact False.elim (Recaman.ThirdSResidualSquare.second_A_third_S_key_collision
        L s U v j i hL hlen hb hs)
    · exact same_family_clock false s s i j _ hs ht

/-- The paired families and the terminal clock2 together cost at most two. -/
theorem paired_suffix_count (L s U v K : Nat) (hL : L≤3) (hlen : 12≤s+v) (hv : 1≤v) :
    rayCount (List.replicate L true++(List.replicate s false++
      (List.replicate U true++List.replicate v false))) K≤2 := by
  let P:=fun i => sourceAt true L
    (List.replicate s false++(List.replicate U true++List.replicate v false)) i ∨
    sourceAt false s (List.replicate U true++List.replicate v false) i
  have hP : cN P 0 K≤1 := paired_source_count L s U v K hL hlen
  have h2 : cN (fun i=>i=2) 0 K≤1 := by
    apply cN_le_one_of_unique
    intros
    omega
  have hU:=cN_or_le P (fun i=>i=2) K
  have hle : rayCount (List.replicate L true++(List.replicate s false++
      (List.replicate U true++List.replicate v false))) K≤cN (fun i=>P i ∨ i=2) 0 K := by
    unfold rayCount
    apply cN_mono
    intro i hi hik he
    rcases second_A_or_third_separator_or_pair L s U v i hv he with ha|hs|hc
    · exact Or.inl (Or.inl ha)
    · exact Or.inl (Or.inr hs)
    · exact Or.inr hc
  omega

/-- The literal local fourth-ray word costs five under the paired key cut. -/
theorem fourth_local_paired_count (h M m L s U v K : Nat)
    (hL : L≤3) (hlen : 12≤s+v) (hv : 1≤v) :
    rayCount (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false) K≤5 := by
  have hp:=run_prefix_ray_budget [(false,h),(true,M),(false,m)]
    (List.replicate L true++(List.replicate s false++
      (List.replicate U true++List.replicate v false))) K
  have hb:=paired_suffix_count L s U v K hL hlen hv
  simp only [runWord,List.length_cons,List.length_nil,List.append_nil,Nat.reduceAdd,
    List.append_assoc] at hp
  simp only [List.append_assoc] at hb ⊢
  omega

/-- The original base and all old suppliers are retained in the six-clock cut. -/
theorem actual_paired_six (f : Nat → Bool) (n B T h M m L s U v : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w)
    (hword : seg f n B=List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false)
    (hm : 1≤m) (hs : 1≤s) (hv : 1≤v) (hL : L≤3) (hlen : 12≤s+v)
    (hA : ∀ i, i<T → f (n+B+i)=true) :
    cN (EndN f 0) (n+B) T≤6 := by
  let y:=List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false
  have hy : 3≤cntF y := by
    simp only [y,cntF_append,cntF_replicate_S,Recaman.UnitTargetSASProfile.cntF_A]
    omega
  have he:=(Recaman.MixedFinalRayOldBudget.actual_mixed_ray_old_budget f n B T w y
    hw hpre hword hy hA).1
  have hl : rayCount y T≤5 := fourth_local_paired_count h M m L s U v T hL hlen hv
  omega

end Recaman.ThirdSPairedSupply
