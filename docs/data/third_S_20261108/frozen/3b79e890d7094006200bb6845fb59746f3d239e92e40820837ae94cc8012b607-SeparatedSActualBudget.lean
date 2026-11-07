import Recaman.ShortSeparatedSSupply

namespace Recaman.SeparatedSActualBudget

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.AdjacentRunSupply Recaman.FourthSourceFamilies Recaman.ThirdSeparatorClock

/-- Both S families share one counted clock even if they overlap. -/
theorem paired_S_count_four (m L s U v K : Nat) (hL : L≤4) (hv : 1≤v) :
    cN (fun i=>sourceAt false m (List.replicate L true++List.replicate s false++
      List.replicate U true++List.replicate v false) i ∨
      sourceAt false s (List.replicate U true++List.replicate v false) i) 0 K≤1 := by
  apply cN_le_one_of_unique
  intro i hi j hj hsi hsj
  rcases hsi with he|hl
  · rcases hsj with hE|hL'
    · exact same_family_clock false m m i j _ he hE
    · exact Recaman.ShortSeparatedSSupply.separated_S_same_clock m L s U v i j hL hv he hL'
  · rcases hsj with hE|hL'
    · exact (Recaman.ShortSeparatedSSupply.separated_S_same_clock m L s U v j i hL hv hE hl).symm
    · exact same_family_clock false s s i j _ hl hL'

/-- The final five-block suffix costs three after the shared S clock. -/
theorem suffix_three (m L s U v K : Nat) (hL : L≤4) (hv : 1≤v) :
    rayCount (List.replicate m false++List.replicate L true++List.replicate s false++
      List.replicate U true++List.replicate v false) K≤3 := by
  let PS:=fun i=>sourceAt false m (List.replicate L true++List.replicate s false++
      List.replicate U true++List.replicate v false) i ∨
      sourceAt false s (List.replicate U true++List.replicate v false) i
  let PA:=sourceAt true L (List.replicate s false++(List.replicate U true++List.replicate v false))
  have hPS : cN PS 0 K≤1 := paired_S_count_four m L s U v K hL hv
  have hPA : cN PA 0 K≤1 := sourceAt_count_le_one true L _ K
  have h2 : cN (fun i=>i=2) 0 K≤1 := by apply cN_le_one_of_unique; intros; omega
  have ho:=cN_or_le PS PA K
  have ho2:=cN_or_le (fun i=>PS i ∨ PA i) (fun i=>i=2) K
  have hle : rayCount (List.replicate m false++List.replicate L true++List.replicate s false++
      List.replicate U true++List.replicate v false) K≤cN (fun i=>(PS i ∨ PA i) ∨ i=2) 0 K := by
    unfold rayCount
    apply cN_mono
    intro i hi hik he
    have he' : Recaman.ThreeNonsuppliedData.localSupply
        ((List.replicate m false++(List.replicate L true++List.replicate s false++
          List.replicate U true++List.replicate v false))++List.replicate i true)=true := by
      simpa only [List.append_assoc] using he
    rcases (local_const_split false m _ i).mp he' with hm|hl
    · exact Or.inl (Or.inl (Or.inl hm))
    · have hl' : Recaman.ThreeNonsuppliedData.localSupply
          ((List.replicate L true++(List.replicate s false++
            (List.replicate U true++List.replicate v false)))++List.replicate i true)=true := by
        simpa only [List.append_assoc] using hl
      rcases second_A_or_third_separator_or_pair L s U v i hv hl' with ha|hs|hc
      · exact Or.inl (Or.inr ha)
      · exact Or.inl (Or.inl (Or.inr hs))
      · exact Or.inr hc
  omega

theorem local_five (h M m L s U v K : Nat) (hL : L≤4) (hv : 1≤v) :
    rayCount (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false) K≤5 := by
  have hp:=run_prefix_ray_budget [(false,h),(true,M)]
    (List.replicate m false++List.replicate L true++List.replicate s false++
      List.replicate U true++List.replicate v false) K
  have hb:=suffix_three m L s U v K hL hv
  simp only [runWord,List.length_cons,List.length_nil,List.append_nil,Nat.reduceAdd,
    List.append_assoc] at hp
  omega

/-- The original last-ray supply is at most six for L<=4, uniformly
in the lengths of all S intervals and in all old suppliers. -/
theorem actual_six (f : Nat → Bool) (n B T h M m L s U v : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w)
    (hword : seg f n B=List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false)
    (hm : 1≤m) (hs : 1≤s) (hv : 1≤v) (hL : L≤4)
    (hA : ∀ i, i<T → f (n+B+i)=true) : cN (EndN f 0) (n+B) T≤6 := by
  let y:=List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false
  have hy : 3≤cntF y := by
    simp only [y,cntF_append,cntF_replicate_S,Recaman.UnitTargetSASProfile.cntF_A]
    omega
  have he:=(Recaman.MixedFinalRayOldBudget.actual_mixed_ray_old_budget f n B T w y
    hw hpre hword hy hA).1
  have hl : rayCount y T≤5 := local_five h M m L s U v T hL hv
  omega

end Recaman.SeparatedSActualBudget
