import Recaman.ThirdSPairedSupply

namespace Recaman.ThirdSSaturatedSources

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.AdjacentRunSupply Recaman.FourthSourceFamilies Recaman.ThirdSeparatorClock

/-- Saturating the three-clock suffix forces both earlier source families.
The witnesses may occur at different counted clocks. -/
theorem suffix_three_needs_both (L s U v T : Nat) (hv : 1≤v)
    (h3 : 3≤rayCount (List.replicate L true++(List.replicate s false++
      (List.replicate U true++List.replicate v false))) T) :
    (∃ i, i<T ∧ sourceAt true L
      (List.replicate s false++(List.replicate U true++List.replicate v false)) i) ∧
    (∃ j, j<T ∧ sourceAt false s (List.replicate U true++List.replicate v false) j) := by
  let P:=sourceAt true L
    (List.replicate s false++(List.replicate U true++List.replicate v false))
  let Q:=sourceAt false s (List.replicate U true++List.replicate v false)
  have hP : cN P 0 T≤1 := sourceAt_count_le_one ..
  have hQ : cN Q 0 T≤1 := sourceAt_count_le_one ..
  have h2 : cN (fun i=>i=2) 0 T≤1 := by
    apply cN_le_one_of_unique
    intros
    omega
  have hu1:=cN_or_le P Q T
  have hu2:=cN_or_le (fun i=>P i ∨ Q i) (fun i=>i=2) T
  have hle : rayCount (List.replicate L true++(List.replicate s false++
      (List.replicate U true++List.replicate v false))) T≤
      cN (fun i=>(P i ∨ Q i) ∨ i=2) 0 T := by
    unfold rayCount
    apply cN_mono
    intro i hi hit he
    rcases second_A_or_third_separator_or_pair L s U v i hv he with ha|hs|hc
    · exact Or.inl (Or.inl ha)
    · exact Or.inl (Or.inr hs)
    · exact Or.inr hc
  have posP : 1≤cN P 0 T := by omega
  have posQ : 1≤cN Q 0 T := by omega
  have witness (R : Nat → Prop) (hR : 1≤cN R 0 T) : ∃ i, i<T ∧ R i := by
    by_cases he : ∃ i, i<T ∧ R i
    · exact he
    · exfalso
      have hz : cN R 0 T=0 := by
        apply cN_zero_of
        intro i hi hit hr
        exact he ⟨i,by omega,hr⟩
      omega
  exact ⟨witness P posP,witness Q posQ⟩

/-- All the old prefix is retained. Three earlier constant blocks and
one old clock leave three clocks to the literal late suffix. -/
theorem fourth_seven_needs_late_sources (w : List Bool) (hw : BlockWord w)
    (h M m L s U v T : Nat) (hm : 1≤m) (hs : 1≤s) (hv : 1≤v)
    (h7 : 7≤rayCount (w++(List.replicate h false++List.replicate M true++
      List.replicate m false++List.replicate L true++List.replicate s false++
      List.replicate U true++List.replicate v false)) T) :
    (∃ i, i<T ∧ sourceAt true L
      (List.replicate s false++(List.replicate U true++List.replicate v false)) i) ∧
    (∃ j, j<T ∧ sourceAt false s (List.replicate U true++List.replicate v false) j) := by
  let z:=List.replicate L true++(List.replicate s false++
    (List.replicate U true++List.replicate v false))
  let y:=List.replicate h false++List.replicate M true++List.replicate m false++
    List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false
  have hy : 3≤cntF y := by
    simp only [y,cntF_append,cntF_replicate_S,Recaman.UnitTargetSASProfile.cntF_A]
    omega
  have ho:=block_rayCount_append hw y hy T
  have hp:=run_prefix_ray_budget [(false,h),(true,M),(false,m)] z T
  have hp' : rayCount y T≤3+rayCount z T := by
    simpa only [y,z,runWord,List.length_cons,List.length_nil,List.append_nil,Nat.reduceAdd,
      List.append_assoc] using hp
  have h3 : 3≤rayCount z T := by change 7≤rayCount (w++y) T at h7; omega
  exact suffix_three_needs_both L s U v T hv h3

/-- Counted EndN at the unchanged base supplies both concrete source
witnesses internally, with no target profile or finite history assumption. -/
theorem actual_seven_needs_late_sources (f : Nat → Bool) (n B T h M m L s U v : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w)
    (hword : seg f n B=List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false)
    (hm : 1≤m) (hs : 1≤s) (hv : 1≤v)
    (hA : ∀ i, i<T → f (n+B+i)=true)
    (h7 : 7≤cN (EndN f 0) (n+B) T) :
    (∃ i, i<T ∧ sourceAt true L
      (List.replicate s false++(List.replicate U true++List.replicate v false)) i) ∧
    (∃ j, j<T ∧ sourceAt false s (List.replicate U true++List.replicate v false) j) := by
  have hfull : seg f 0 (n+B)=w++(List.replicate h false++List.replicate M true++
      List.replicate m false++List.replicate L true++List.replicate s false++
      List.replicate U true++List.replicate v false) := by
    rw [seg_add,Nat.zero_add,hpre,hword]
  rw [endable_A_run_count f (n+B) T _ hfull hA] at h7
  exact fourth_seven_needs_late_sources w hw h M m L s U v T hm hs hv h7

end Recaman.ThirdSSaturatedSources
