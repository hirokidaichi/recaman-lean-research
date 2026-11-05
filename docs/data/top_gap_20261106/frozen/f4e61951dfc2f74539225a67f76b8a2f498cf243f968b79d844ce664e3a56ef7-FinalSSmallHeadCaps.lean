import Recaman.FinalSLocalKey
import Recaman.ThirdSeparatorClock

namespace Recaman.FinalSSmallHeadCaps

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.FourthSourceFamilies Recaman.AdjacentRunSupply Recaman.ShortCounterFactorBounds
open Recaman.FinalSLocalKey Recaman.ThirdSeparatorClock

private theorem unit_pair_key_ne (q s v : Nat) (hs : 1≤s) (hv : 3≤v) :
    runKey (List.replicate q false++List.replicate 1 true++List.replicate s false++
      List.replicate 1 true++List.replicate v false)≠ -2 := by
  intro hk
  have hh:=fourth_prefix_key q 0 0 1 s 1 v
  simp only [List.replicate_zero,List.append_nil] at hh
  rw [hk] at hh
  let X:=(q : Int)+(s : Int)+(v : Int)
  have hp:=Int.mul_nonneg (show 0≤X by dsimp [X]; omega) (show 0≤X-4 by dsimp [X]; omega)
  dsimp [X] at hp
  grind only

/-- If the head has exactly three A signs in its three runs, all
local sources after the first A reduce to the final pair. -/
theorem unit_head_final_local_three (h m s v T : Nat) (hs : 1≤s) (hv : 3≤v) :
    rayCount (List.replicate h false++List.replicate 1 true++List.replicate m false++
      List.replicate 1 true++List.replicate s false++List.replicate 1 true++List.replicate v false) T≤3 := by
  let z:=List.replicate 1 true++(List.replicate s false++(List.replicate 1 true++List.replicate v false))
  let y:=List.replicate m false++z
  have hlocal : rayCount y T≤1 := by
    have honly (i : Nat) (he : Recaman.ThreeNonsuppliedData.localSupply (y++List.replicate i true)=true) : i=2 := by
      rcases (local_const_split false m z i).mp he with hm|hr
      · obtain ⟨q,_,_,_,hk⟩:=hm
        exact False.elim (unit_pair_key_ne q s v hs hv (by simpa only [z,List.append_assoc] using hk))
      · rcases second_A_or_third_separator_or_pair 1 s 1 v i (by omega) hr with ha|hs'|h2
        · obtain ⟨q,hq,hq1,_,hk⟩:=ha
          have hq' : q=1 := by omega
          exact False.elim (unit_pair_key_ne 0 s v hs hv
            (by simpa only [hq',List.replicate_zero,List.nil_append,List.append_assoc] using hk))
        · have hbad:=third_separator_A_floor s 1 v i (by omega) hs'
          omega
        · exact h2
    unfold rayCount
    apply cN_le_one_of_unique
    intro i _ k _ hi hk
    exact (honly i hi).trans (honly k hk).symm
  have hb:=run_prefix_ray_budget [(false,h),(true,1)] y T
  have hh : rayCount (runWord [(false,h),(true,1)]++y) T≤3 := by
    change rayCount (runWord [(false,h),(true,1)]++y) T≤2+rayCount y T at hb
    omega
  simpa only [y,z,runWord,List.append_nil,List.append_assoc] using hh

private theorem large_separator_two_families_disjoint (M L s U v i k : Nat)
    (hM : 1≤M) (hL : 1≤L) (hs : 1≤s) (hN : M+L+U≤5) (hv : 4≤v)
    (ha : sourceAt true L (List.replicate s false++(List.replicate U true++List.replicate v false)) i)
    (ht : sourceAt false s (List.replicate U true++List.replicate v false) k) : False := by
  have hb:=third_separator_A_floor s U v k (by omega) ht
  have hU : U=3 := by omega
  have hv4 : v=4 := by omega
  obtain ⟨e,he,heL,_,hk⟩:=ha
  have he1 : e=1 := by omega
  have hk' : runKey (List.replicate e true++List.replicate s false++List.replicate U true++
      List.replicate v false)= -2 := by simpa only [List.append_assoc] using hk
  have hh:=fourth_prefix_key 0 0 0 e s U v
  simp only [List.replicate_zero,List.nil_append] at hh
  rw [hk',he1,hU,hv4] at hh
  have hsq : ((s : Int)+3)^2=26 := by grind only
  by_cases hs2 : s≤2
  · have hb:=square_lower 5 ((s : Int)+3) (by omega) (by omega)
    grind only
  · have hb:=square_lower ((s : Int)+3) 6 (by decide) (by omega)
    grind only

theorem small_head_large_separator_local_five (h M m L s U v T : Nat)
    (hM : 1≤M) (hL : 1≤L) (hs : 1≤s) (hN : M+L+U≤5) (hv : 4≤v) :
    rayCount (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false) T≤5 := by
  let x:=List.replicate U true++List.replicate v false
  let y:=List.replicate s false++x
  let z:=List.replicate L true++y
  let P:=fun i=>sourceAt true L y i ∨ sourceAt false s x i
  have hP : cN P 0 T≤1 := by
    apply cN_le_one_of_unique
    intro i _ k _ hi hk
    rcases hi with ha|hs'
    · rcases hk with hb|ht
      · exact same_family_clock true L L i k y ha hb
      · exact False.elim (large_separator_two_families_disjoint M L s U v i k hM hL hs hN hv ha ht)
    · rcases hk with ha|ht
      · exact False.elim (large_separator_two_families_disjoint M L s U v k i hM hL hs hN hv ha hs')
      · exact same_family_clock false s s i k x hs' ht
  have h2 : cN (fun i=>i=2) 0 T≤1 := by apply cN_le_one_of_unique; intros; omega
  have hc : rayCount z T≤cN (fun i=>P i ∨ i=2) 0 T := by
    unfold rayCount
    apply cN_mono
    intro i _ _ he
    rcases second_A_or_third_separator_or_pair L s U v i (by omega) he with ha|ht|hclock
    · exact Or.inl (Or.inl ha)
    · exact Or.inl (Or.inr ht)
    · exact Or.inr hclock
  have hres : rayCount z T≤2 := by
    have hh:=cN_or_le P (fun i=>i=2) T
    omega
  have hp:=run_prefix_ray_budget [(false,h),(true,M),(false,m)] z T
  have hh : rayCount (runWord [(false,h),(true,M),(false,m)]++z) T≤5 := by
    change rayCount (runWord [(false,h),(true,M),(false,m)]++z) T≤3+rayCount z T at hp
    omega
  simpa only [runWord,z,y,x,List.append_nil,List.append_assoc] using hh

end Recaman.FinalSSmallHeadCaps
