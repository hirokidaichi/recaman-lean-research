import Recaman.FourthSourceFamilies
import Recaman.UnitTargetSASProfile

namespace Recaman.FourthSaturationSources

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.AdjacentRunSupply Recaman.FourthSourceFamilies Recaman.UnitTargetSASProfile

/-- Saturating seven clocks requires an old source and an initial-S
source within the counted interval. A source outside that interval cannot pay. -/
theorem fourth_seven_sources (w : List Bool) (hw : BlockWord w) (h M m L s U v T : Nat)
    (hm : 1≤m) (hs : 1≤s) (hv : 1≤v) :
    let x:=List.replicate M true++List.replicate m false++List.replicate L true++
      List.replicate s false++List.replicate U true++List.replicate v false
    let y:=List.replicate h false++x
    7≤rayCount (w++y) T →
      (∃ i, i<T ∧ tailOldRay w y i) ∧ (∃ k, k<T ∧ sourceAt false h x k) := by
  dsimp only
  let x:=List.replicate M true++List.replicate m false++List.replicate L true++
    List.replicate s false++List.replicate U true++List.replicate v false
  let y:=List.replicate h false++x
  change 7≤rayCount (w++y) T →
    (∃ i, i<T ∧ tailOldRay w y i) ∧ (∃ k, k<T ∧ sourceAt false h x k)
  intro h7
  have hlocal : rayCount y T≤6 := by
    simpa only [y,x,List.append_assoc] using fourth_ray_local_le_six h M m L s U v T hv
  have hrest : rayCount x T≤5 := by
    have hp:=run_prefix_ray_budget [(true,M),(false,m),(true,L),(false,s)]
      (List.replicate U true++List.replicate v false) T
    have hb:=rayCount_A_S_le_one U v T hv
    simp only [runWord,List.length_cons,List.length_nil,List.append_nil,Nat.reduceAdd,
      List.append_assoc] at hp
    have hh : rayCount (List.replicate M true++(List.replicate m false++(List.replicate L true++
        (List.replicate s false++(List.replicate U true++List.replicate v false))))) T≤5 := by omega
    simpa only [x,List.append_assoc] using hh
  have hS : 3≤cntF y := by
    simp only [y,x,cntF_append,cntF_A,cntF_replicate_S]
    omega
  have hb:=block_rayCount_append hw y hS T
  constructor
  · by_cases hp : ∃ i, i<T ∧ tailOldRay w y i
    · exact hp
    · exfalso
      have he : rayCount (w++y) T=rayCount y T := by
        apply cN_congr
        intro i _ hi
        rw [ray_supply_append_iff]
        exact or_iff_right (fun ho=>hp ⟨i,by omega,ho⟩)
      omega
  · by_cases hp : ∃ k, k<T ∧ sourceAt false h x k
    · exact hp
    · exfalso
      have he : rayCount y T=rayCount x T := by
        apply cN_congr
        intro i _ hi
        change Recaman.ThreeNonsuppliedData.localSupply ((List.replicate h false++x)++List.replicate i true)=true ↔ _
        rw [local_const_split]
        exact or_iff_right (fun ho=>hp ⟨i,by omega,ho⟩)
      omega

end Recaman.FourthSaturationSources
