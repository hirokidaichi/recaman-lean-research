import Recaman.TenHeadTargetCases

namespace Recaman.TenHeadSourcePruning

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.AdjacentRunSupply

private theorem square_gap (x k d : Int) (hk : 0≤k)
    (hlo : k*k<d) (hhi : d<(k+1)*(k+1)) : x*x≠d := by
  have nonneg_case (y : Int) (hy : 0≤y) : y*y≠d := by
    intro he
    by_cases hh : y≤k
    · have hp:=Int.mul_nonneg (show 0≤k-y by omega) (show 0≤k+y by omega)
      grind only
    · have hp:=Int.mul_nonneg (show 0≤y-k-1 by omega) (show 0≤y+k+1 by omega)
      grind only
  by_cases hx : 0≤x
  · exact nonneg_case x hx
  · have h:=nonneg_case (-x) (by omega)
    intro he
    apply h
    grind only

/-- Removing an initial S prefix from the same moment-constrained head
cannot expose a local key-2 source in either target-derived case. The
head following that prefix remains arbitrary. -/
theorem initial_S_source_excluded (d v : Nat) (x : List Bool) (B : Int)
    (hm : mass (List.replicate d false++x)=0)
    (hS : cntF (List.replicate d false++x)=10)
    (ha : areaW (List.replicate d false++x)= -B)
    (hc : (v=1 ∧ B=46) ∨ (v=2 ∧ B=56)) :
    runKey (x++List.replicate v false)≠ -2 := by
  intro hk
  have hkey : runKey (List.replicate d false++x)= -2*B := by
    unfold runKey
    rw [hm,ha]
    grind only
  rw [mass_append,mass_rep_false] at hm
  rw [cntF_append,cntF_replicate_S] at hS
  rw [runKey_prepend_S] at hkey
  rw [runKey_append_S] at hk
  have he : ((d : Int)-(10+(v : Int)))^2=101+20*(v : Int)-B := by
    have hSc : (cntF x : Int)=10-(d : Int) := by omega
    rw [hSc] at hkey
    grind only
  rcases hc with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact square_gap ((d : Int)-11) 8 75 (by decide) (by decide) (by decide) (by grind only)
  · exact square_gap ((d : Int)-12) 9 85 (by decide) (by decide) (by decide) (by grind only)

private theorem local_append_split (u x : List Bool) (i : Nat) :
    Recaman.ThreeNonsuppliedData.localSupply ((u++x)++List.replicate i true)=true ↔
      (∃ t, t<u.length ∧ mass (u.drop t++x)+(i : Int)=1 ∧ runKey (u.drop t++x)= -2) ∨
      Recaman.ThreeNonsuppliedData.localSupply (x++List.replicate i true)=true := by
  let P:=fun y : List Bool=>mass y+(i : Int)=1 ∧ runKey y= -2
  have h1 : Recaman.ThreeNonsuppliedData.localSupply ((u++x)++List.replicate i true)=true ↔
      ∃ t, t<(u++x).length ∧ P ((u++x).drop t) := by
    simpa [P] using localSupply_A_S_iff (u++x) i 0
  have h2 : Recaman.ThreeNonsuppliedData.localSupply (x++List.replicate i true)=true ↔
      ∃ t, t<x.length ∧ P (x.drop t) := by
    simpa [P] using localSupply_A_S_iff x i 0
  rw [h1,exists_drop_append,←h2]

/-- The initial S block is erased only for local ray counting, after
its impossible square condition has been proved for every source. -/
theorem initial_S_ray_erasure (h v K : Nat) (x : List Bool) (B : Int)
    (hm : mass (List.replicate h false++x)=0)
    (hS : cntF (List.replicate h false++x)=10)
    (ha : areaW (List.replicate h false++x)= -B)
    (hc : (v=1 ∧ B=46) ∨ (v=2 ∧ B=56)) :
    rayCount (List.replicate h false++x++List.replicate v false) K=
      rayCount (x++List.replicate v false) K := by
  apply cN_congr
  intro i _ _
  rw [List.append_assoc,local_append_split]
  apply or_iff_right
  rintro ⟨t,ht,_,hk⟩
  have ht' : t≤h := by simp only [List.length_replicate] at ht; omega
  have heq : List.replicate h false++x=List.replicate t false++((List.replicate h false).drop t++x) := by
    rw [List.drop_replicate,←List.append_assoc,←List.replicate_add,
      show t+(h-t)=h by omega]
  have hn:=initial_S_source_excluded t v ((List.replicate h false).drop t++x) B
    (by rw [←heq]; exact hm) (by rw [←heq]; exact hS) (by rw [←heq]; exact ha) hc
  apply hn
  simpa only [List.append_assoc] using hk

/-- The second target-derived case needs only a five-clock local budget:
the impossible initial S source saves one whole family, for all lengths. -/
theorem ten_head_local_le_five (h M m L s U v K : Nat) (B : Int)
    (hv : 1≤v)
    (hm : mass (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true)=0)
    (hS : cntF (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true)=10)
    (ha : areaW (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true)= -B)
    (hc : (v=1 ∧ B=46) ∨ (v=2 ∧ B=56)) :
    rayCount (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false) K≤5 := by
  let x:=List.replicate M true++List.replicate m false++List.replicate L true++
    List.replicate s false++List.replicate U true
  have he:=initial_S_ray_erasure h v K x B
    (by simpa only [x,List.append_assoc] using hm)
    (by simpa only [x,List.append_assoc] using hS)
    (by simpa only [x,List.append_assoc] using ha) hc
  have hp:=run_prefix_ray_budget [(true,M),(false,m),(true,L),(false,s)]
    (List.replicate U true++List.replicate v false) K
  have hb:=rayCount_A_S_le_one U v K hv
  simp only [runWord,List.length_cons,List.length_nil,List.append_nil,Nat.reduceAdd,
    List.append_assoc] at hp
  simp only [x,List.append_assoc] at he
  simp only [List.append_assoc] at ⊢
  omega

end Recaman.TenHeadSourcePruning
