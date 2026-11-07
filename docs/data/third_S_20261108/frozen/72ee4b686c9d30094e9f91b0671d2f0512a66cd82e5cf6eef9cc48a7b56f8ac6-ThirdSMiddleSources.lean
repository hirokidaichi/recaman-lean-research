import Recaman.ThirdSTargetSmallBand

namespace Recaman.ThirdSMiddleSources

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.AdjacentRunSupply Recaman.FourthSourceFamilies Recaman.ShortCounterFactorBounds

private theorem square_not_in_gap (y a : Int) (hy : 0≤y) (ha : 0≤a)
    (hlo : a^2<y^2) (hhi : y^2<(a+1)^2) : False := by
  by_cases h : y≤a
  · have hs:=square_lower a y hy h
    omega
  · have hs:=square_lower y (a+1) (by omega) (by omega)
    omega

theorem middle_sources_absent (m s v i : Nat) (hlen : 11≤s+v) (hv : v=3 ∨ v=4) :
    ¬sourceAt false m (List.replicate 1 true++List.replicate s false++
      List.replicate 12 true++List.replicate v false) i ∧
    ¬sourceAt true 1 (List.replicate s false++
      (List.replicate 12 true++List.replicate v false)) i ∧
    ¬sourceAt false s (List.replicate 12 true++List.replicate v false) i := by
  have hv4 : v≤4 := by omega
  refine ⟨?_,?_,?_⟩
  · rintro ⟨b,hb,_,_,hk⟩
    have he:=Recaman.SourceFamilyFreeCount.runKey_five_runs b 1 s 12 v
    have hk' : runKey (List.replicate b false++List.replicate 1 true++List.replicate s false++
      List.replicate 12 true++List.replicate v false)= -2 := by
      simpa only [List.append_assoc] using hk
    rw [he] at hk'
    let z:=(s : Int)+(v : Int)
    have h1:=square_lower ((b : Int)+z) (z+1) (by dsimp [z]; omega) (by omega)
    have h2:=square_lower z 11 (by decide) (by dsimp [z]; omega)
    dsimp [z] at h1 h2
    grind only
  · rintro ⟨a,ha,ha1,_,hk⟩
    have haeq : a=1 := by omega
    subst a
    rw [runKey_prepend_A,←List.append_assoc,runKey_S_A_S] at hk
    simp only [cntF_append,cntF_replicate_S,Recaman.UnitTargetSASProfile.cntF_A] at hk
    have h1:=square_lower ((s : Int)+(v : Int)-1) 10 (by decide) (by omega)
    grind only
  · rintro ⟨k,hk,_,_,hkey⟩
    rw [←List.append_assoc,runKey_S_A_S] at hkey
    rcases hv with rfl|rfl
    · exact square_not_in_gap ((k : Int)+3) 8 (by omega) (by decide)
        (by grind only) (by grind only)
    · exact square_not_in_gap ((k : Int)+4) 9 (by omega) (by decide)
        (by grind only) (by grind only)

/-- The entire middle S/A/S source group is absent in the two remaining
same-target scalar shapes. Only the unchanged last pair remains there. -/
theorem middle_ray_one (m s v K : Nat) (hlen : 11≤s+v) (hv : v=3 ∨ v=4) :
    rayCount (List.replicate m false++(List.replicate 1 true++(List.replicate s false++
      (List.replicate 12 true++List.replicate v false)))) K≤1 := by
  let x:=List.replicate 12 true++List.replicate v false
  have hx : rayCount x K≤1 := rayCount_A_S_le_one 12 v K (by omega)
  have hle : rayCount (List.replicate m false++(List.replicate 1 true++(List.replicate s false++x))) K≤
      rayCount x K := by
    unfold rayCount
    apply cN_mono
    intro i hi hiK he
    obtain ⟨hS,hA,hS3⟩:=middle_sources_absent m s v i hlen hv
    rcases (local_const_split false m _ i).mp he with hs|hl
    · exact False.elim (hS (by simpa only [List.append_assoc,x] using hs))
    · rcases (local_const_split true 1 _ i).mp hl with ha|hs
      · exact False.elim (hA ha)
      · rcases (local_const_split false s x i).mp hs with hs|hx
        · exact False.elim (hS3 hs)
        · exact hx
  change rayCount (List.replicate m false++(List.replicate 1 true++(List.replicate s false++x))) K≤1
  omega

theorem actual_last_three (f : Nat → Bool) (n B T h m s v : Nat) (w : List Bool)
    (hw : BlockWord w) (hpre : seg f 0 n=w)
    (hword : seg f n B=List.replicate h false++List.replicate 1 true++List.replicate m false++
      List.replicate 1 true++List.replicate s false++List.replicate 12 true++List.replicate v false)
    (hm : 1≤m) (hlen : 11≤s+v) (hv : v=3 ∨ v=4)
    (hA : ∀ i, i<T → f (n+B+i)=true) : cN (EndN f 0) (n+B) T≤3 := by
  let x:=List.replicate m false++(List.replicate 1 true++(List.replicate s false++
      (List.replicate 12 true++List.replicate v false)))
  let y:=List.replicate h false++(List.replicate 1 true++x)
  have hy : 3≤cntF y := by
    simp only [y,x,cntF_append,cntF_replicate_S,Recaman.UnitTargetSASProfile.cntF_A]
    omega
  have hword' : seg f n B=y := by simpa only [y,x,List.append_assoc] using hword
  have ho:=(Recaman.MixedFinalRayOldBudget.actual_mixed_ray_old_budget f n B T w y hw hpre hword' hy hA).1
  have hp:=Recaman.MixedShortAPairBudget.pair_prefix_saving x h 1 T (by decide)
  have hx : rayCount x T≤1 := middle_ray_one m s v T hlen hv
  change rayCount y T≤1+rayCount x T at hp
  omega

end Recaman.ThirdSMiddleSources
