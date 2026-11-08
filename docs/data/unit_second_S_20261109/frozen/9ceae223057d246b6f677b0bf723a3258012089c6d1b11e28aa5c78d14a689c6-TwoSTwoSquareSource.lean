import Recaman.TargetSSourceSquareOrder

namespace Recaman.TwoSTwoSquareSource

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.FourthSourceFamilies Recaman.ShortCounterFactorBounds

/-- Primitive odd S-count leaves no third-S source in the actual D<=6 band,
without the U floor or an R/D/U/v classification. -/
theorem last_S_source_excluded (L s U v R D i : Nat) (hL : 1≤L) (hv : 1≤v)
    (hR : 5≤R) (hD6 : D≤6) (hDL : D+L=2+s+v)
    (htarget : runKey (List.replicate 2 false++(List.replicate L true++
      (List.replicate s false++List.replicate U true++List.replicate v false)))= -2*(R : Int)^2) :
    ¬sourceAt false s (List.replicate U true++List.replicate v false) i := by
  rintro ⟨k,hk,hks,hm,hkey⟩
  have hodd:=Recaman.MixedASQuarterBudget.source_subtraction_odd _ hkey
  simp only [cntF_append,cntF_replicate_S,Recaman.UnitTargetSASProfile.cntF_A,Nat.add_zero,Nat.zero_add] at hodd
  rw [←List.append_assoc,runKey_S_A_S] at hkey
  rw [runKey_prepend_S,runKey_prepend_A] at htarget
  simp only [cntF_append,cntF_replicate_S,Recaman.UnitTargetSASProfile.cntF_A,Nat.add_zero,Nat.zero_add] at htarget
  rw [runKey_S_A_S] at htarget
  have hDi : (D : Int)+(L : Int)=2+(s : Int)+(v : Int) := by omega
  have he : (D : Int)^2=(R : Int)^2+((L : Int)-2)^2-5+((k : Int)+(v : Int))^2 := by grind only
  have hLsq:=Int.sq_nonneg ((L : Int)-2)
  have hd:=square_lower 6 (D : Int) (by omega) (by omega)
  have hr:=square_lower (R : Int) 5 (by decide) (by omega)
  have hJ3 : k+v=3 := by
    have hJ4 : k+v≤4 := by
      by_cases hh : k+v≤4
      · exact hh
      · have hj:=square_lower ((k : Int)+(v : Int)) 5 (by decide) (by omega)
        omega
    omega
  have hJi : (k : Int)+(v : Int)=3 := by omega
  rw [hJi] at he
  have hRD : R<D := by
    by_cases hh : R<D
    · exact hh
    · have hp:=Int.mul_nonneg (show 0≤(R : Int)-(D : Int) by omega)
        (show 0≤(R : Int)+(D : Int) by omega)
      grind only
  have hD : D=6 := by omega
  have hR5 : R=5 := by omega
  rw [hD,hR5] at he
  have hseven : ((L : Int)-2)^2=7 := by omega
  by_cases hh : 2≤L
  · have hn:=Recaman.ShortGapSourceClocks.nonnegative_square_gap ((L : Int)-2) 2 7
      (by omega) (by decide) (by decide) (by decide)
    exact hn (by grind only)
  · have hL1 : L=1 := by omega
    rw [hL1] at hseven
    omega

theorem D_seven_source_boundary :
    let x:=List.replicate 9 false++List.replicate 4 true++List.replicate 1 false
    runKey (List.replicate 2 false++(List.replicate 5 true++x))= -72 ∧
      sourceAt false 9 (List.replicate 4 true++List.replicate 1 false) 0 := by
  dsimp only
  refine ⟨by decide,2,by decide,by decide,by decide,by decide⟩

end Recaman.TwoSTwoSquareSource
