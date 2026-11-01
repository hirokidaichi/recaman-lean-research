import Recaman.SourceCrossSurplus

namespace Recaman.SourceMassStrictCut

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.ASourceReuse
open Recaman.RunSupplyBudget Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality
open Recaman.LineCapacityPeriodic

/-- Target mass at least two supplies a strict source-prefix A cut
without any AS-pair or positive-cross hypothesis. No free-count bound. -/
theorem source_mass_two_strict_A (u b v : List Bool) (hu : BlockWord u) (hC2 : 2≤mass u)
    (i T j : Nat) (hj : 2≤j) (hband : T≤i+j)
    (hm1 : mass (v++List.replicate i true)=1)
    (ha1 : areaW (v++List.replicate i true)=0)
    (hm2 : mass (u++b++v++List.replicate T true++List.replicate j false)=1)
    (ha2 : areaW (u++b++v++List.replicate T true++List.replicate j false)=0) :
    (j : Int)+1+((i : Int)+(j : Int)-(T : Int))+1≤ones b := by
  let C:=mass u
  let K:=(i : Int)+(j : Int)-(T : Int)
  let X:=ones b-K
  let R:=(j : Int)+1
  have he:=Recaman.SourceCrossSurplus.two_source_cross_identity u b v i T j hm1 ha1 hm2 ha2
  have hC : 2≤C := hC2
  have hku : -2≤runKey u := by have hh:=block_area_quadratic_lower hu; unfold runKey; omega
  have hK : 0≤K := by dsimp [K]; omega
  have hcv : 0≤(cntF v : Int) := by omega
  have hprod:=Int.mul_nonneg hK hcv
  have hm : 0≤C+X := by
    have hcb:=cntF_int b
    have hmb:=mass_eq b
    simp only [mass_append,mass_replicate_A,mass_rep_false] at hm1 hm2
    dsimp [C,X,K]
    omega
  have hcross : 0≤runKey b+2*(cntF b : Int)^2 := by
    have hk:=runKey_count_lower b
    omega
  have hineq : C^2+R^2-2≤X^2 := by dsimp [C,R,X,K]; grind
  have hR : 3≤R := by dsimp [R]; omega
  have hX : 0≤X := by
    by_cases hh : 0≤X
    · exact hh
    · have hp:=Int.mul_nonneg hm (show 0≤C-X by omega)
      have hs : X^2≤C^2 := by grind
      grind
  have hCC : 4≤C^2 := by have hp:=Int.mul_nonneg (show 0≤C-2 by omega) (show 0≤C+2 by omega); grind
  have hgt : R<X := by
    by_cases hh : R<X
    · exact hh
    · have hp:=Int.mul_nonneg (show 0≤R-X by omega) (show 0≤R+X by omega)
      grind
  dsimp [R,X,K] at hgt
  omega


end Recaman.SourceMassStrictCut
