import Recaman.TenHeadFirstASource

namespace Recaman.OneGapInteriorA

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.SourceFamilyFreeCount

/-- A source in the A run preceding one older separator, followed by a
single final S, can supply only clock2. All lengths are unbounded and
the intermediate A length U may be zero. -/
theorem interior_A_one_gap_clock (e s U i : Nat) (he : 1≤e) (hs : 1≤s)
    (hm : mass (List.replicate e true++List.replicate s false++List.replicate U true++[false])+
      (i : Int)=1)
    (hk : runKey (List.replicate e true++List.replicate s false++List.replicate U true++[false])= -2) :
    i=2 := by
  have hkey:=runKey_five_runs 0 e s U 1
  simp only [List.replicate_zero,List.nil_append,List.replicate_one] at hkey
  rw [hkey] at hk
  simp only [mass_append,mass_replicate_A,mass_rep_false,mass_cons,mass_nil,
    Recaman.ShortPeriodicSupply.sign,Int.natCast_one] at hm
  let p : Int:=(s : Int)+1
  let r : Int:=p-2*(e : Int)
  have hp : 2≤p := by dsimp [p]; omega
  have hpr : p*r=2*(U : Int)+1 := by dsimp [p,r] at *; grind only
  have hrel : p≥r+2 := by dsimp [r]; omega
  have hr : 1≤r := by
    by_cases hh : 1≤r
    · exact hh
    · have hz:=Int.mul_nonpos_of_nonneg_of_nonpos (show 0≤p by omega) (show r≤0 by omega)
      omega
  have hi : 2*(i : Int)=4-(p-1)*(r-1) := by dsimp [p,r] at *; grind only
  have hr2 : r≤2 := by
    by_cases hh : r≤2
    · exact hh
    · have hprod:=Int.mul_nonneg (show 0≤p-5 by omega) (show 0≤r-1 by omega)
      grind only
  have hr1 : r=1 := by
    by_cases hh : r=1
    · exact hh
    · have hrval : r=2 := by omega
      rw [hrval] at hpr
      omega
  rw [hr1] at hi
  omega

/-- The excluded e=0 boundary really would allow clock0; it is not an
A-run source and must not be inserted into the classification. -/
theorem empty_A_boundary_control :
    mass (List.replicate 0 true++List.replicate 2 false++List.replicate 4 true++[false])=1 ∧
    runKey (List.replicate 0 true++List.replicate 2 false++List.replicate 4 true++[false])= -2 := by decide

end Recaman.OneGapInteriorA
