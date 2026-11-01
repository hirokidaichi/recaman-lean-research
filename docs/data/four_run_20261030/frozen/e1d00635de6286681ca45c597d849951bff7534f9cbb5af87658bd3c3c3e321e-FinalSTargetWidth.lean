import Recaman.OldTargetMassCircle
import Recaman.FinalSSourceResidual

namespace Recaman.FinalSTargetWidth

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.RunSupplyBudget Recaman.FourRunSupplySeventeen Recaman.OldTargetMassCircle
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

private theorem small_circle_bounds (C R : Int) (hC : 0≤C) (hR : 5≤R)
    (h : C^2+R^2≤117) : C≤9 ∧ C+R≤15 := by
  have hrp:=Int.mul_nonneg (show 0≤R-5 by omega) (show 0≤R+5 by omega)
  have hr2 : 25≤R^2 := by grind only
  have hc : C≤9 := by
    by_cases hh : C≤9
    · exact hh
    · have hp:=Int.mul_nonneg (show 0≤C-10 by omega) (show 0≤C+10 by omega)
      grind only
  have hs : C+R≤15 := by
    by_cases hh : C+R≤15
    · exact hh
    · have hp:=Int.mul_nonneg (show 0≤C+R-16 by omega) (show 0≤C+R+16 by omega)
      have hd:=Int.sq_nonneg (C-R)
      grind only
  exact ⟨hc,hs⟩

private theorem large_circle_bounds (C R : Int) (hC : 0≤C) (hR : 5≤R)
    (h : C^2+(R+1)^2≤226) : C≤13 ∧ C+R≤20 := by
  have hrp:=Int.mul_nonneg (show 0≤R+1-6 by omega) (show 0≤R+1+6 by omega)
  have hr2 : 36≤(R+1)^2 := by grind only
  have hc : C≤13 := by
    by_cases hh : C≤13
    · exact hh
    · have hp:=Int.mul_nonneg (show 0≤C-14 by omega) (show 0≤C+14 by omega)
      grind only
  have hs : C+R≤20 := by
    by_cases hh : C+R≤20
    · exact hh
    · have hp:=Int.mul_nonneg (show 0≤C+R+1-22 by omega) (show 0≤C+R+1+22 by omega)
      have hd:=Int.sq_nonneg (C-(R+1))
      grind only
  exact ⟨hc,hs⟩

end Recaman.FinalSTargetWidth
