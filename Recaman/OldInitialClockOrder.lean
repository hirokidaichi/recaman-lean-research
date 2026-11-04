import Recaman.OldInitialKeyGap

namespace Recaman.OldInitialClockOrder

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.BlockOldRay
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- Over any common mixed suffix, an initial-S supplier must supply
strictly before an old BlockWord supplier of mass>=2. No zero head,
target, separator bound or run count is required. -/
theorem initial_clock_before_old (u x : List Bool) (d i k : Nat) (hu : BlockWord u)
    (hD : 2≤mass u)
    (hmold : mass (u++(List.replicate d false++x))+(i : Int)=1)
    (hkold : runKey (u++(List.replicate d false++x))= -2)
    (hmlocal : mass x+(k : Int)=1) (hklocal : runKey x= -2) : k<i := by
  have hN : 1≤cntF x := by
    have hh:=runKey_count_lower x
    by_cases hz : cntF x=0
    · rw [hz,hklocal] at hh
      simp only [Int.natCast_zero] at hh
      omega
    · omega
  have he:=Recaman.OldInitialKeyGap.shared_initial_key u x d hkold hklocal
  have hlo : -2≤runKey u := by have hh:=block_area_quadratic_lower hu; unfold runKey; omega
  have hd : mass u<(d : Int) := by
    by_cases ht : mass u<(d : Int)
    · exact ht
    have hp:=Int.mul_nonpos_of_nonpos_of_nonneg (show (d : Int)-mass u≤0 by omega)
      (show 0≤(d : Int)+(cntF x : Int) by omega)
    have hd1 : d≤1 := by
      by_cases hh : d≤1
      · exact hh
      have hs:=Int.mul_nonneg (show 0≤(d : Int)-2 by omega) (show 0≤(d : Int)+2 by omega)
      grind only
    rcases (show d=0 ∨ d=1 by omega) with h0|h1
    · rw [h0] at he
      have hp:=Int.mul_pos (show 0<mass u by omega) (show 0<(cntF x : Int) by omega)
      grind only
    · rw [h1] at he
      have hp:=Int.mul_pos (show 0<mass u-1 by omega) (show 0<1+(cntF x : Int) by omega)
      grind only
  simp only [mass_append,mass_rep_false] at hmold
  omega

end Recaman.OldInitialClockOrder
