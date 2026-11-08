import Recaman.MixedPrefixClockSquare

namespace Recaman.MixedPrefixDistinctClock

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.ShortCounterFactorBounds

/-- Source-start order need not equal clock order. The inner-clock
square bound holds in both directions, for every mixed prefix. -/
theorem distinct_clock_square (p u : List Bool) (i j : Nat) (hne : i≠j)
    (hkey : runKey u= -2) (hnewkey : runKey (p++u)= -2)
    (hm : mass u+(i : Int)=1) (hn : mass (p++u)+(j : Int)=1) :
    4*(i : Int)+1≤(ones p)^2 := by
  by_cases hij : i<j
  · exact (Recaman.MixedPrefixClockSquare.mixed_prefix_clock_square p u i j hij hkey hnewkey hm hn).2
  · have hji : j<i := by omega
    have hodd:=Recaman.MixedASQuarterBudget.source_subtraction_odd u hkey
    have hnodd:=Recaman.MixedASQuarterBudget.source_subtraction_odd _ hnewkey
    simp only [cntF_append,Int.natCast_add] at hnodd
    have hpeven : (cntF p : Int)%2=0 := by omega
    have hFu : 1≤cntF u := by omega
    have hc:=cntF_int p
    have hmp:=mass_eq p
    simp only [mass_append] at hn
    let C:=(i : Int)-(j : Int)
    have hC : 1≤C := by dsimp [C]; omega
    have hpC : mass p=C := by dsimp [C]; omega
    rw [runKey_append,hkey,hpC] at hnewkey
    have hkP : runKey p= -4*C*(cntF u : Int) := by dsimp only [C] at hnewkey ⊢; grind only
    have hl:=runKey_count_lower p
    rw [hkP] at hl
    have hB1 : 1≤cntF p := by
      by_cases hh : 1≤cntF p
      · exact hh
      · have hz : cntF p=0 := by omega
        rw [hz] at hl
        have hp:=Int.mul_pos (show 0<C by omega) (show 0<(cntF u : Int) by omega)
        grind only
    have hB2 : 2≤cntF p := by omega
    have hAeq : ones p=(cntF p : Int)+C := by omega
    have hA3 : 3≤ones p := by omega
    have hFc : cntF u=1 ∨ 3≤cntF u := by omega
    rcases hFc with hF1|hF3
    · have hcU:=cntF_int u
      have hmU:=mass_eq u
      have hAu:=(ones_bounds u).1
      have hi2 : i≤2 := by omega
      have hs:=square_lower (ones p) 3 (by decide) hA3
      omega
    · have hiF:=Recaman.PrimitiveClockRadius.primitive_clock_half_S u i hF3 hkey hm
      have hCF:=Int.mul_nonneg (show 0≤C-1 by omega) (show 0≤(cntF u : Int) by omega)
      have hBC:=Int.mul_nonneg (show 0≤(cntF p : Int) by omega) (show 0≤C by omega)
      have hC2:=square_lower C 1 (by decide) hC
      have hs : 2*(cntF u : Int)+3≤(ones p)^2 := by
        have hp:=Int.mul_nonneg (show 0≤(cntF p : Int)-1 by omega) (show 0≤C by omega)
        grind only
      omega

theorem reversed_clock_control :
    let p:=[false,false,true,true,true,true]
    let u:=[false]
    runKey u= -2 ∧ runKey (p++u)= -2 ∧ mass u+2=1 ∧ mass (p++u)+0=1 ∧ ones p=4 := by decide

end Recaman.MixedPrefixDistinctClock
