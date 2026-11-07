import Recaman.ShortSeparatedSSupply
import Recaman.UnitTargetPrefixParity

namespace Recaman.MixedSeparatedSources

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.AdjacentRunSupply Recaman.FourthSourceFamilies Recaman.ThirdSeparatorClock
open Recaman.ShortCounterFactorBounds

/-- The earlier S depth cut holds for any common mixed future word. -/
theorem earlier_S_depth_mixed (x : List Bool) (m L s i j : Nat)
    (he : sourceAt false m (List.replicate L true++(List.replicate s false++x)) i)
    (hl : sourceAt false s x j) :
    sourceAt false (min m (L-1)) (List.replicate L true++(List.replicate s false++x)) i := by
  obtain ⟨b,hb,hbm,hm,hk⟩:=he
  have hk_original:=hk
  obtain ⟨k,hk1,hks,_,hlk⟩:=hl
  rw [runKey_prepend_S,runKey_prepend_A,runKey_prepend_S] at hk
  rw [runKey_prepend_S] at hlk
  simp only [cntF_append,cntF_replicate_S,Recaman.UnitTargetSASProfile.cntF_A,
    Int.natCast_add,Int.natCast_zero,Int.zero_add] at hk
  let z:=(s : Int)+(cntF x : Int)
  let y:=(k : Int)+(cntF x : Int)
  have hz : 1≤z := by dsimp [z]; omega
  have hy : 1≤y := by dsimp [y]; omega
  have hsquare:=square_lower z y (by omega) (by dsimp [z,y]; omega)
  have heq : ((b : Int)+z)^2=y^2+2*(L : Int)*z := by dsimp [z,y]; grind only
  have hbl : b<L := by
    by_cases h : b<L
    · exact h
    · have hp:=Int.mul_nonneg (show 0≤(b : Int)-(L : Int) by omega) (show 0≤z by omega)
      have hb2:=square_lower (b : Int) 1 (by decide) (by omega)
      grind only
  exact ⟨b,hb,by omega,hm,hk_original⟩

/-- A short intervening A makes the two S source clocks agree in an
arbitrary mixed future that still contains a subtraction. -/
theorem short_A_same_clock_mixed (x : List Bool) (m L s i j : Nat)
    (hF : 1≤cntF x) (hL : L≤4)
    (he : sourceAt false m (List.replicate L true++(List.replicate s false++x)) i)
    (hl : sourceAt false s x j) : i=j := by
  obtain ⟨b,hb,hbm,hm,hk⟩:=earlier_S_depth_mixed x m L s i j he hl
  obtain ⟨k,hk1,hks,hml,hlk⟩:=hl
  obtain ⟨Q,hQ⟩:=Recaman.UnitTargetPrefixParity.cross_four (List.replicate k false++x)
  rw [hlk] at hQ
  simp only [cntF_append,cntF_replicate_S,Int.natCast_add] at hQ
  rw [runKey_prepend_S,runKey_prepend_A,runKey_prepend_S] at hk
  rw [runKey_prepend_S] at hlk
  simp only [cntF_append,cntF_replicate_S,Recaman.UnitTargetSASProfile.cntF_A,
    Int.natCast_add,Int.natCast_zero,Int.zero_add] at hk
  simp only [mass_append,mass_replicate_A,mass_rep_false] at hm hml
  have hc:=Recaman.ShortSeparatedSSupply.short_clock_equation (L : Int) (b : Int)
    ((s : Int)+(cntF x : Int)) ((k : Int)+(cntF x : Int)) Q
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by grind only) (by omega)
  omega

/-- Having a subtraction in the common future is necessary. The empty
future admits clocks three and two across an A interval of length three. -/
theorem empty_future_distinct_clocks :
    sourceAt false 1 (List.replicate 3 true++(List.replicate 4 false++[])) 3 ∧
    sourceAt false 4 [] 2 := by
  constructor
  · exact ⟨1,by decide,by decide,by decide,by decide⟩
  · exact ⟨1,by decide,by decide,by decide,by decide⟩

end Recaman.MixedSeparatedSources
