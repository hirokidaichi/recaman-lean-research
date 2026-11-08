import Recaman.MixedASQuarterBudget

namespace Recaman.PrimitiveLayerClockCost

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.ShortCounterFactorBounds

/-- The cost is in A signs, not actual free additions. Both clocks belong
to primitive suffixes of the same unchanged future word. -/
theorem layer_clock_A_cost (u : List Bool) (a b i j : Nat) (hb : 1≤b)
    (hkey : runKey u= -2)
    (hnewkey : runKey (List.replicate a true++(List.replicate b false++u))= -2)
    (hm : mass u+(i : Int)=1)
    (hnewmass : mass (List.replicate a true++(List.replicate b false++u))+(j : Int)=1) :
    i+2≤j ∧ j-i+2≤a := by
  have hodd:=Recaman.MixedASQuarterBudget.source_subtraction_odd u hkey
  have hnodd:=Recaman.MixedASQuarterBudget.source_subtraction_odd _ hnewkey
  simp only [cntF_append,cntF_replicate_S,Recaman.UnitTargetSASProfile.cntF_A,
    Nat.zero_add,Int.natCast_add] at hnodd
  have hF : 1≤cntF u := by omega
  have hbeven : (b : Int)%2=0 := by omega
  simp only [mass_append,mass_replicate_A,mass_rep_false] at hnewmass
  have hclock : (a : Int)+(j : Int)=(b : Int)+(i : Int) := by omega
  rw [runKey_prepend_A,runKey_prepend_S,hkey] at hnewkey
  simp only [cntF_append,cntF_replicate_S,Int.natCast_add] at hnewkey
  have hab : a<b := by
    by_cases hh : a<b
    · exact hh
    · have hp:=Int.mul_nonneg (show 0≤(a : Int)-(b : Int) by omega)
        (show 0≤(b : Int)+(cntF u : Int) by omega)
      have hbb:=square_lower (b : Int) 1 (by decide) (by omega)
      grind only
  let d:=(j : Int)-(i : Int)
  have hd : 1≤d := by dsimp [d]; omega
  have he : (a : Int)^2=d^2+2*d*(cntF u : Int) := by dsimp [d]; grind only
  have had : d<(a : Int) := by
    by_cases hh : d<(a : Int)
    · exact hh
    · have hp:=Int.mul_nonneg (show 0≤d-(a : Int) by omega) (show 0≤d+(a : Int) by omega)
      have hFpos:=Int.mul_pos (show 0<d by omega) (show 0<(cntF u : Int) by omega)
      grind only
  have hsamepar : ((a : Int)-d)%2=0 := by dsimp [d]; omega
  have hcost : d+2≤(a : Int) := by omega
  have hd2 : 2≤d := by
    by_cases hh : 2≤d
    · exact hh
    · have hd1 : d=1 := by omega
      have haodd : (a : Int)%2=1 := by omega
      obtain ⟨Q,hQ⟩:=Recaman.OldThreeKeyParity.odd_square_eight (a : Int) haodd
      rw [hd1] at he
      omega
  dsimp [d] at hd2 hcost
  constructor <;> omega

/-- The first E598 layer attains the new additive A cost. -/
theorem cost_sharp :
    let u:=[false,true,true,false,false]
    runKey u= -2 ∧ runKey (List.replicate 4 true++(List.replicate 6 false++u))= -2 ∧
      mass u+2=1 ∧ mass (List.replicate 4 true++(List.replicate 6 false++u))+4=1 ∧
      4-2+2=4 := by decide

end Recaman.PrimitiveLayerClockCost
