import Recaman.PrimitiveLayerClockCost

namespace Recaman.SlowPrimitiveClockPair

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- Both primitive suffix clocks differ by two, while their first clock
is quadratic in l. This is a literal-source family, not a C1 counterexample. -/
theorem clock_pair_family (l z : Nat) (hl : 1≤l) (hz : z+2=4*l*l) :
    let u:=List.replicate 1 false++List.replicate (2*l*l) true++List.replicate z false
    let w:=List.replicate (4*l) true++(List.replicate (4*l+2) false++u)
    runKey u= -2 ∧ mass u+((2*l*l : Nat) : Int)=1 ∧
      runKey w= -2 ∧ mass w+((2*l*l+2 : Nat) : Int)=1 := by
  dsimp only
  have hz':=congrArg (fun n : Nat=>(n : Int)) hz
  simp only [Int.natCast_add,Int.natCast_mul] at hz'
  have hzi : (z : Int)=4*(l : Int)*(l : Int)-2 := by omega
  have hkey : runKey (List.replicate 1 false++List.replicate (2*l*l) true++List.replicate z false)= -2 := by
    rw [runKey_S_A_S]
    simp only [Int.natCast_mul]
    grind only
  have hm : mass (List.replicate 1 false++List.replicate (2*l*l) true++List.replicate z false)+
      ((2*l*l : Nat) : Int)=1 := by
    simp only [mass_append,mass_rep_false,mass_replicate_A,Int.natCast_mul]
    grind only
  have hn : runKey (List.replicate (4*l) true++(List.replicate (4*l+2) false++
      (List.replicate 1 false++List.replicate (2*l*l) true++List.replicate z false)))= -2 := by
    rw [runKey_prepend_A,runKey_prepend_S,hkey]
    simp only [cntF_append,cntF_replicate_S,Recaman.UnitTargetSASProfile.cntF_A,
      Nat.zero_add,Nat.add_zero,Int.natCast_add,Int.natCast_mul]
    grind only
  refine ⟨hkey,hm,hn,?_⟩
  simp only [mass_append,mass_rep_false,mass_replicate_A,Int.natCast_add,Int.natCast_mul]
  grind only

end Recaman.SlowPrimitiveClockPair
