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
  have hzi : (z : Int)=4*(l : Int)*(l : Int)-2 := by
    rw [show ((4 : Nat) : Int)=4 by decide] at hz'
    omega
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

/-- Both primitive witnesses live in the same word, at clocks i and i+2. -/
theorem same_word_two_clocks (l : Nat) (hl : 1≤l) :
    ∃ w : List Bool,
      Recaman.ThreeNonsuppliedData.localSupply (w++List.replicate (2*l*l) true)=true ∧
      Recaman.ThreeNonsuppliedData.localSupply (w++List.replicate (2*l*l+2) true)=true := by
  have hll : 1≤l*l := Nat.mul_le_mul hl hl
  have hassoc : 4*l*l=4*(l*l) := Nat.mul_assoc 4 l l
  let z:=4*l*l-2
  have hz : z+2=4*l*l := by dsimp [z]; omega
  let u:=List.replicate 1 false++List.replicate (2*l*l) true++List.replicate z false
  let b:=List.replicate (4*l) true++List.replicate (4*l+2) false
  let w:=b++u
  obtain ⟨hkey,hm,hnew,hmnew⟩:=clock_pair_family l z hl hz
  change runKey u= -2 at hkey
  change mass u+((2*l*l : Nat) : Int)=1 at hm
  have hnkey : runKey w= -2 := by simpa only [w,b,u,List.append_assoc] using hnew
  have hnmass : mass w+((2*l*l+2 : Nat) : Int)=1 := by
    simpa only [w,b,u,List.append_assoc] using hmnew
  have hu : 0<u.length := by simp only [u,List.length_append,List.length_replicate]; omega
  have hw : 0<w.length := by simp only [w,List.length_append]; omega
  have hd : w.drop b.length=u := by
    rw [w,List.drop_append,List.drop_length,Nat.sub_self,List.drop_zero,List.nil_append]
  have hfirst:= (localSupply_A_S_iff w (2*l*l) 0).mpr
    ⟨b.length,by simp only [w,List.length_append]; omega,
      by rw [hd]; exact hm,by rw [hd,hkey]; decide⟩
  have hsecond:= (localSupply_A_S_iff w (2*l*l+2) 0).mpr
    ⟨0,hw,by simpa only [List.drop_zero] using hnmass,by simp only [List.drop_zero,hnkey]; decide⟩
  refine ⟨w,?_,?_⟩
  · simpa only [List.replicate_zero,List.append_nil] using hfirst
  · simpa only [List.replicate_zero,List.append_nil] using hsecond

/-- Arbitrarily close to unit relative growth: no fixed multiplicative
clock separation follows from primitive suffixes alone. -/
theorem arbitrarily_slow_relative_growth (N : Nat) :
    ∃ (w : List Bool) (i j : Nat),
      0<i ∧ j=i+2 ∧ (N : Int)*(j : Int)<((N : Int)+1)*(i : Int) ∧
      Recaman.ThreeNonsuppliedData.localSupply (w++List.replicate i true)=true ∧
      Recaman.ThreeNonsuppliedData.localSupply (w++List.replicate j true)=true := by
  let l:=N+1
  obtain ⟨w,hi,hj⟩:=same_word_two_clocks l (by dsimp [l]; omega)
  refine ⟨w,2*l*l,2*l*l+2,?_,rfl,?_,hi,hj⟩
  · have hll : 1≤l*l := Nat.mul_le_mul (by dsimp [l]; omega) (by dsimp [l]; omega)
    have he : 2*l*l=2*(l*l) := Nat.mul_assoc 2 l l
    omega
  · have hp:=Int.sq_nonneg (N : Int)
    have hl : (l : Int)=(N : Int)+1 := by dsimp [l]; omega
    simp only [Int.natCast_add,Int.natCast_mul]
    rw [show ((2 : Nat) : Int)=2 by decide]
    grind only

end Recaman.SlowPrimitiveClockPair
