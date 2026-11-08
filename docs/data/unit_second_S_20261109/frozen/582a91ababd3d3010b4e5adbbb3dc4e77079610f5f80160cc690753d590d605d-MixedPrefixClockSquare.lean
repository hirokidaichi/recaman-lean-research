import Recaman.PrimitiveClockRadius

namespace Recaman.MixedPrefixClockSquare

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.ShortCounterFactorBounds

/-- A general mixed prefix loses the AS layer's gap-two property,
but keeps a sharp quadratic cost in its actual number of A signs. -/
theorem mixed_prefix_clock_square (p u : List Bool) (i j : Nat) (hij : i<j)
    (hkey : runKey u= -2) (hnewkey : runKey (p++u)= -2)
    (hm : mass u+(i : Int)=1) (hn : mass (p++u)+(j : Int)=1) :
    (j-i : Nat)+2≤ones p ∧ 4*(i : Int)+1≤(ones p)^2 := by
  have hodd:=Recaman.MixedASQuarterBudget.source_subtraction_odd u hkey
  have hnodd:=Recaman.MixedASQuarterBudget.source_subtraction_odd _ hnewkey
  simp only [cntF_append,Int.natCast_add] at hnodd
  have hpeven : (cntF p : Int)%2=0 := by omega
  have hFu : 1≤cntF u := by omega
  have hc:=cntF_int p
  have hmp:=mass_eq p
  simp only [mass_append] at hn
  let d:=(j : Int)-(i : Int)
  have hd : 1≤d := by dsimp [d]; omega
  have hpd : mass p= -d := by dsimp [d]; omega
  rw [runKey_append,hkey,hpd] at hnewkey
  have hcross:=Recaman.PrimitiveClockRadius.cross_upper p
  have hpA:=(ones_bounds p).1
  have he : d^2+2*d*(cntF u : Int)≤(ones p)^2 := by grind only
  have hA : d<ones p := by
    by_cases hh : d<ones p
    · exact hh
    · have hp:=Int.mul_nonneg (show 0≤d-ones p by omega) (show 0≤d+ones p by omega)
      have hFpos:=Int.mul_pos (show 0<d by omega) (show 0<(cntF u : Int) by omega)
      grind only
  have hpar : (ones p-d)%2=0 := by omega
  have hcost : d+2≤ones p := by omega
  refine ⟨by dsimp [d] at hcost; omega,?_⟩
  have hFc : cntF u=1 ∨ 3≤cntF u := by omega
  rcases hFc with hF1|hF3
  · have hcU:=cntF_int u
    have hmU:=mass_eq u
    have hA0:=(ones_bounds u).1
    have hi2 : i≤2 := by omega
    have hs:=square_lower (ones p) 3 (by decide) (by omega)
    omega
  · have hiF:=Recaman.PrimitiveClockRadius.primitive_clock_half_S u i hF3 hkey hm
    by_cases hd1 : d=1
    · have hAodd : ones p%2=1 := by omega
      obtain ⟨Q,hQ⟩:=Recaman.OldThreeKeyParity.odd_square_eight (ones p) hAodd
      rw [hd1] at he
      omega
    · have hp:=Int.mul_nonneg (show 0≤d-2 by omega)
        (show 0≤d+2+2*(cntF u : Int) by omega)
      have hlo : 4+4*(cntF u : Int)≤(ones p)^2 := by grind only
      omega

/-- Unit advance and equality show why the AS coefficient eight does
not extend to an arbitrary mixed prefix. -/
theorem unit_advance_sharp :
    let p:=[true,true,false,true,false,false,false]
    let u:=[false,true,true,false,false]
    runKey u= -2 ∧ runKey (p++u)= -2 ∧ mass u+2=1 ∧ mass (p++u)+3=1 ∧
      ones p=3 ∧ 4*(2 : Int)+1=(ones p)^2 := by decide

end Recaman.MixedPrefixClockSquare
