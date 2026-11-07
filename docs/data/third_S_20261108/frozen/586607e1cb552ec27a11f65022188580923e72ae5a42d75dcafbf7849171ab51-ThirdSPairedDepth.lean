import Recaman.ThirdSPairedSupply
import Recaman.OldThreeKeyParity

namespace Recaman.ThirdSPairedDepth

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.FourthSourceFamilies Recaman.ShortCounterFactorBounds
open Recaman.LineCapacityPeriodic

private theorem small_leg_impossible (a x y Z : Int) (ha : 1≤a) (ha3 : a≤3)
    (he : x^2=a^2+y^2) (hy : y^2=1+2*Z) : False := by
  obtain ⟨d,hd⟩:=Recaman.OldThreeKeyParity.square_even_delta y
  have hyo : y%2=1 := by omega
  obtain ⟨b,hb⟩:=Recaman.OldThreeKeyParity.odd_square_eight y hyo
  obtain ⟨c,hc⟩:=Recaman.OldThreeKeyParity.square_even_delta x
  rcases (show a=1 ∨ a=2 ∨ a=3 by omega) with h1|h2|h3
  · rw [h1] at he
    have hxe : x%2=0 := by omega
    have hxx : x=2*(x/2) := by omega
    have hx2 : x^2=4*(x/2)^2 := by rw [hxx]; grind only
    omega
  · rw [h2] at he
    have hxo : x%2=1 := by omega
    obtain ⟨d,hd⟩:=Recaman.OldThreeKeyParity.odd_square_eight x hxo
    omega
  · rw [h3] at he
    have hxe : x%2=0 := by omega
    have hxx : x=2*(x/2) := by omega
    have hx2 : x^2=4*(x/2)^2 := by rw [hxx]; grind only
    omega

/-- Joint suppliers require a depth of at least four and a quadratic
separator budget. The two source clocks need not coincide. -/
theorem paired_depth_budget (L s U v i j : Nat)
    (ha : sourceAt true L (List.replicate s false++
      (List.replicate U true++List.replicate v false)) i)
    (hs : sourceAt false s (List.replicate U true++List.replicate v false) j) :
    ∃ a, 4≤a ∧ a≤L ∧ 2*((s : Int)+(v : Int))≤((a : Int)+1)^2 := by
  obtain ⟨a,ha1,haL,hma,hka⟩:=ha
  obtain ⟨k,hk1,_,_,hks⟩:=hs
  rw [runKey_prepend_A,←List.append_assoc,runKey_S_A_S] at hka
  rw [←List.append_assoc,runKey_S_A_S] at hks
  simp only [cntF_append,cntF_replicate_S,Recaman.UnitTargetSASProfile.cntF_A] at hka
  simp only [mass_append,mass_replicate_A,mass_rep_false] at hma
  let x:=(s : Int)+(v : Int)-(a : Int)
  let y:=(k : Int)+(v : Int)
  have he : x^2=(a : Int)^2+y^2 := by dsimp [x,y]; grind only
  have hy : y^2=1+2*(U : Int)*(v : Int) := by dsimp [y]; grind only
  have ha4 : 4≤a := by
    by_cases h : 4≤a
    · exact h
    · exact False.elim (small_leg_impossible (a : Int) x y ((U : Int)*(v : Int))
        (by omega) (by omega) he (by grind only))
  have hxlo : -1≤x := by dsimp [x]; omega
  have hylo : 1≤y := by dsimp [y]; omega
  have hapos:=square_lower (a : Int) 1 (by decide) (by omega)
  have hypos:=square_lower y 1 (by decide) (by omega)
  have hxpos : 1≤x := by
    by_cases h : 1≤x
    · exact h
    · rcases (show x= -1 ∨ x=0 by omega) with hm|hz
      · rw [hm] at he
        grind only
      · rw [hz] at he
        grind only
  have hyx : y<x := by
    by_cases h : y<x
    · exact h
    · have hsq:=square_lower y x (by omega) (by omega)
      omega
  have hsq:=square_lower (x-1) y (by omega) (by omega)
  refine ⟨a,ha4,haL,?_⟩
  dsimp [x] at hsq he
  grind only

/-- Length-three A sources cannot coexist with the following S source,
without a lower bound on the separator lengths. -/
theorem short_A_collision (L s U v i j : Nat) (hL : L≤3)
    (ha : sourceAt true L (List.replicate s false++
      (List.replicate U true++List.replicate v false)) i)
    (hs : sourceAt false s (List.replicate U true++List.replicate v false) j) : False := by
  obtain ⟨a,ha,hal,_⟩:=paired_depth_budget L s U v i j ha hs
  omega

/-- The bound three cannot be replaced by four even in a literal source
model: the two suppliers occur at different clocks six and zero. -/
theorem length_four_joint_witness :
    sourceAt true 4 (List.replicate 8 false++
      (List.replicate 4 true++List.replicate 1 false)) 6 ∧
    sourceAt false 8 (List.replicate 4 true++List.replicate 1 false) 0 := by
  constructor
  · exact ⟨4,by decide,by decide,by decide,by decide⟩
  · exact ⟨2,by decide,by decide,by decide,by decide⟩

end Recaman.ThirdSPairedDepth
