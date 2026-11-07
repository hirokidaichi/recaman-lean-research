import Recaman.MixedSeparatedSources
import Recaman.OldThreeKeyParity

namespace Recaman.MixedASQuarterBudget

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.FourthSourceFamilies Recaman.ShortCounterFactorBounds

/-- A primitive source word has an odd subtraction count. This consumes
the existing all-word integral cross surplus, not a new AS identity. -/
theorem source_subtraction_odd (w : List Bool) (hk : runKey w= -2) :
    (cntF w : Int)%2=1 := by
  obtain ⟨Q,hQ⟩:=Recaman.UnitTargetPrefixParity.cross_four w
  rw [hk] at hQ
  obtain ⟨d,hd⟩:=Recaman.OldThreeKeyParity.square_even_delta (cntF w : Int)
  omega

/-- The two source families force a multiple-of-four A depth and a sharp
quadratic budget, uniformly in the entire mixed future. -/
theorem mixed_A_S_quarter_budget (x : List Bool) (L s i j : Nat)
    (ha : sourceAt true L (List.replicate s false++x) i)
    (hs : sourceAt false s x j) :
    ∃ a, 4≤a ∧ a≤L ∧ (a : Int)%4=0 ∧
      4*((s : Int)+(cntF x : Int))≤((a : Int)+2)^2 ∧
      mass (List.replicate a true++(List.replicate s false++x))+(i : Int)=1 ∧
      runKey (List.replicate a true++(List.replicate s false++x))= -2 := by
  obtain ⟨a,ha1,haL,hm,hka⟩:=ha
  obtain ⟨k,hk1,hks,_,hksrc⟩:=hs
  have hka_original:=hka
  have hzodd:=source_subtraction_odd _ hka
  have hyodd:=source_subtraction_odd _ hksrc
  simp only [cntF_append,cntF_replicate_S,Recaman.UnitTargetSASProfile.cntF_A,
    Int.natCast_add,Int.natCast_zero,Int.zero_add] at hzodd hyodd
  rw [runKey_prepend_A,runKey_prepend_S] at hka
  rw [runKey_prepend_S] at hksrc
  simp only [cntF_append,cntF_replicate_S,Int.natCast_add] at hka
  let z:=(s : Int)+(cntF x : Int)
  let y:=(k : Int)+(cntF x : Int)
  have he : z^2-y^2=2*(a : Int)*z := by dsimp [z,y]; grind only
  change z%2=1 at hzodd
  change y%2=1 at hyodd
  obtain ⟨A,hA⟩:=Recaman.OldThreeKeyParity.odd_square_eight z hzodd
  obtain ⟨B,hB⟩:=Recaman.OldThreeKeyParity.odd_square_eight y hyodd
  have hp : (a : Int)*z=4*(A-B) := by omega
  have hm4 : ((a : Int)*z)%4=0 := by rw [hp]; omega
  rw [Int.mul_emod] at hm4
  have ha4mod : (a : Int)%4=0 := by
    rcases (show z%4=1 ∨ z%4=3 by omega) with h1|h3
    · rw [h1] at hm4
      omega
    · rw [h3] at hm4
      omega
  have ha4 : 4≤a := by omega
  let u:=z-(a : Int)
  have hpy : u^2=(a : Int)^2+y^2 := by dsimp [u]; grind only
  have hmass:=hm
  simp only [mass_append,mass_replicate_A,mass_rep_false] at hmass
  have hc:=cntF_int x
  have hmx:=mass_eq x
  have hones:=(ones_bounds x).1
  have hul : -1≤u := by dsimp [u,z]; omega
  have hyl : 1≤y := by dsimp [y]; omega
  have ha2:=square_lower (a : Int) 1 (by decide) (by omega)
  have hy2:=square_lower y 1 (by decide) hyl
  have hu : 1≤u := by
    by_cases h : 1≤u
    · exact h
    · rcases (show u= -1 ∨ u=0 by omega) with hneg|hzero
      · rw [hneg] at hpy
        grind only
      · rw [hzero] at hpy
        grind only
  have hyu : y<u := by
    by_cases h : y<u
    · exact h
    · have h:=square_lower y u (by omega) (by omega)
      omega
  have huodd : u%2=1 := by dsimp [u]; omega
  have hyu2 : y≤u-2 := by omega
  have hsquare:=square_lower (u-2) y (by omega) hyu2
  have hquarter : 4*z≤((a : Int)+2)^2 := by dsimp [u] at hpy hsquare; grind only
  exact ⟨a,ha4,haL,ha4mod,hquarter,hm,hka_original⟩

/-- A depth-four example attains equality in the quadratic budget. -/
theorem quarter_budget_sharp :
    sourceAt true 4 (List.replicate 8 false++
      (List.replicate 4 true++List.replicate 1 false)) 2 ∧
    sourceAt false 8 (List.replicate 4 true++List.replicate 1 false) 0 ∧
    (4 : Int)*(8+1)=(4+2)^2 := by
  refine ⟨⟨4,by decide,by decide,by decide,by decide⟩,
    ⟨2,by decide,by decide,by decide,by decide⟩,by decide⟩

end Recaman.MixedASQuarterBudget
