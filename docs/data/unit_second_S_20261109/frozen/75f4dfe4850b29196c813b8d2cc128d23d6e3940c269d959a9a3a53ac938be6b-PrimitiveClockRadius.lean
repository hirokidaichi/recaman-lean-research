import Recaman.PrimitiveLayerClockCost

namespace Recaman.PrimitiveClockRadius

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.ShortCounterFactorBounds

/-- This is the standard A-before-S pair upper bound, used only as a helper. -/
theorem cross_upper (w : List Bool) :
    runKey w+2*(cntF w : Int)^2≤4*ones w*(cntF w : Int) := by
  induction w with
  | nil => decide
  | cons b w ih =>
    cases b with
    | false =>
      have he:=Recaman.SourceCrossSurplus.cross_append [false] w
      have h0 : runKey [false]+2*(cntF [false] : Int)^2=0 := by decide
      have ha : ones [false]=0 := by decide
      rw [h0,ha] at he
      have hcnt : (cntF ([false]++w) : Int)=1+(cntF w : Int) := by simp [cntF]
      have hones : ones ([false]++w)=ones w := by simp [ones]
      have hon:=(ones_bounds w).1
      change runKey ([false]++w)+2*(cntF ([false]++w) : Int)^2≤4*ones ([false]++w)*(cntF ([false]++w) : Int)
      rw [hcnt,hones] at he ⊢
      grind only
    | true =>
      have he:=Recaman.SourceCrossSurplus.cross_append [true] w
      have h0 : runKey [true]+2*(cntF [true] : Int)^2=0 := by decide
      have ha : ones [true]=1 := by decide
      rw [h0,ha] at he
      have hcnt : (cntF ([true]++w) : Int)=(cntF w : Int) := by simp [cntF]
      have hones : ones ([true]++w)=1+ones w := by simp [ones]
      change runKey ([true]++w)+2*(cntF ([true]++w) : Int)^2≤4*ones ([true]++w)*(cntF ([true]++w) : Int)
      rw [hcnt,hones] at he ⊢
      grind only

/-- F=1 is exceptional; a genuine layer below supplies F>=3 internally. -/
theorem primitive_clock_half_S (u : List Bool) (i : Nat) (hF : 3≤cntF u)
    (hkey : runKey u= -2) (hm : mass u+(i : Int)=1) :
    2*(i : Int)≤(cntF u : Int)+1 := by
  have hu:=cross_upper u
  rw [hkey] at hu
  have hc:=cntF_int u
  have hmass:=mass_eq u
  have hodd:=Recaman.MixedASQuarterBudget.source_subtraction_odd u hkey
  by_cases hh : 2*(i : Int)≤(cntF u : Int)+1
  · exact hh
  · have hA : 2*ones u≤(cntF u : Int)-1 := by omega
    have hp:=Int.mul_nonneg (show 0≤(cntF u : Int)-2*ones u-1 by omega)
      (show 0≤(cntF u : Int) by omega)
    grind only

/-- The absolute inner clock, rather than just its increment, has a
sharp quadratic A cost, uniformly in the entire mixed future. -/
theorem layer_A_square (u : List Bool) (a b i j : Nat) (hb : 1≤b)
    (hkey : runKey u= -2)
    (hnewkey : runKey (List.replicate a true++(List.replicate b false++u))= -2)
    (hm : mass u+(i : Int)=1)
    (hnewmass : mass (List.replicate a true++(List.replicate b false++u))+(j : Int)=1) :
    8*(i : Int)≤(a : Int)^2 := by
  obtain ⟨hij,hcost⟩:=Recaman.PrimitiveLayerClockCost.layer_clock_A_cost u a b i j hb hkey hnewkey hm hnewmass
  simp only [mass_append,mass_replicate_A,mass_rep_false] at hnewmass
  rw [runKey_prepend_A,runKey_prepend_S,hkey] at hnewkey
  simp only [cntF_append,cntF_replicate_S,Int.natCast_add] at hnewkey
  let d:=(j : Int)-(i : Int)
  have hd : 2≤d := by dsimp [d]; omega
  have hacost : d+2≤(a : Int) := by dsimp [d]; omega
  have he : (a : Int)^2=d^2+2*d*(cntF u : Int) := by dsimp [d]; grind only
  have hF3 : 3≤cntF u := by
    by_cases hh : 3≤cntF u
    · exact hh
    · have hs:=square_lower (a : Int) (d+2) (by omega) hacost
      have hp:=Int.mul_nonneg (show 0≤d by omega) (show 0≤2-(cntF u : Int) by omega)
      grind only
  have hclock:=primitive_clock_half_S u i hF3 hkey hm
  have hp:=Int.mul_nonneg (show 0≤d-2 by omega) (show 0≤d+2+2*(cntF u : Int) by omega)
  grind only

end Recaman.PrimitiveClockRadius
