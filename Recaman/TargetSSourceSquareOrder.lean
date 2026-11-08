import Recaman.TwoSecondSLastFour

namespace Recaman.TargetSSourceSquareOrder

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.FourthSourceFamilies Recaman.ShortCounterFactorBounds

/-- A source's own nonnegative clock puts its square above D^2,
while the same target puts it strictly below D^2. No source-shape
or R/D energy classification is needed. -/
theorem last_S_source_excluded (q L R D : Int) (s U v i : Nat)
    (hq : 1≤q) (hR : q+1≤R) (hD : 0≤D) (hU : D+1≤(U : Int))
    (he : D^2=R^2+(L-q)^2-q^2+2*(U : Int)*(v : Int)) :
    ¬sourceAt false s (List.replicate U true++List.replicate v false) i := by
  rintro ⟨k,hk,hks,hm,hkey⟩
  rw [←List.append_assoc,runKey_S_A_S] at hkey
  simp only [mass_append,mass_rep_false,mass_replicate_A] at hm
  have hJ : D≤(k : Int)+(v : Int) := by omega
  have hp:=Int.mul_nonneg (show 0≤(k : Int)+(v : Int)-D by omega)
    (show 0≤(k : Int)+(v : Int)+D by omega)
  have hL:=Int.sq_nonneg (L-q)
  have hR2:=square_lower R (q+1) (by omega) hR
  have hsq : ((k : Int)+(v : Int))^2=1+2*(U : Int)*(v : Int) := by grind only
  grind only

end Recaman.TargetSSourceSquareOrder
