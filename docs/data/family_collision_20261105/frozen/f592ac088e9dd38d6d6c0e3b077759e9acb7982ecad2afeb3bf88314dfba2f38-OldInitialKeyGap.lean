import Recaman.MassTwoThreeKeys
import Recaman.UnitTargetSASProfile

namespace Recaman.OldInitialKeyGap

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.BlockOldRay
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- The old supplier and initial-S supplier share a literal suffix. -/
theorem shared_initial_key (u x : List Bool) (d : Nat)
    (hold : runKey (u++(List.replicate d false++x))= -2) (hlocal : runKey x= -2) :
    runKey u=4*((d : Int)-mass u)*((d : Int)+(cntF x : Int))-2*(d : Int)^2 := by
  rw [runKey_append,runKey_prepend_S,cntF_append,cntF_replicate_S,hlocal] at hold
  simp only [Int.natCast_add] at hold
  grind only

private theorem gap_positive (D E d k : Int) (hD : 2≤D) (hE : 2*d+2≤E)
    (hd : 0≤d) (hkey : k=4*(d-D)*E-2*d^2) (hlo : -2≤k) : D<d := by
  by_cases hlt : D<d
  · exact hlt
  have hp:=Int.mul_nonpos_of_nonpos_of_nonneg (show d-D≤0 by omega) (show 0≤E by omega)
  have hd1 : d≤1 := by
    by_cases hh : d≤1
    · exact hh
    have hs:=Int.mul_nonneg (show 0≤d-2 by omega) (show 0≤d+2 by omega)
    grind only
  rcases (show d=0 ∨ d=1 by omega) with h0|h1
  · rw [h0] at hkey hE
    have hp:=Int.mul_pos (show 0<D by omega) (show 0<E by omega)
    grind only
  · rw [h1] at hkey hE
    have hp:=Int.mul_pos (show 0<D-1 by omega) (show 0<E by omega)
    grind only

private theorem low_mass_gap_large (D E d k : Int) (hD : D=2 ∨ D=3)
    (hE : 2*d+2≤E) (hd : D<d) (hkey : k=4*(d-D)*E-2*d^2) : 8≤k := by
  have hp:=Int.mul_nonneg (show 0≤d-D by omega) (show 0≤E-(2*d+2) by omega)
  rcases hD with h2|h3
  · rw [h2] at hd hkey hp
    have hq:=Int.mul_nonneg (show 0≤d-3 by omega) (show 0≤6*d+10 by omega)
    grind only
  · rw [h3] at hd hkey hp
    have hq:=Int.mul_nonneg (show 0≤d-4 by omega) (show 0≤6*d+8 by omega)
    grind only

/-- A common low-mass old supplier is incompatible with an initial-S
supplier whenever the literal structural S bound E>=2d+2 holds. -/
theorem low_mass_initial_excluded (u x : List Bool) (d : Nat) (hu : BlockWord u)
    (hD : mass u=2 ∨ mass u=3) (hE : 2*d+2≤d+cntF x)
    (hold : runKey (u++(List.replicate d false++x))= -2) (hlocal : runKey x= -2) : False := by
  have he:=shared_initial_key u x d hold hlocal
  have hlo : -2≤runKey u := by have hh:=block_area_quadratic_lower hu; unfold runKey; omega
  have hD2 : 2≤mass u := by omega
  have hpos:=gap_positive (mass u) ((d : Int)+(cntF x : Int)) (d : Int) (runKey u)
    hD2 (by omega) (by omega) he hlo
  have hbig:=low_mass_gap_large (mass u) ((d : Int)+(cntF x : Int)) (d : Int) (runKey u)
    hD (by omega) hpos he
  rcases hD with h2|h3
  · have hk:=Recaman.MassTwoThreeKeys.mass_two_keys u hu h2
    omega
  · have hk:=Recaman.MassTwoThreeKeys.mass_three_keys u hu h3
    omega

end Recaman.OldInitialKeyGap
