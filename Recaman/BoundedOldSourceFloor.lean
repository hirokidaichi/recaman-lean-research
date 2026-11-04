import Recaman.OldSeedInversionKey

namespace Recaman.BoundedOldSourceFloor

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.BlockOldRay Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

private theorem source_rectangle_impossible (S v D K : Int) (hS : 3≤S) (hS7 : S≤7)
    (hK : 3≤K) (hvD : D≤v+1)
    (hregion : (3≤D ∧ v≤5) ∨ (4≤D ∧ v≤6))
    (hkey : 2*K+2*D*(S+v)≤S^2+v^2) : False := by
  have hpS:=Int.mul_nonneg (show 0≤S-3 by omega) (show 0≤7-S by omega)
  rcases hregion with h3|h4
  · have hpv:=Int.mul_nonneg (show 0≤v-2 by omega) (show 0≤5-v by omega)
    have hD:=Int.mul_nonneg (show 0≤D-3 by omega) (show 0≤S+v by omega)
    grind only
  · have hpv:=Int.mul_nonneg (show 0≤v-3 by omega) (show 0≤6-v by omega)
    have hD:=Int.mul_nonneg (show 0≤D-4 by omega) (show 0≤S+v by omega)
    grind only

/-- A primitive old source cannot supply this bounded separator over a
small zero head. Source mass/key, not a free tag, supplies the inequality. -/
theorem small_head_seed_excluded (u z : List Bool) (hu : BlockWord u)
    (hmz : mass z=0) (hS : 3≤cntF z) (hS7 : cntF z≤7)
    (K : Int) (hK : 3≤K) (hkz : runKey z=4*K-2*(cntF z : Int)^2)
    (v i : Nat) (hregion : (3≤mass u ∧ v≤5) ∨ (4≤mass u ∧ v≤6))
    (hmass : mass u-(v : Int)+(i : Int)=1)
    (hkey : runKey (u++z++List.replicate v false)= -2) : False := by
  have hi:=Recaman.OldSeedInversionKey.old_seed_clock_inversion u z hu hmz v i K hkz hmass hkey
  have he : (i : Int)-1=(v : Int)-mass u := by omega
  rw [he] at hi
  have hnorm : 2*K+2*mass u*((cntF z : Int)+(v : Int))≤(cntF z : Int)^2+(v : Int)^2 := by grind only
  exact source_rectangle_impossible (cntF z : Int) (v : Int) (mass u) K (by omega) (by omega) hK
    (by omega) (by rcases hregion with h|h; exact Or.inl ⟨h.1,by omega⟩; exact Or.inr ⟨h.1,by omega⟩) hnorm

end Recaman.BoundedOldSourceFloor
