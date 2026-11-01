import Recaman.OldSourceKeyOrder

namespace Recaman.OldTargetLocalTail

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.ASourceReuse
open Recaman.RunClockClassifier Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- A source after an initial S prefix cannot supply a final-band A
clock when a BlockWord old source supplies the endpoint after a positive
S gap. The later common word and all lengths remain unrestricted. -/
theorem initial_S_tail_exclusion (u v : List Bool) (hu : BlockWord u)
    (a i T j : Nat) (hj : 1≤j) (hband : T≤i+j)
    (hm1 : mass (v++List.replicate i true)=1)
    (ha1 : areaW (v++List.replicate i true)=0)
    (hm2 : mass (u++List.replicate a false++v++List.replicate T true++List.replicate j false)=1)
    (ha2 : areaW (u++List.replicate a false++v++List.replicate T true++List.replicate j false)=0) : False := by
  have hk1 := source_key_before_gap v i 0
    (by simpa only [List.replicate_zero,List.append_nil] using hm1)
    (by simpa only [List.replicate_zero,List.append_nil] using ha1)
  have hk2 := source_key_before_gap (u++List.replicate a false++v) T j hm2 ha2
  have hmass : 0≤mass u-(a : Int) := by
    simp only [mass_append,mass_replicate_A,mass_rep_false] at hm1 hm2
    omega
  have hlow := block_area_quadratic_lower hu
  have hku : -2≤runKey u := by unfold runKey; omega
  have hp := Int.mul_nonneg (show 0≤(a : Int) by omega)
    (show 0≤2*mass u-(a : Int) by omega)
  have hkp : -2≤runKey (u++List.replicate a false) := by
    rw [runKey_append_S]
    grind
  have hpm : 0≤mass (u++List.replicate a false) := by
    rw [mass_append,mass_rep_false]
    exact hmass
  have hcross := Int.mul_nonneg hpm (show 0≤(cntF v : Int) by omega)
  have hjprod := Int.mul_nonneg (show 0≤(j : Int)-1 by omega)
    (show 0≤(j : Int)+3 by omega)
  rw [runKey_append] at hk2
  grind

end Recaman.OldTargetLocalTail
