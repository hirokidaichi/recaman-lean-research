import Recaman.ThreeRunFreeGap

namespace Recaman.LocalSourcePrefixBudget

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.ASourceReuse
open Recaman.RunSupplyBudget Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality
open Recaman.LineCapacityPeriodic

/-- For an arbitrary mixed continuation b, retaining nonnegative total
mass keeps its negative key charge within twice its A count squared. -/
theorem block_continuation_key_lower (u b : List Bool) (hu : BlockWord u)
    (hm : 0≤mass (u++b)) : -2-2*(ones b)^2≤runKey (u++b) := by
  let C := mass u
  let A := ones b
  let S := (cntF b : Int)
  have hC : 0≤C := block_mass_nonnegative hu
  have hA : 0≤A := (ones_bounds b).1
  have hS : 0≤S := by dsimp [S]; omega
  have hmb : mass b=A-S := by
    have hc := cntF_int b
    have he := mass_eq b
    dsimp [A,S]
    omega
  have hSA : S≤C+A := by rw [mass_append,hmb] at hm; dsimp [C]; omega
  have hsq : (S-C)^2≤C^2+A^2 := by
    by_cases hh : S≤C
    · have hp := Int.mul_nonneg hS (show 0≤2*C-S by omega)
      have hAA := Int.mul_nonneg hA hA
      grind
    · have hp := Int.mul_nonneg (show 0≤A-(S-C) by omega) (show 0≤A+(S-C) by omega)
      have hCC := Int.mul_nonneg hC hC
      grind
  have hlow := block_area_quadratic_lower hu
  have hku : -2≤runKey u := by unfold runKey; omega
  have hkb := runKey_count_lower b
  rw [runKey_append]
  change -2-2*A^2≤runKey u+runKey b+4*C*S
  change -2*S^2≤runKey b at hkb
  grind

/-- Any mixed-word local source supplying a final-band A clock must
start after at least j+1 earlier A signs. No run-count bound or free/rank
hypothesis is assumed; the same old target is retained. -/
theorem local_source_prefix_A (u b v : List Bool) (hu : BlockWord u)
    (i T j : Nat) (hj : 2≤j) (hband : T≤i+j)
    (hm1 : mass (v++List.replicate i true)=1)
    (ha1 : areaW (v++List.replicate i true)=0)
    (hm2 : mass (u++b++v++List.replicate T true++List.replicate j false)=1)
    (ha2 : areaW (u++b++v++List.replicate T true++List.replicate j false)=0) :
    (j : Int)+1≤ones b := by
  have hpm : 0≤mass (u++b) := by
    simp only [mass_append,mass_replicate_A,mass_rep_false] at hm1 hm2 ⊢
    omega
  have hlow := block_continuation_key_lower u b hu hpm
  have hk1 := source_key_before_gap v i 0
    (by simpa only [List.replicate_zero,List.append_nil] using hm1)
    (by simpa only [List.replicate_zero,List.append_nil] using ha1)
  have hk2 := source_key_before_gap (u++b++v) T j hm2 ha2
  rw [runKey_append] at hk2
  have hcross := Int.mul_nonneg hpm (show 0≤(cntF v : Int) by omega)
  have hquad : ((j : Int)+1)^2≤(ones b)^2+2 := by grind
  have hA : 0≤ones b := (ones_bounds b).1
  by_cases hh : (j : Int)+1≤ones b
  · exact hh
  · have hp := Int.mul_nonneg (show 0≤(j : Int)-ones b by omega)
      (show 0≤(j : Int)+ones b by omega)
    grind

end Recaman.LocalSourcePrefixBudget
