import Recaman.LowerMomentOldClock
import Recaman.ShortGapLocalBudget

namespace Recaman.LowerMomentBoundary

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

open Recaman.FourthSourceFamilies Recaman.ShortGapSourceClocks Recaman.OneGapInteriorA
open Recaman.ASourceReuse

private theorem boundary_scalar (S C V R : Int) (hS : 0≤S) (hC : 1≤C)
    (hV : 1≤V) (hR : 5≤R) (hCV : V-1≤C)
    (hk : R*R+2*C*(S+V)-V*V≤4*S+6) : C=1 ∧ V≤2 := by
  have hRp:=Int.mul_nonneg (show 0≤R-5 by omega) (show 0≤R+5 by omega)
  have hRsq : 25≤R*R := by grind only
  have hV2 : V≤2 := by
    by_cases hh : V≤2
    · exact hh
    · have hp:=Int.mul_nonneg (show 0≤C-V+1 by omega) (show 0≤S+V by omega)
      have hq:=Int.mul_nonneg (show 0≤V-3 by omega) hS
      have hr:=Int.mul_nonneg (show 0≤V-3 by omega) (show 0≤V+1 by omega)
      grind only
  have hv : V=1 ∨ V=2 := by omega
  have hC1 : C=1 := by
    by_cases hh : C=1
    · exact hh
    · have hp:=Int.mul_nonneg (show 0≤C-2 by omega) (show 0≤S+V by omega)
      rcases hv with rfl|rfl <;> grind only
  exact ⟨hC1,hV2⟩

/-- Exact boundary target coupling forces a single final S and a large
head. No bound on the other old-source masses is supplied as an input. -/
theorem lower_boundary_target (u z : List Bool) (hu : BlockWord u) (hne : u≠[])
    (hmz : mass z=0) (B : Int) (haz : areaW z= -B) (hB : B=4*(cntF z : Int)+5)
    (v T j : Nat) (hv : 1≤v) (hR : 5≤j+1) (hband : T≤j+2)
    (hm : mass (u++z++List.replicate v false++List.replicate T true++List.replicate j false)=1)
    (ha : areaW (u++z++List.replicate v false++List.replicate T true++List.replicate j false)=0) :
    u=[true] ∧ v=1 ∧ T=j+1 ∧ 10≤cntF z := by
  have hC : 1≤mass u := (sufPos_block hu [] u rfl hne).1
  have hm' := hm
  simp only [mass_append,mass_rep_false,mass_replicate_A,hmz] at hm'
  have hk:=source_key_before_gap (u++z++List.replicate v false) T j hm ha
  have hkz : runKey z= -2*B := by unfold runKey; rw [hmz,haz]; grind only
  rw [runKey_append_S,runKey_append,hkz,mass_append,hmz] at hk
  have hkey : runKey u=2*B-4*mass u*((cntF z : Int)+(v : Int))+2*(v : Int)^2-2*((j : Int)+1)^2 := by grind only
  have hl:=block_area_quadratic_lower hu
  have hlow : -2≤runKey u := by unfold runKey; omega
  obtain ⟨hC1,hV2⟩:=boundary_scalar (cntF z : Int) (mass u) (v : Int) ((j : Int)+1)
    (by omega) hC (by omega) (by omega) (by omega) (by grind only)
  have huA:=block_mass_one hu hC1
  have hku : runKey u=0 := by rw [huA]; decide
  rw [hku,hC1] at hkey
  have hv12 : v=1 ∨ v=2 := by omega
  have hv1 : v=1 := by
    rcases hv12 with hh|hh
    · exact hh
    · rw [hh] at hkey
      have hc : ((j : Int)+1)*((j : Int)+1)=2*(cntF z : Int)+5 := by grind only
      exact False.elim (Recaman.LowerMomentOldClock.lower_five_circle_excluded z hmz B ((j : Int)+1) haz hB hc)
  refine ⟨huA,hv1,by omega,?_⟩
  rw [hv1] at hkey
  have hRprod:=Int.mul_nonneg (show 0≤((j : Int)+1)-5 by omega) (show 0≤((j : Int)+1)+5 by omega)
  grind only

end Recaman.LowerMomentBoundary
