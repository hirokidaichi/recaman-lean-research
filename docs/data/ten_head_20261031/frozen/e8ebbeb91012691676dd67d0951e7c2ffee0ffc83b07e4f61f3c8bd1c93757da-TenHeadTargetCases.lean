import Recaman.MomentBandOldClock

namespace Recaman.TenHeadTargetCases

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.ASourceReuse Recaman.FourRunTargetArea

private theorem twice_area_parity (z : List Bool) :
    ∃ k : Int, 2*areaW z=(z.length : Int)*((z.length : Int)+1)+4*k := by
  induction z with
  | nil => exact ⟨0,by decide⟩
  | cons x z ih =>
    obtain ⟨k,hk⟩:=ih
    cases x
    · refine ⟨k-(z.length : Int)-1,?_⟩
      simp only [areaW,Recaman.ShortPeriodicSupply.sign,List.length_cons,Int.natCast_add,Int.natCast_one]
      grind only
    · refine ⟨k,?_⟩
      simp only [areaW,Recaman.ShortPeriodicSupply.sign,List.length_cons,Int.natCast_add,Int.natCast_one]
      grind only

private theorem target_scalar (C V R B : Int) (hC : 1≤C) (hV : 1≤V)
    (hR : 5≤R) (hCV : V-1≤C) (hB : B≤64)
    (hk : R*R+2*C*(10+V)-V*V≤B+1) :
    C=1 ∧ (V=1 ∨ V=2) ∧ (R=5 ∨ R=6) := by
  have hRprod:=Int.mul_nonneg (show 0≤R-5 by omega) (show 0≤R+5 by omega)
  have hRsq : 25≤R*R := by grind only
  have hV12 : V=1 ∨ V=2 := by
    by_cases hh : V≤2
    · omega
    · have hp:=Int.mul_nonneg (show 0≤C-V+1 by omega) (show 0≤10+V by omega)
      have hq:=Int.mul_nonneg (show 0≤V-3 by omega) (show 0≤V+21 by omega)
      grind only
  have hCone : C=1 := by
    rcases hV12 with hv|hv <;> rw [hv] at hk <;> grind only
  have hR6 : R≤6 := by
    by_cases hh : R≤6
    · exact hh
    · have hp:=Int.mul_nonneg (show 0≤R-7 by omega) (show 0≤R+7 by omega)
      rw [hCone] at hk
      rcases hV12 with hv|hv <;> rw [hv] at hk <;> grind only
  exact ⟨hCone,hV12,by omega⟩

/-- The same target suffix and arbitrary zero-mass ten-S head reduce to
exactly two cases. No bound on other old sources is imposed. The lower
R bound is a premise here, and is supplied from actual counts separately. -/
theorem ten_head_target_cases (u z : List Bool) (hu : BlockWord u) (hne : u≠[])
    (B : Int) (hmz : mass z=0) (hSz : cntF z=10) (haz : areaW z= -B)
    (hlo : 46≤B) (hhi : B≤64) (v T j q i : Nat)
    (hv : 1≤v) (hq : 1≤q) (hqv : q≤v) (hi : i<T) (hband : T≤i+j)
    (hR : 5≤j+1)
    (hm : mass (u++z++List.replicate v false++List.replicate T true++List.replicate j false)=1)
    (ha : areaW (u++z++List.replicate v false++List.replicate T true++List.replicate j false)=0)
    (hlm : mass (List.replicate q false++List.replicate i true)=1)
    (hla : areaW (List.replicate q false++List.replicate i true)=0) :
    u=[true] ∧ q=1 ∧ i=2 ∧
      ((v=1 ∧ T=5 ∧ j=4 ∧ B=46) ∨ (v=2 ∧ T=7 ∧ j=5 ∧ B=56)) := by
  obtain ⟨hq1,hi2⟩:=final_S_source_clock q i hlm hla
  have hC : 1≤mass u := (sufPos_block hu [] u rfl hne).1
  have hm' := hm
  simp only [mass_append,mass_rep_false,mass_replicate_A,hmz] at hm'
  have hk:=source_key_before_gap (u++z++List.replicate v false) T j hm ha
  have hkz : runKey z= -2*B := by unfold runKey; rw [hmz,haz]; grind only
  rw [runKey_append_S,runKey_append,hkz,hSz,mass_append,hmz] at hk
  have hkey : runKey u=2*B-4*mass u*(10+(v : Int))+2*(v : Int)^2-2*((j : Int)+1)^2 := by grind only
  have hl:=block_area_quadratic_lower hu
  have hlow : -2≤runKey u := by unfold runKey; omega
  have hc:=target_scalar (mass u) (v : Int) ((j : Int)+1) B hC (by omega)
    (by omega) (by omega) hhi (by grind only)
  obtain ⟨hC1,hv12,hj56⟩:=hc
  have huA:=block_mass_one hu hC1
  have hkey0 : runKey u=0 := by rw [huA]; decide
  have hlen : z.length=20 := by have h:=mass_cntF z; rw [hmz,hSz] at h; omega
  obtain ⟨k,hkpar⟩:=twice_area_parity z
  rw [haz,hlen] at hkpar
  have hBeven : B%2=0 := by omega
  have hcases : (v=1 ∧ T=5 ∧ j=4 ∧ B=46) ∨ (v=2 ∧ T=7 ∧ j=5 ∧ B=56) := by
    rw [hkey0,hC1] at hkey
    rcases hv12 with hv1|hv2 <;> rcases hj56 with hj5|hj6
    · have hvv : v=1 := by omega
      have hjj : j=4 := by omega
      subst v; subst j
      left
      refine ⟨rfl,?_,rfl,?_⟩ <;> grind only
    · have hvv : v=1 := by omega
      have hjj : j=5 := by omega
      subst v; subst j
      have hB57 : B=57 := by grind only
      omega
    · have hvv : v=2 := by omega
      have hjj : j=4 := by omega
      subst v; subst j
      grind only
    · have hvv : v=2 := by omega
      have hjj : j=5 := by omega
      subst v; subst j
      right
      refine ⟨rfl,?_,rfl,?_⟩ <;> grind only
  exact ⟨huA,hq1,hi2,hcases⟩

end Recaman.TenHeadTargetCases
