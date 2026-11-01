import Recaman.TenHeadTargetCases

namespace Recaman.MomentTargetMass

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.ASourceReuse Recaman.FourRunTargetArea

private theorem mass_separator_scalar (S C V R B : Int) (hS : 0≤S) (hC : 1≤C)
    (hV : 1≤V) (hR : 5≤R) (hCV : V-1≤C) (hB : B≤6*S+4)
    (hk : R*R+2*C*(S+V)-V*V≤B+1) : C≤2 ∧ V≤3 := by
  have hRp:=Int.mul_nonneg (show 0≤R-5 by omega) (show 0≤R+5 by omega)
  have hRsq : 25≤R*R := by grind only
  have hV3 : V≤3 := by
    by_cases hh : V≤3
    · exact hh
    · have hp:=Int.mul_nonneg (show 0≤C-V+1 by omega) (show 0≤S+V by omega)
      have hq:=Int.mul_nonneg (show 0≤V-4 by omega) hS
      have hr:=Int.mul_nonneg (show 0≤V-4 by omega) (show 0≤V+2 by omega)
      grind only
  have hC2 : C≤2 := by
    by_cases hh : C≤2
    · exact hh
    · have hp:=Int.mul_nonneg (show 0≤C-3 by omega) (show 0≤S+V by omega)
      have hv : V=1 ∨ V=2 ∨ V=3 := by omega
      rcases hv with rfl|rfl|rfl <;> grind only
  exact ⟨hC2,hV3⟩

/-- Arbitrary-length zero-mass moment-band heads have a low-mass TARGET
suffix and at most three final S signs when the same final-S source is
in band. No mass bound is imposed on other old suppliers. -/
theorem moment_target_low_mass (u z : List Bool) (hu : BlockWord u) (hne : u≠[])
    (B : Int) (hmz : mass z=0) (haz : areaW z= -B)
    (hlo : 4*(cntF z : Int)+6≤B) (hhi : B≤6*(cntF z : Int)+4)
    (v T j q i : Nat) (hv : 1≤v) (hq : 1≤q) (hqv : q≤v) (hi : i<T) (hband : T≤i+j)
    (hR : 5≤j+1)
    (hm : mass (u++z++List.replicate v false++List.replicate T true++List.replicate j false)=1)
    (ha : areaW (u++z++List.replicate v false++List.replicate T true++List.replicate j false)=0)
    (hlm : mass (List.replicate q false++List.replicate i true)=1)
    (hla : areaW (List.replicate q false++List.replicate i true)=0) :
    mass u≤2 ∧ v≤3 ∧ T≤j+2 ∧
      (u=[true] ∨ u=[true,true] ∨ u=[false,true,true,true]) ∧
      ((j : Int)+1)^2≤4*(cntF z : Int)+4 := by
  obtain ⟨hq1,hi2⟩:=final_S_source_clock q i hlm hla
  have hC : 1≤mass u := (sufPos_block hu [] u rfl hne).1
  have hm' := hm
  simp only [mass_append,mass_rep_false,mass_replicate_A,hmz] at hm'
  have hk:=source_key_before_gap (u++z++List.replicate v false) T j hm ha
  have hkz : runKey z= -2*B := by unfold runKey; rw [hmz,haz]; grind only
  rw [runKey_append_S,runKey_append,hkz,mass_append,hmz] at hk
  have hkey : runKey u=2*B-4*mass u*((cntF z : Int)+(v : Int))+2*(v : Int)^2-2*((j : Int)+1)^2 := by grind only
  have hl:=block_area_quadratic_lower hu
  have hlow : -2≤runKey u := by unfold runKey; omega
  have hc:=mass_separator_scalar (cntF z : Int) (mass u) (v : Int) ((j : Int)+1) B
    (by omega) hC (by omega) (by omega) (by omega) hhi (by grind only)
  have hwords : u=[true] ∨ u=[true,true] ∨ u=[false,true,true,true] := by
    by_cases h1 : mass u=1
    · exact Or.inl (block_mass_one hu h1)
    · rcases block_mass_two hu (by omega) with he|he
      · exact Or.inr (Or.inl he)
      · exact Or.inr (Or.inr he)
  refine ⟨hc.1,by omega,by omega,hwords,?_⟩
  have hvv : v=1 ∨ v=2 ∨ v=3 := by omega
  rcases hwords with rfl|rfl|rfl <;>
    have hmval : mass _ = _ := by decide
  all_goals simp only [mass_cons,mass_nil,Recaman.ShortPeriodicSupply.sign,runKey,areaW,
    List.length_cons,List.length_nil] at hkey hm'
  all_goals rcases hvv with rfl|rfl|rfl <;> grind only

/-- Both low-mass alternatives and v=3 must be retained. This is a raw
same-target control, not an actual free-gap/C1 counterexample. -/
theorem mass_two_separator_three_control :
    let u:=[true,true]
    let z:=List.replicate 8 false++List.replicate 8 true++List.replicate 3 false++
      List.replicate 2 true++[false]++List.replicate 2 true
    BlockWord u ∧ mass z=0 ∧ cntF z=12 ∧ areaW z= -76 ∧
    (4*12+6 : Int)≤76 ∧ (76 : Int)≤6*12+4 ∧
    mass (u++z++List.replicate 3 false++List.replicate 6 true++List.replicate 4 false)=1 ∧
    areaW (u++z++List.replicate 3 false++List.replicate 6 true++List.replicate 4 false)=0 ∧
    mass ([false,true,true])=1 ∧ areaW [false,true,true]=0 ∧ (6 : Nat)≤2+4 := by
  dsimp only
  refine ⟨BlockWord.free (BlockWord.free BlockWord.nil),by decide,by decide,by decide,
    by decide,by decide,by decide,by decide,by decide,by decide,by decide⟩

end Recaman.MomentTargetMass
