import Recaman.BlockOldRay
namespace Recaman.OldRayPrefixInequality
open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- Necessary inequality for every old source, without any mass cutoff. -/
theorem old_ray_prefix_inequality (w v : List Bool) (hw : BlockWord w) (i : Nat)
    (ho : tailOldRay w v i) : runKey v+4*(1-mass v-(i : Int))*(cntF v : Int)≤0 := by
  obtain ⟨t,ht,hm,hk⟩:=ho
  have hs : BlockWord (w.drop t) := block_suffix hw (w.take t) (w.drop t) (List.take_append_drop t w)
  have hb:=block_area_quadratic_lower hs
  have hlo : -2≤runKey (w.drop t) := by unfold runKey; omega
  have he : 1-mass v-(i : Int)=mass (w.drop t) := by omega
  rw [he]
  omega

/-- The short second ray of the two residual shapes has no old suppliers. -/
theorem seed_second_old_excluded (w : List Bool) (hw : BlockWord w) (i : Nat) (hi : i<4) :
    ¬tailOldRay w (List.replicate 11 false++List.replicate 4 true++List.replicate 1 false) i := by
  intro ho
  have hx:=old_ray_prefix_inequality w _ hw i ho
  have hm : mass (List.replicate 11 false++List.replicate 4 true++List.replicate 1 false)= -8 := by decide
  have hs : cntF (List.replicate 11 false++List.replicate 4 true++List.replicate 1 false)=12 := by decide
  have hk : runKey (List.replicate 11 false++List.replicate 4 true++List.replicate 1 false)= -272 := by decide
  rw [hm,hs,hk] at hx
  omega

theorem seed_second_ray_two (w : List Bool) (hw : BlockWord w) (K : Nat) (hK : K≤4) :
    rayCount (w++(List.replicate 11 false++List.replicate 4 true++List.replicate 1 false)) K≤2 := by
  have he : rayCount (w++(List.replicate 11 false++List.replicate 4 true++List.replicate 1 false)) K=
      rayCount (List.replicate 11 false++List.replicate 4 true++List.replicate 1 false) K := by
    unfold rayCount
    apply cN_congr
    intro i hi hiB
    rw [ray_supply_append_iff]
    constructor
    · intro h
      rcases h with hold | hlocal
      · exact False.elim (seed_second_old_excluded w hw i (by omega) hold)
      · exact hlocal
    · exact Or.inr
  rw [he]
  exact rayCount_S_A_S 11 4 1 K
end Recaman.OldRayPrefixInequality
