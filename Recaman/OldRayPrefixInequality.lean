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
theorem seed_second_actual_two (f : Nat → Bool) (n h M m L : Nat) (w : List Bool)
    (hw : BlockWord w) (hpre : seg f 0 n=w) 
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ i, i<M → f (n+h+i)=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → f x=false)
    (hA2 : ∀ i, i<L → f (n+h+M+m+i)=true)
    (hh11 : h=11) (hM4 : M=4) (hm1 : m=1) (hL4 : L≤4) :
    cN (EndN f 0) (n+h+M+m) L≤2 := by
  have hp1 : seg f 0 (n+h)=w++List.replicate h false := by
    rw [seg_add,Nat.zero_add,hpre,seg_false f n h hS]
  have hp2 : seg f 0 (n+h+M+m)=w++(List.replicate h false++List.replicate M true++List.replicate m false) := by
    have hsegA : seg f (n+h) M=List.replicate M true := by
      apply seg_A
      intro x hx hxB
      have ha:=hA (x-(n+h)) (by omega)
      rw [Nat.add_sub_cancel' hx] at ha
      exact ha
    rw [show n+h+M+m=(n+h+M)+m by omega,seg_add,Nat.zero_add,
      seg_false f (n+h+M) m hS2,show n+h+M=(n+h)+M by omega,seg_add,Nat.zero_add,hp1,hsegA]
    simp only [List.append_assoc]
  have hb:=seed_second_ray_two w hw L hL4
  have he:=endable_A_run_count f (n+h+M+m) L _ hp2 hA2
  rw [hh11,hM4,hm1] at he
  rw [hh11,hM4,hm1]
  omega

end Recaman.OldRayPrefixInequality
