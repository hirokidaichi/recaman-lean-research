import Recaman.OldRayPrefixInequality
import Recaman.HeadRunCountBounds
namespace Recaman.S15SecondExclusion
open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

open Recaman.OldRayPrefixInequality Recaman.HeadRunSupplyBudgets

theorem S15_second_old_excluded (w : List Bool) (hw : BlockWord w) (i : Nat) (hi : i<1) :
    ¬tailOldRay w (List.replicate 12 false++List.replicate 8 true++List.replicate 2 false) i := by
  intro ho
  have hx:=old_ray_prefix_inequality w _ hw i ho
  have hm : mass (List.replicate 12 false++List.replicate 8 true++List.replicate 2 false)= -6 := by decide
  have hs : cntF (List.replicate 12 false++List.replicate 8 true++List.replicate 2 false)=14 := by decide
  have hk : runKey (List.replicate 12 false++List.replicate 8 true++List.replicate 2 false)= -328 := by decide
  rw [hm,hs,hk] at hx
  omega

theorem S15_second_ray_zero (w : List Bool) (hw : BlockWord w) (K : Nat) (hK : K≤1) :
    rayCount (w++(List.replicate 12 false++List.replicate 8 true++List.replicate 2 false)) K=0 := by
  have he : rayCount (w++(List.replicate 12 false++List.replicate 8 true++List.replicate 2 false)) K=
      rayCount (List.replicate 12 false++List.replicate 8 true++List.replicate 2 false) K := by
    unfold rayCount
    apply cN_congr
    intro i hi hiB
    rw [ray_supply_append_iff]
    constructor
    · intro h
      rcases h with hold | hlocal
      · exact False.elim (S15_second_old_excluded w hw i (by omega) hold)
      · exact hlocal
    · exact Or.inr
  rw [he]
  have hzero : rayCount (List.replicate 12 false++List.replicate 8 true++List.replicate 2 false) 1=0 := by decide
  by_cases hk0 : K=0
  · subst K; rfl
  · have hk1 : K=1 := by omega
    rw [hk1]
    exact hzero
theorem S15_second_actual_zero (f : Nat → Bool) (n h M m L : Nat) (w : List Bool)
    (hw : BlockWord w) (hpre : seg f 0 n=w) 
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ i, i<M → f (n+h+i)=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → f x=false)
    (hA2 : ∀ i, i<L → f (n+h+M+m+i)=true)
    (hh12 : h=12) (hM8 : M=8) (hm2 : m=2) (hL1 : L=1) :
    cN (EndN f 0) (n+h+M+m) L=0 := by
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
  have hb:=S15_second_ray_zero w hw L (by omega)
  have he:=endable_A_run_count f (n+h+M+m) L _ hp2 hA2
  rw [hh12,hM8,hm2] at he
  rw [hh12,hM8,hm2]
  omega

end Recaman.S15SecondExclusion
