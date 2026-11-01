import Recaman.MomentTargetMass
import Recaman.OldSourceKeyOrder

namespace Recaman.MomentActualTarget

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.MomentTargetMass Recaman.MomentBandOldClock Recaman.OldSourceKeyOrder

private theorem window_profile (f : Nat → Bool) (s l : Nat) (hw : Win f s l) :
    mass (seg f s l)=1 ∧ areaW (seg f s l)=0 := by
  refine ⟨?_,?_⟩
  · rw [seg_mass]
    have hm:=hw.2.1
    omega
  · rw [←Ar_areaW]
    exact hw.2.2

/-- A same-base actual target supplies the generic low-mass restrictions.
R>=5 is explicit here and is internally supplied in the counter theorem. -/
theorem actual_moment_target_low_mass (f : Nat → Bool) (n t H v T j q i : Nat) (w z : List Bool)
    (hw : BlockWord w) (hpre : seg f 0 n=w) (ht : t<n) (hz : seg f n H=z)
    (hmz : mass z=0) (B : Int) (haz : areaW z= -B)
    (hlo : 4*(cntF z : Int)+6≤B) (hhi : B≤6*(cntF z : Int)+4) (hv : 1≤v) (hq : 1≤q) (hqv : q≤v)
    (hi : i<T) (hband : T≤i+j)
    (hS : ∀ x, n+H≤x → x<n+H+v → f x=false)
    (hA : ∀ k, k<T → f (n+H+v+k)=true)
    (hgap : ∀ x, n+H+v+T≤x → x<n+H+v+T+j → f x=false)
    (htarget : Win f t (n+H+v+T+j-t))
    (hlocal : Win f (n+H+v-q) (q+i))
    (hR : 5≤j+1) :
    mass (w.drop t)≤2 ∧ v≤3 ∧ T≤j+2 ∧
      (w.drop t=[true] ∨ w.drop t=[true,true] ∨ w.drop t=[false,true,true,true]) ∧
      ((j : Int)+1)^2≤4*(cntF z : Int)+4 := by
  have hn : w.length=n := by rw [←hpre,seg_length]
  have hu : BlockWord (w.drop t) := block_suffix hw (w.take t) (w.drop t) (List.take_append_drop t w)
  have hne : w.drop t≠[] := by
    intro he
    have hl : (w.drop t).length=w.length-t := List.length_drop
    rw [he,hn] at hl
    simp only [List.length_nil] at hl
    omega
  have hd:=seg_drop f 0 n t (by omega)
  simp only [Nat.zero_add,hpre] at hd
  have hfull : seg f t (n+H+v+T+j-t)=w.drop t++z++List.replicate v false++
      List.replicate T true++List.replicate j false := by
    rw [show n+H+v+T+j-t=(n-t)+(H+v+T+j) by omega,seg_add,
      show t+(n-t)=n by omega,←hd,seg_add,seg_add,seg_add,hz,
      seg_false f (n+H) v hS]
    have hAt : seg f (n+(H+v)) T=List.replicate T true := by
      apply seg_A
      intro x hx hxT
      have hh:=hA (x-(n+H+v)) (by omega)
      rw [show n+H+v+(x-(n+H+v))=x by omega] at hh
      exact hh
    rw [hAt]
    have hSt : seg f (n+(H+v+T)) j=List.replicate j false := by
      apply seg_false
      intro x hx hxj
      exact hgap x (by omega) (by omega)
    rw [hSt]
    simp only [List.append_assoc]
  have hloc : seg f (n+H+v-q) (q+i)=List.replicate q false++List.replicate i true := by
    rw [seg_add,show n+H+v-q+q=n+H+v by omega]
    have hs : seg f (n+H+v-q) q=List.replicate q false := by
      apply seg_false
      intro x hx hxq
      exact hS x (by omega) (by omega)
    have ha : seg f (n+H+v) i=List.replicate i true := by
      apply seg_A
      intro x hx hxi
      have hh:=hA (x-(n+H+v)) (by omega)
      rw [show n+H+v+(x-(n+H+v))=x by omega] at hh
      exact hh
    rw [hs,ha]
  obtain ⟨hm,ha⟩:=window_profile f t _ htarget
  obtain ⟨hlm,hla⟩:=window_profile f (n+H+v-q) _ hlocal
  rw [hfull] at hm ha
  rw [hloc] at hlm hla
  exact moment_target_low_mass (w.drop t) z hu hne B hmz haz hlo hhi v T j q i hv hq hqv hi hband hR hm ha hlm hla


end Recaman.MomentActualTarget
