import Recaman.MomentActualTarget

namespace Recaman.MomentTargetProfile

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.ASourceReuse

/-- The same actual old target reconstructs its full raw word without
truncating the prefix before the chosen source. -/
theorem actual_target_word_profile (f : Nat → Bool) (n t H v T j : Nat) (w z : List Bool)
    (hpre : seg f 0 n=w) (ht : t<n) (hz : seg f n H=z)
    (hS : ∀ x, n+H≤x → x<n+H+v → f x=false)
    (hA : ∀ k, k<T → f (n+H+v+k)=true)
    (hgap : ∀ x, n+H+v+T≤x → x<n+H+v+T+j → f x=false)
    (htarget : Win f t (n+H+v+T+j-t)) :
    mass (w.drop t++z++List.replicate v false++List.replicate T true++List.replicate j false)=1 ∧
    areaW (w.drop t++z++List.replicate v false++List.replicate T true++List.replicate j false)=0 := by
  have hn : w.length=n := by rw [←hpre,seg_length]
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
  rw [←hfull]
  constructor
  · rw [seg_mass]
    have hh:=htarget.2.1
    rw [show t+(n+H+v+T+j-t)=n+H+v+T+j by omega] at hh ⊢
    omega
  · rw [←Ar_areaW]
    exact htarget.2.2

/-- A primitive key equality for the same measured old target. This is
an accounting helper, not a free-count or C1 theorem. -/
theorem actual_zero_mass_target_key (f : Nat → Bool) (n t H v T j : Nat) (w z : List Bool)
    (hpre : seg f 0 n=w) (ht : t<n) (hz : seg f n H=z)
    (hmz : mass z=0) (B : Int) (haz : areaW z= -B)
    (hS : ∀ x, n+H≤x → x<n+H+v → f x=false)
    (hA : ∀ k, k<T → f (n+H+v+k)=true)
    (hgap : ∀ x, n+H+v+T≤x → x<n+H+v+T+j → f x=false)
    (htarget : Win f t (n+H+v+T+j-t)) :
    runKey (w.drop t)=2*B-4*mass (w.drop t)*((cntF z : Int)+(v : Int))+
      2*(v : Int)^2-2*((j : Int)+1)^2 := by
  obtain ⟨hm,ha⟩:=actual_target_word_profile f n t H v T j w z hpre ht hz hS hA hgap htarget
  have hk:=source_key_before_gap (w.drop t++z++List.replicate v false) T j hm ha
  have hkz : runKey z= -2*B := by unfold runKey; rw [hmz,haz]; grind only
  rw [runKey_append_S,runKey_append,hkz,mass_append,hmz] at hk
  grind only

end Recaman.MomentTargetProfile
