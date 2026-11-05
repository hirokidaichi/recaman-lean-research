import Recaman.UnitTargetSASProfile

namespace Recaman.FinalSTargetLengths

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.ASourceReuse Recaman.UnitTargetSASProfile

/-- An actual target beginning inside the last S and ending after the
following A/S tail forces exactly twice the gap-plus-one A signs. -/
theorem final_S_target_lengths (f : Nat → Bool) (a v T j t : Nat)
    (hta : a≤t) (htb : t<a+v)
    (hS : ∀ x, a≤x → x<a+v → f x=false)
    (hA : ∀ i, i<T → f (a+v+i)=true)
    (hgap : ∀ x, a+v+T≤x → x<a+v+T+j → f x=false)
    (htarget : Win f t (a+v+T+j-t)) :
    a+v-t=j+1 ∧ T=2*(j+1) ∧ j+1≤v := by
  let q:=a+v-t
  have hq : 1≤q := by dsimp [q]; omega
  have hqend : t+q=a+v := by dsimp [q]; omega
  have hSa : seg f t q=List.replicate q false := by
    apply seg_false
    intro x hx hxq
    exact hS x (by omega) (by omega)
  have hAa : seg f (a+v) T=List.replicate T true := by
    apply seg_A
    intro x hx hxT
    simpa only [Nat.add_sub_cancel' hx] using hA (x-(a+v)) (by omega)
  have hword : seg f t (a+v+T+j-t)=List.replicate q false++List.replicate T true++List.replicate j false := by
    rw [show a+v+T+j-t=q+T+j by omega,seg_add,seg_add,hqend,
      show t+(q+T)=a+v+T by omega,hSa,hAa,seg_false f (a+v+T) j hgap]
  have hm : mass (List.replicate q false++List.replicate T true++List.replicate j false)=1 := by
    rw [←hword,seg_mass]
    have h:=htarget.2.1
    rw [show t+(a+v+T+j-t)=a+v+T+j by omega] at h ⊢
    omega
  have ha : areaW (List.replicate q false++List.replicate T true++List.replicate j false)=0 := by
    rw [←hword,←Ar_areaW]
    exact htarget.2.2
  have hk:=source_key_before_gap (List.replicate q false) T j hm ha
  rw [S_key] at hk
  have he : ((q : Int)-((j : Int)+1))*((q : Int)+(j : Int)+1)=0 := by grind only
  have hqR : q=j+1 := by rcases Int.mul_eq_zero.mp he with he|he <;> omega
  simp only [mass_append,mass_rep_false,mass_replicate_A] at hm
  exact ⟨hqR,by omega,by dsimp [q] at hqR; omega⟩

end Recaman.FinalSTargetLengths
