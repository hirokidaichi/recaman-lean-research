import Recaman.ThirdSeparatorClock
import Recaman.ASourceReuse

namespace Recaman.ThirdSTargetProfile

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.ASourceReuse Recaman.FourthSourceFamilies Recaman.ShortCounterFactorBounds

/-- The same actual target beginning in the third S separator keeps
its residual S length and both subsequent runs. -/
theorem actual_third_S_target_profile (f : Nat → Bool) (a s U v T j t : Nat)
    (hta : a≤t) (htb : t<a+s)
    (hS0 : ∀ x, a≤x → x<a+s → f x=false)
    (hA0 : ∀ i, i<U → f (a+s+i)=true)
    (hS : ∀ x, a+s+U≤x → x<a+s+U+v → f x=false)
    (hA : ∀ i, i<T → f (a+s+U+v+i)=true)
    (hgap : ∀ x, a+s+U+v+T≤x → x<a+s+U+v+T+j → f x=false)
    (htarget : Win f t (a+s+U+v+T+j-t)) :
    let q:=a+s-t
    T+U=(j+1)+q+v ∧ ((q : Int)+(v : Int))^2=((j : Int)+1)^2+2*(U : Int)*(v : Int) := by
  dsimp only
  let q:=a+s-t
  have hqend : t+q=a+s := by dsimp [q]; omega
  have hS0' : seg f t q=List.replicate q false := by
    apply seg_false
    intro x hx hxq
    exact hS0 x (by omega) (by omega)
  have hA0' : seg f (a+s) U=List.replicate U true := by
    apply seg_A
    intro x hx hxU
    simpa only [Nat.add_sub_cancel' hx] using hA0 (x-(a+s)) (by omega)
  have hAa : seg f (a+s+U+v) T=List.replicate T true := by
    apply seg_A
    intro x hx hxT
    simpa only [Nat.add_sub_cancel' hx] using hA (x-(a+s+U+v)) (by omega)
  have hword : seg f t (a+s+U+v+T+j-t)=List.replicate q false++List.replicate U true++
      List.replicate v false++List.replicate T true++List.replicate j false := by
    rw [show a+s+U+v+T+j-t=q+U+v+T+j by omega,seg_add,seg_add,seg_add,seg_add,hqend,
      show t+(q+U)=a+s+U by omega,show t+(q+U+v)=a+s+U+v by omega,
      show t+(q+U+v+T)=a+s+U+v+T by omega,hS0',hA0',hAa,
      seg_false f (a+s+U) v hS,seg_false f (a+s+U+v+T) j hgap]
  have hm : mass (List.replicate q false++List.replicate U true++
      List.replicate v false++List.replicate T true++List.replicate j false)=1 := by
    rw [←hword,seg_mass]
    have hh:=htarget.2.1
    rw [show t+(a+s+U+v+T+j-t)=a+s+U+v+T+j by omega] at hh ⊢
    omega
  have ha : areaW (List.replicate q false++List.replicate U true++
      List.replicate v false++List.replicate T true++List.replicate j false)=0 := by
    rw [←hword,←Ar_areaW]
    exact htarget.2.2
  have hk:=source_key_before_gap
    (List.replicate q false++List.replicate U true++List.replicate v false) T j hm ha
  rw [runKey_S_A_S] at hk
  simp only [mass_append,mass_rep_false,mass_replicate_A] at hm
  change T+U=(j+1)+q+v ∧ ((q : Int)+(v : Int))^2=((j : Int)+1)^2+2*(U : Int)*(v : Int)
  exact ⟨by omega,by grind only⟩

/-- A same-separator supplier uses a strictly shorter suffix than the
selected target, with an exact factored key difference. -/
theorem third_S_same_separator_clock (q s U v T j i : Nat) (hj : 1≤j)
    (hbalance : T+U=j+1+q+v)
    (hsq : ((q : Int)+(v : Int))^2=((j : Int)+1)^2+2*(U : Int)*(v : Int))
    (hs : sourceAt false s (List.replicate U true++List.replicate v false) i) :
    i+j<T ∧ ∃ k, 1≤k ∧ k≤s ∧ k<q ∧ q-k=T-j-i ∧
      ((q : Int)-(k : Int))*((q : Int)+(k : Int)+2*(v : Int))=((j : Int)+1)^2-1 := by
  obtain ⟨k,hk,hks,hm,hkey⟩:=hs
  rw [←List.append_assoc,runKey_S_A_S] at hkey
  simp only [mass_append,mass_rep_false,mass_replicate_A] at hm
  have hR:=square_lower ((j : Int)+1) 2 (by decide) (by omega)
  have hlt : k<q := by
    by_cases he : k<q
    · exact he
    · have hsq' := square_lower ((k : Int)+(v : Int)) ((q : Int)+(v : Int)) (by omega) (by omega)
      grind only
  exact ⟨by omega,k,hk,hks,hlt,by omega,by grind only⟩

end Recaman.ThirdSTargetProfile
