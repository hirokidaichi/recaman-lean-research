import Recaman.SlowPrimitiveClockPair
import Recaman.InitialSPaddingPositive

namespace Recaman.PositiveTwoClockHistory

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.InitialSPaddingPositive Recaman.InitialSeparatorTrim

/-- Standard initial-S padding transports both local witnesses into one
actual EndN history. It asserts no shortage of actual free additions. -/
theorem two_clocks_positive_history (w : List Bool) (i j : Nat) (hij : i<j)
    (hi : Recaman.ThreeNonsuppliedData.localSupply (w++List.replicate i true)=true)
    (hj : Recaman.ThreeNonsuppliedData.localSupply (w++List.replicate j true)=true) :
    ∃ (g : Nat → Bool) (B : Nat),
      seg g 0 0=[] ∧ cN (EndN g 0) 0 0=cN (fun x=>g x=false) 0 0 ∧
      (∀ k, 0<k → k≤B+j+1 → cN (EndN g 0) 0 k+1≤cN (fun x=>g x=false) 0 k) ∧
      (∀ r, g (B+r)=true) ∧ EndN g 0 (B+i) ∧ EndN g 0 (B+j) := by
  let T:=j+1
  let h:=w.length+T+1
  let B:=h+w.length
  let f:=finiteSign w
  let g:=trimSSequence f 0 h
  have hAall (r : Nat) : f (w.length+r)=true := finiteSign_after w r
  have hfword (r : Nat) : seg f 0 (w.length+r)=w++List.replicate r true := by
    rw [seg_add,Nat.zero_add,finiteSign_seg]
    congr 1
    apply seg_A
    intro x hx hxr
    have he:=hAall (x-w.length)
    rwa [Nat.add_sub_cancel' hx] at he
  have hgword (r : Nat) : seg g 0 (B+r)=List.replicate h false++(w++List.replicate r true) := by
    have he:=trimS_prefix f 0 h (w.length+r)
    change seg g 0 (h+(w.length+r))=List.replicate h false++seg f 0 (w.length+r) at he
    rw [hfword r] at he
    simpa only [B,Nat.add_assoc] using he
  have hAcount : cN (fun x=>g x=true) 0 (B+T)<h := by
    have ho:=ones_seg_eq_count g 0 (B+T)
    rw [hgword T,ones_append,ones_append,ones_replicate_S,ones_replicate_A] at ho
    have hbound:=(ones_bounds w).2
    dsimp [h] at ho ⊢
    omega
  have hS (r : Nat) (hr : r<h) : g r=false := by
    simp only [g,trimSSequence,if_pos hr]
  have hpos:=initial_S_positive g h (B+T) hS hAcount
  have hAallg (r : Nat) : g (B+r)=true := by
    change trimSSequence f 0 h (B+r)=true
    rw [show B+r=h+(w.length+r) by dsimp [B]; omega,trimS_tail_sign,Nat.zero_add]
    exact hAall r
  have hend (r : Nat) (hr : Recaman.ThreeNonsuppliedData.localSupply (w++List.replicate r true)=true) :
      EndN g 0 (B+r) := by
    have hl : Recaman.ThreeNonsuppliedData.localSupply (seg g 0 (B+r))=true := by
      rw [hgword r]
      have he:=(ray_supply_append_iff (List.replicate h false) w r).mpr (Or.inr hr)
      simpa only [List.append_assoc] using he
    exact (localSupply_seg_iff g 0 (B+r) (by dsimp [B,h,T]; omega) (hAallg r)).mp hl
  refine ⟨g,B,by simp [seg],by simp [cN],?_,hAallg,hend i hi,hend j hj⟩
  intro k hk hkB
  exact hpos k hk (by dsimp [T]; omega)

/-- Even zero/fullpositive actual histories have distinct final-ray
supply clocks with relative ratio arbitrarily close to one. -/
theorem actual_slow_relative_growth (N : Nat) :
    ∃ (g : Nat → Bool) (B i j : Nat),
      0<i ∧ j=i+2 ∧ (N : Int)*(j : Int)<((N : Int)+1)*(i : Int) ∧
      seg g 0 0=[] ∧ cN (EndN g 0) 0 0=cN (fun x=>g x=false) 0 0 ∧
      (∀ k, 0<k → k≤B+j+1 → cN (EndN g 0) 0 k+1≤cN (fun x=>g x=false) 0 k) ∧
      (∀ r, g (B+r)=true) ∧ EndN g 0 (B+i) ∧ EndN g 0 (B+j) := by
  obtain ⟨w,i,j,hi,hj,hratio,hfirst,hsecond⟩:=
    Recaman.SlowPrimitiveClockPair.arbitrarily_slow_relative_growth N
  obtain ⟨g,B,hseg,hzero,hpos,hA,hendi,hendj⟩:=two_clocks_positive_history w i j (by omega) hfirst hsecond
  exact ⟨g,B,i,j,hi,hj,hratio,hseg,hzero,hpos,hA,hendi,hendj⟩

end Recaman.PositiveTwoClockHistory
