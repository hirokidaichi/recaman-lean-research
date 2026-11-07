import Recaman.InitialSPaddingPositive

namespace Recaman.PaddedLayeredSupply

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.LayeredPrimitiveSupply Recaman.InitialSPaddingPositive Recaman.InitialSeparatorTrim

/-- Zero/fullpositive and an actual endpoint target do not give a
run-independent constant bound on the final A ray's supplied clocks.
This is not a free-gap counterexample: no lack of actual free is claimed. -/
theorem positive_history_many_last_clocks (N : Nat) :
    ∃ (f : Nat → Bool) (B T : Nat),
      seg f 0 0=[] ∧ cN (EndN f 0) 0 0=cN (fun i=>f i=false) 0 0 ∧
      (∀ k, 0<k → k≤B+T → cN (EndN f 0) 0 k+1≤cN (fun i=>f i=false) 0 k) ∧
      EndN f 0 (B+T) ∧ (∀ i, i<T → f (B+i)=true) ∧
      N+1≤cN (EndN f 0) B T := by
  let d:=3^(N+1)
  let w:=layered (N+1)
  let T:=d+1
  let h:=3*d+3
  let B:=h+w.length
  let f:=finiteSign w
  let g:=trimSSequence f 0 h
  obtain ⟨hc,hm,hkey⟩:=layered_profile (N+1)
  change cntF w=3*d at hc
  change mass w= -(d : Int) at hm
  have hone : ones w=2*(d : Int) := by
    have hcnt:=cntF_int w
    have hmass:=mass_eq w
    omega
  have hAall (i : Nat) : f (w.length+i)=true := finiteSign_after w i
  have hfword : seg f 0 (w.length+T)=w++List.replicate T true := by
    rw [seg_add,Nat.zero_add]
    have hf0 : seg f 0 w.length=w := finiteSign_seg w
    rw [hf0]
    congr 1
    apply seg_A
    intro x hx hxT
    have he:=hAall (x-w.length)
    rwa [Nat.add_sub_cancel' hx] at he
  have hgword:=trimS_prefix f 0 h (w.length+T)
  change seg g 0 (h+(w.length+T))=List.replicate h false++seg f 0 (w.length+T) at hgword
  rw [hfword] at hgword
  have hwhole : seg g 0 (B+T)=List.replicate h false++(w++List.replicate T true) := by
    simpa only [B,Nat.add_assoc] using hgword
  have hAcount : cN (fun i=>g i=true) 0 (B+T)<h := by
    have ho:=ones_seg_eq_count g 0 (B+T)
    rw [hwhole,ones_append,ones_append,ones_replicate_S,ones_replicate_A,hone] at ho
    dsimp [h,T]
    omega
  have hS (i : Nat) (hi : i<h) : g i=false := by
    simp only [g,trimSSequence,if_pos hi]
  have hpos:=initial_S_positive g h (B+T) hS hAcount
  have hpre:=trimS_prefix f 0 h w.length
  change seg g 0 B=List.replicate h false++seg f 0 w.length at hpre
  rw [finiteSign_seg] at hpre
  have hAallg (i : Nat) : g (B+i)=true := by
    change trimSSequence f 0 h (B+i)=true
    rw [show B+i=h+(w.length+i) by dsimp [B]; omega,trimS_tail_sign,Nat.zero_add]
    exact hAall i
  have hlocal:=layer_supplies_clock (N+1) (N+1) (by omega)
  change Recaman.ThreeNonsuppliedData.localSupply (w++List.replicate T true)=true at hlocal
  have hlocalg : Recaman.ThreeNonsuppliedData.localSupply (seg g 0 (B+T))=true := by
    rw [hwhole]
    have he:=(ray_supply_append_iff (List.replicate h false) w T).mpr (Or.inr hlocal)
    simpa only [List.append_assoc] using he
  have htarget : EndN g 0 (B+T) :=
    (localSupply_seg_iff g 0 (B+T) (by omega) (hAallg T)).mp hlocalg
  have hlower:=layered_ray_count_unbounded (N+1)
  change N+1+1≤rayCount w (T+1) at hlower
  have hsucc:=cN_succ_le
    (fun i=>Recaman.ThreeNonsuppliedData.localSupply (w++List.replicate i true)=true) 0 T
  change rayCount w (T+1)≤rayCount w T+1 at hsucc
  have hretain:=actual_ray_retains_suffix g B T h w hpre (fun i _=>hAallg i)
  refine ⟨g,B,T,rfl,rfl,hpos,htarget,fun i _=>hAallg i,?_⟩
  omega

end Recaman.PaddedLayeredSupply
