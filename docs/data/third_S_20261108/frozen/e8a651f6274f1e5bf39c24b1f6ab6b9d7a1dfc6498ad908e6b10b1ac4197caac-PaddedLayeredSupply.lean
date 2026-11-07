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
      N+1≤cN (EndN f 0) B T ∧
      2≤cN (fun i=>f i=true ∧ ¬EndN f 0 i) 0 (B+T) := by
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
    dsimp [h,T] at ho ⊢
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
  have hfree2 : 2≤cN (fun i=>g i=true ∧ ¬EndN g 0 i) 0 (B+T) := by
    let M:=4*3^N
    have hpAll : ∀ k : Nat, 1≤3^k := by
      intro k
      induction k with
      | zero => decide
      | succ k ih => rw [Nat.pow_succ]; omega
    have hp:=hpAll N
    have hM4 : 4≤M := by dsimp [M]; omega
    have hMlen : M≤w.length := by
      change M≤(layered (N+1)).length
      rw [layered_length,Nat.pow_succ]
      dsimp [M]
      omega
    have hfirstA : ∀ i, i<M → g (h+i)=true := by
      intro i hi
      change trimSSequence f 0 h (h+i)=true
      rw [trimS_tail_sign,Nat.zero_add]
      have hil : i<w.length := by omega
      have htrue : w[i]?=some true := by
        change (List.replicate M true++(List.replicate (6*3^N) false++layered N))[i]?=some true
        rw [List.getElem?_append_left (by simpa only [List.length_replicate] using hi),
          List.getElem?_replicate,if_pos hi]
      have hget:=List.getElem?_eq_getElem hil
      change finiteSign w i=true
      rw [finiteSign,dif_pos hil]
      exact Option.some.inj (hget.symm.trans htrue)
    have hb:=single_A_run_free_budget g 0 h M [] BlockWord.nil rfl
      (by intro i hi hik; exact hS i (by omega)) (by simpa only [Nat.zero_add] using hfirstA)
    have hspl:=cN_add (fun i=>g i=true ∧ ¬EndN g 0 i) 0 h M
    have hmono:=count_prefix_le (fun i=>g i=true ∧ ¬EndN g 0 i) 0 (h+M) (B+T)
      (by dsimp [B]; omega)
    simp only [Nat.zero_add] at hb hspl
    omega
  refine ⟨g,B,T,rfl,rfl,hpos,htarget,fun i _=>hAallg i,?_,hfree2⟩
  omega

end Recaman.PaddedLayeredSupply
