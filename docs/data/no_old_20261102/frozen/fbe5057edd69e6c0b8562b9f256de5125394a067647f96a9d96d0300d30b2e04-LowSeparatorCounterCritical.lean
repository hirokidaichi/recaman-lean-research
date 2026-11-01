import Recaman.LowSeparatorTargetCounter
import Recaman.LowSeparatorLocalBudget

namespace Recaman.LowSeparatorCounterCritical

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

private theorem low_target_head_ten (u z : List Bool) (hu : BlockWord u)
    (v R : Nat) (hv : v=1 ∨ v=2) (hR : 5≤R)
    (hkey : runKey u= -runKey z-12*((cntF z : Int)+(v : Int))+2*(v : Int)^2-2*(R : Int)^2) :
    10≤cntF z := by
  have hlo : -2≤runKey u := by
    have hb:=block_area_quadratic_lower hu
    unfold runKey
    omega
  have hlowz:=runKey_count_lower z
  by_cases hh : 10≤cntF z
  · exact hh
  · have hp:=Int.mul_nonneg (show 0≤9-(cntF z : Int) by omega)
      (show 0≤(cntF z : Int)+3 by omega)
    have hRR:=Int.mul_nonneg (show 0≤(R : Int)-5 by omega)
      (show 0≤(R : Int)+5 by omega)
    rcases hv with rfl|rfl <;> grind only

/-- A hypothetical S1/S2 counter is forced onto one critical boundary:
headfree4, fullfree=j and a saturated last local budget3/4. No absence
claim is made here. Every original old source is internally excluded. -/
theorem low_separator_counter_critical (f : Nat → Bool) (n t h M m L s U v T j : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w) (ht : t<n)
    (hh : 1≤h) (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hU : 1≤U)
    (hv : v=1 ∨ v=2)
    (hzeroMass : M+L+U=h+m+s)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ k, k<M → f (n+h+k)=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → f x=false)
    (hA2 : ∀ k, k<L → f (n+h+M+m+k)=true)
    (hS3 : ∀ x, n+h+M+m+L≤x → x<n+h+M+m+L+s → f x=false)
    (hA3 : ∀ k, k<U → f (n+h+M+m+L+s+k)=true)
    (hS4 : ∀ x, n+h+M+m+L+s+U≤x → x<n+h+M+m+L+s+U+v → f x=false)
    (hA4 : ∀ k, k<T → f (n+h+M+m+L+s+U+v+k)=true)
    (hgap : ∀ x, n+h+M+m+L+s+U+v+T≤x → x<n+h+M+m+L+s+U+v+T+j → f x=false)
    (htarget : Win f t (n+h+M+m+L+s+U+v+T+j-t))
    (hC : mass (w.drop t)=3)
    (hpos : ∀ k, 0<k → k≤h+M+m+L+s+U+v+T →
      cN (EndN f 0) n k+1≤cN (fun x=>f x=false) n k)
    (hbad : cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)<j+1) :
    (∀ k, k<T → ∀ r, r<n → ¬Win f r (n+h+M+m+L+s+U+v+k-r)) ∧
    cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U)=4 ∧
    cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)=j ∧
    cN (EndN f 0) (n+h+M+m+L+s+U+v) T=v+2 ∧
    10≤h+m+s ∧ h+m+s≤14 ∧ 5≤j+1 ∧ T+2=v+j := by
  have hb:=Recaman.LowSeparatorTargetCounter.low_separator_counter_parameters f n t h M m L s U v T j w hw hpre ht
    hh hM hm hL hs hU hv hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad
  let H:=h+M+m+L+s+U
  let z:=seg f n H
  let P:=fun x=>f x=true ∧ ¬EndN f 0 x
  have hhead:=Recaman.SeparatorSupplyReset.three_run_word f n h M m L s U hS hA hS2 hA2 hS3 hA3
  have hmz : mass z=0 := by
    simp only [z,H,hhead,mass_append,mass_rep_false,mass_replicate_A]
    omega
  have hSz : cntF z=h+m+s := by
    have hc:=mass_cntF z
    have hl : z.length=H := seg_length f n H
    rw [hmz,hl] at hc
    dsimp [H] at hc
    omega
  let B : Int:= -areaW z
  have hB : runKey z= -2*B := by
    unfold runKey
    rw [hmz]
    dsimp [B]
    grind only
  have hu : BlockWord (w.drop t) :=
    block_suffix hw (w.take t) (w.drop t) (List.take_append_drop t w)
  have hkey : runKey (w.drop t)= -runKey z-12*((h : Int)+(m : Int)+(s : Int)+(v : Int))+2*(v : Int)^2-2*((j : Int)+1)^2 := hb.2.2.2
  have hkeyB : runKey (w.drop t)=2*B-12*((h : Int)+(m : Int)+(s : Int)+(v : Int))+2*(v : Int)^2-2*((j : Int)+1)^2 := by
    rw [hB] at hkey
    omega
  have hno : ∀ k, k<T → ∀ r, r<n → ¬Win f r (n+H+v+k-r) := by
    intro k hk r hr hwin
    have hw' : BlockWord (seg f 0 n) := by rw [hpre]; exact hw
    have ho:=Recaman.OldSourceKeyOrder.actual_old_target_prior_clock f n r t (H+v) k T j hw' hr ht
      (by omega) (by have hR:=hb.2.1; omega)
      (by simpa only [H,Nat.add_assoc] using hA4)
      (by simpa only [H,Nat.add_assoc] using hgap) hwin
      (by simpa only [H,Nat.add_assoc] using htarget)
    have hT:=hb.1
    have hv2 : v≤2 := by omega
    omega
  have hraw:=Recaman.LowSeparatorLocalBudget.low_separator_local_budget (w.drop t) hu hC h M m L s U v (j+1) T
    hv (by have hR:=hb.2.1; omega) hzeroMass hs (by have hm:=hb.2.2.1; omega) B
    (by rw [←hhead]; exact hB)
    (by simpa only [Int.natCast_add,Int.natCast_one] using hkeyB)
  have heq:=Recaman.MomentNoOld.last_count_eq_local f n H v T z rfl
    (by simpa only [H,Nat.add_assoc] using hS4)
    (by simpa only [H,Nat.add_assoc] using hA4) hno
  have hlast : cN (EndN f 0) (n+H+v) T≤v+2 := by
    rw [heq]
    simpa only [z,H,hhead,List.append_assoc] using hraw
  have hS10:=low_target_head_ten (w.drop t) z hu v (j+1) hv hb.2.1
    (by rw [hSz]; simpa only [Int.natCast_add,Int.natCast_one] using hkey)
  rw [hSz] at hS10
  have hAh:=ones_seg_eq_count f n H
  change ones (seg f n (h+M+m+L+s+U))=_ at hAh
  rw [hhead] at hAh
  simp only [ones_append,ones_replicate_A,ones_replicate_S] at hAh
  have hfhead : 4≤cN P n H := by
    by_cases hf : cN P n H≤3
    · have hpre0 : seg f 0 n=w++List.replicate 0 true := by simpa using hpre
      have hc:=positive_r3_additions_free_bound f n 0 H hw hpre0
        (fun k hk hkH=>hpos k hk (by dsimp [H] at hkH; omega)) hf
      change cN (fun x=>f x=true) n H≤2*cN P n H+1 at hc
      omega
    · omega
  have hsep : cN P (n+H) v=0 := by
    apply cN_zero_of
    intro x hx hxv hp
    have hf:=hS4 x (by dsimp [H] at hx; omega) (by dsimp [H] at hxv; omega)
    change f x=true ∧ ¬EndN f 0 x at hp
    rw [hf] at hp
    simp at hp
  have hf1:=cN_add P n H v
  have hf2:=cN_add P n (H+v) T
  have hp:=addition_endable_partition f (n+H+v) T
  rw [count_A_run f (n+H+v) T (by simpa only [H,Nat.add_assoc] using hA4)] at hp
  change T=cN (EndN f 0) (n+H+v) T+cN P (n+H+v) T at hp
  have hT:=hb.1
  change cN P n (H+v+T)<j+1 at hbad
  simp only [Nat.add_assoc] at hf1 hf2 hp hlast hbad
  have hfh : cN P n H=4 := by omega
  have hfull : cN P n (H+v+T)=j := by
    simp only [Nat.add_assoc]
    omega
  have helast : cN (EndN f 0) (n+H+v) T=v+2 := by
    simp only [Nat.add_assoc]
    omega
  have hhead10:=Recaman.InitialSTargetBounds.three_run_count_of_manyS f n h M m L s U w hw hpre hs
    (by omega) hS hA hS2 hA2 hS3 hA3 (fun k hk hkH=>hpos k hk (by omega))
  have hph:=addition_endable_partition f n H
  change cN (fun x=>f x=true) n H=cN (EndN f 0) n H+cN P n H at hph
  have hS14 : h+m+s≤14 := by
    change cN (EndN f 0) n H≤10 at hhead10
    omega
  exact ⟨by simpa only [H,Nat.add_assoc] using hno,hfh,hfull,by simpa only [H,Nat.add_assoc] using helast,
    hS10,hS14,hb.2.1,hT⟩

end Recaman.LowSeparatorCounterCritical
