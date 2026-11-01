import Recaman.NoOldTargetBounds

namespace Recaman.FourMassTargetCounter

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.MomentTargetProfile Recaman.ASourceReuse

/-- Counter parameters from the same mass-three target, independently of
whether old windows supply the last ray. All head lengths remain unbounded. -/
theorem four_mass_counter_parameters (f : Nat → Bool) (n t h M m L s U v T j : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w) (ht : t<n)
    (hh : 1≤h) (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hU : 1≤U)
    (hv : v=5)
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
    (hC : mass (w.drop t)=4)
    (hpos : ∀ k, 0<k → k≤h+M+m+L+s+U+v+T →
      cN (EndN f 0) n k+1≤cN (fun x=>f x=false) n k)
    (hbad : cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)<j+1) :
    T+3=v+j ∧ 5≤j+1 ∧ M≤j+2 ∧
      runKey (w.drop t)= -runKey (seg f n (h+M+m+L+s+U))-
        16*((h : Int)+(m : Int)+(s : Int)+(v : Int))+2*(v : Int)^2-2*((j : Int)+1)^2 := by
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
  have hprof:=actual_target_word_profile f n t H v T j w z hpre ht rfl
    (by simpa only [H,Nat.add_assoc] using hS4)
    (by simpa only [H,Nat.add_assoc] using hA4)
    (by simpa only [H,Nat.add_assoc] using hgap)
    (by simpa only [H,Nat.add_assoc] using htarget)
  have hT : T+3=v+j := by
    have hm:=hprof.1
    simp only [mass_append,mass_rep_false,mass_replicate_A,hmz,hC] at hm
    omega
  let B : Int:= -areaW z
  have hB : runKey z= -2*B := by
    unfold runKey
    rw [hmz]
    dsimp [B]
    grind only
  have hkt:=actual_zero_mass_target_key f n t H v T j w z hpre ht rfl hmz B
    (by dsimp [B]; omega)
    (by simpa only [H,Nat.add_assoc] using hS4)
    (by simpa only [H,Nat.add_assoc] using hA4)
    (by simpa only [H,Nat.add_assoc] using hgap)
    (by simpa only [H,Nat.add_assoc] using htarget)
  rw [hC,hSz] at hkt
  have hkey : runKey (w.drop t)= -runKey z-16*((h : Int)+(m : Int)+(s : Int)+(v : Int))+2*(v : Int)^2-
      2*((j : Int)+1)^2 := by grind only
  have hu : BlockWord (w.drop t) :=
    block_suffix hw (w.take t) (w.drop t) (List.take_append_drop t w)
  have hRS : j+1+1≤cntF z := by
    have hlo : -2≤runKey (w.drop t) := by
      have hb:=block_area_quadratic_lower hu
      unfold runKey
      omega
    have hlz:=runKey_count_lower z
    by_cases hh : j+1+1≤cntF z
    · exact hh
    · have hp:=Int.mul_nonneg (show 0≤(j : Int)+1-(cntF z : Int) by omega)
        (show 0≤(j : Int)+1+(cntF z : Int) by omega)
      have hS0 : 0≤(cntF z : Int) := by omega
      rw [hSz] at hlz hp hS0
      subst v
      grind only
  have hword : seg f n (H+v+T)=z++List.replicate v false++List.replicate T true := by
    rw [seg_add,seg_add]
    rw [show seg f n H=z by rfl,seg_false f (n+H) v (by simpa only [H,Nat.add_assoc] using hS4)]
    have hAt : seg f (n+(H+v)) T=List.replicate T true := by
      apply seg_A
      intro x hx hxT
      have ha:=hA4 (x-(n+H+v)) (by omega)
      rw [show n+h+M+m+L+s+U+v+(x-(n+H+v))=x by dsimp [H]; omega] at ha
      exact ha
    rw [hAt]
  have hAc : cN (fun x=>f x=true) n (H+v+T)=h+m+s+T := by
    have hc:=ones_seg_eq_count f n (H+v+T)
    rw [hword] at hc
    have hone : ones z=(h+m+s : Nat) := by
      have hc:=mass_cntF z
      have hm:=mass_eq z
      rw [hmz,hSz] at hc
      rw [hmz] at hm
      omega
    simp only [ones_append,ones_replicate_S,ones_replicate_A,hone] at hc
    omega
  have hvpos : 3≤v := by omega
  have hR : 5≤j+1 := by
    by_cases hf : cN P n (H+v+T)≤3
    · have hpre0 : seg f 0 n=w++List.replicate 0 true := by simpa using hpre
      have hb:=positive_r3_additions_free_bound f n 0 (H+v+T) hw hpre0
        (by simpa only [H,Nat.add_assoc] using hpos) hf
      change cN (fun x=>f x=true) n (H+v+T)≤2*cN P n (H+v+T)+1 at hb
      rw [hAc] at hb
      rw [hSz] at hRS
      change cN P n (H+v+T)<j+1 at hbad
      omega
    · change cN P n (H+v+T)<j+1 at hbad
      omega
  have hbudget : M≤j+2 := by
    have hpreA : seg f 0 (n+h)=w++List.replicate h false := by
      rw [seg_add,Nat.zero_add,hpre,seg_false f n h hS]
    have hE:=endable_A_run_count f (n+h) M (w++List.replicate h false) hpreA hA
    have hE2:=block_rayCount_after_S hw h M
    have hpartA:=addition_endable_partition f (n+h) M
    rw [count_A_run f (n+h) M hA] at hpartA
    have h1:=cN_add P n h M
    have h2:=cN_add P n (h+M) (m+L+s+U+v+T)
    change cN P n (H+v+T)<j+1 at hbad
    change M=cN (EndN f 0) (n+h) M+cN P (n+h) M at hpartA
    dsimp only [H] at hbad
    simp only [Nat.add_assoc] at h1 h2 hpartA hE hbad
    omega
  exact ⟨hT,hR,hbudget,hkey⟩

end Recaman.FourMassTargetCounter
