import Recaman.NoOldTargetBounds

namespace Recaman.OffsetTargetCounter

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.MomentTargetProfile Recaman.ASourceReuse

theorem offset_two_counter (f : Nat → Bool) (n t h M m L s U v T j C : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w) (ht : t<n)
    (hh : 1≤h) (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hU : 1≤U)
    (hv : v=C+2) (hC4 : 4≤C)
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
    (hC : mass (w.drop t)=(C : Int))
    (hpos : ∀ k, 0<k → k≤h+M+m+L+s+U+v+T →
      cN (EndN f 0) n k+1≤cN (fun x=>f x=false) n k)
    (hbad : cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)<j+1) :
    T=j+3 ∧ 5≤j+1 ∧
      runKey (w.drop t)≤ -runKey (seg f n (h+M+m+L+s+U))-
        12*((h : Int)+(m : Int)+(s : Int))-10-2*((j : Int)+1)^2 := by
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
  have hT : T=j+3 := by
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
  have hkey : runKey (w.drop t)≤ -runKey z-12*((h : Int)+(m : Int)+(s : Int))-10-
      2*((j : Int)+1)^2 := by
    have hprod:=Int.mul_nonneg (show 0≤(C : Int)-3 by omega)
      (show 0≤(C : Int)+3+2*((h : Int)+(m : Int)+(s : Int)) by omega)
    have hcv : (v : Int)=(C : Int)+2 := by omega
    grind only
  have hu : BlockWord (w.drop t) :=
    block_suffix hw (w.take t) (w.drop t) (List.take_append_drop t w)
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
  have hR : 5≤j+1 := by
    by_cases hR5 : 5≤j+1
    · exact hR5
    · have hf : cN P n (H+v+T)≤3 := by
        change cN P n (H+v+T)<j+1 at hbad
        omega
      have hpre0 : seg f 0 n=w++List.replicate 0 true := by simpa using hpre
      have hb:=positive_r3_additions_free_bound f n 0 (H+v+T) hw hpre0
        (by simpa only [H,Nat.add_assoc] using hpos) hf
      change cN (fun x=>f x=true) n (H+v+T)≤2*cN P n (H+v+T)+1 at hb
      rw [hAc] at hb
      change cN P n (H+v+T)<j+1 at hbad
      omega
  exact ⟨hT,hR,hkey⟩

end Recaman.OffsetTargetCounter
