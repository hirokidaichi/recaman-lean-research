import Recaman.NoOldInitialSource
import Recaman.MomentNoOld
import Recaman.InitialSTargetBounds

namespace Recaman.NoOldTargetBounds

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.MomentTargetProfile Recaman.ASourceReuse

/-- The same primitive target forces a head longer than the gap parameter.
No endpoint-A premise or unrelated old-source cutoff is used. -/
theorem target_head_S_bound (u z : List Bool) (hu : BlockWord u) (R : Nat)
    (hkey : runKey u= -runKey z-12*(cntF z : Int)-18-2*(R : Int)^2) :
    R+1≤cntF z := by
  have hlo : -2≤runKey u := by
    have hb:=block_area_quadratic_lower hu
    unfold runKey
    omega
  have hlowz:=runKey_count_lower z
  by_cases hh : R+1≤cntF z
  · exact hh
  · have hp:=Int.mul_nonneg (show 0≤(R : Int)-(cntF z : Int) by omega)
      (show 0≤(R : Int)+(cntF z : Int) by omega)
    have hS0 : 0≤(cntF z : Int) := by omega
    grind only

/-- Under an actual counter, the no-old branch supplies its own bounds
R>=5, head S<=15, first-A budget and same-target key. They are conclusions,
not independent inputs or an assumed free-count proposition. -/
theorem no_old_counter_bounds (f : Nat → Bool) (n t h M m L s U T j : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w) (ht : t<n)
    (hh : 1≤h) (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hU : 1≤U)
    (hzeroMass : M+L+U=h+m+s)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ k, k<M → f (n+h+k)=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → f x=false)
    (hA2 : ∀ k, k<L → f (n+h+M+m+k)=true)
    (hS3 : ∀ x, n+h+M+m+L≤x → x<n+h+M+m+L+s → f x=false)
    (hA3 : ∀ k, k<U → f (n+h+M+m+L+s+k)=true)
    (hS4 : ∀ x, n+h+M+m+L+s+U≤x → x<n+h+M+m+L+s+U+3 → f x=false)
    (hA4 : ∀ k, k<T → f (n+h+M+m+L+s+U+3+k)=true)
    (hgap : ∀ x, n+h+M+m+L+s+U+3+T≤x → x<n+h+M+m+L+s+U+3+T+j → f x=false)
    (htarget : Win f t (n+h+M+m+L+s+U+3+T+j-t))
    (hC : mass (w.drop t)=3)
    (hno : ∀ k, k<T → ∀ r, r<n → ¬Win f r (n+h+M+m+L+s+U+3+k-r))
    (hpos : ∀ k, 0<k → k≤h+M+m+L+s+U+3+T →
      cN (EndN f 0) n k+1≤cN (fun x=>f x=false) n k)
    (hbad : cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+3+T)<j+1) :
    T=j+1 ∧ 5≤j+1 ∧ h+m+s≤15 ∧ M≤j+2 ∧
      runKey (w.drop t)= -runKey (seg f n (h+M+m+L+s+U))-
        12*((h : Int)+(m : Int)+(s : Int))-18-2*((j : Int)+1)^2 := by
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
  have hprof:=actual_target_word_profile f n t H 3 T j w z hpre ht rfl
    (by simpa only [H,Nat.add_assoc] using hS4)
    (by simpa only [H,Nat.add_assoc] using hA4)
    (by simpa only [H,Nat.add_assoc] using hgap)
    (by simpa only [H,Nat.add_assoc] using htarget)
  have hT : T=j+1 := by
    have hm:=hprof.1
    simp only [mass_append,mass_rep_false,mass_replicate_A,hmz,hC] at hm
    omega
  let B : Int:= -areaW z
  have hB : runKey z= -2*B := by
    unfold runKey
    rw [hmz]
    dsimp [B]
    grind only
  have hkt:=actual_zero_mass_target_key f n t H 3 T j w z hpre ht rfl hmz B
    (by dsimp [B]; omega)
    (by simpa only [H,Nat.add_assoc] using hS4)
    (by simpa only [H,Nat.add_assoc] using hA4)
    (by simpa only [H,Nat.add_assoc] using hgap)
    (by simpa only [H,Nat.add_assoc] using htarget)
  rw [hC,hSz] at hkt
  have hkey : runKey (w.drop t)= -runKey z-12*((h : Int)+(m : Int)+(s : Int))-18-
      2*((j : Int)+1)^2 := by grind only
  have hu : BlockWord (w.drop t) :=
    block_suffix hw (w.take t) (w.drop t) (List.take_append_drop t w)
  have hRS:=target_head_S_bound (w.drop t) z hu (j+1)
    (by rw [hSz]; simpa only [Int.natCast_add,Int.natCast_one] using hkey)
  have hword : seg f n (H+3+T)=z++List.replicate 3 false++List.replicate T true := by
    rw [seg_add,seg_add]
    rw [show seg f n H=z by rfl,seg_false f (n+H) 3 (by simpa only [H,Nat.add_assoc] using hS4)]
    have hAt : seg f (n+(H+3)) T=List.replicate T true := by
      apply seg_A
      intro x hx hxT
      have ha:=hA4 (x-(n+H+3)) (by omega)
      rw [show n+h+M+m+L+s+U+3+(x-(n+H+3))=x by dsimp [H]; omega] at ha
      exact ha
    rw [hAt]
  have hAc : cN (fun x=>f x=true) n (H+3+T)=h+m+s+T := by
    have hc:=ones_seg_eq_count f n (H+3+T)
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
    by_cases hf : cN P n (H+3+T)≤3
    · have hpre0 : seg f 0 n=w++List.replicate 0 true := by simpa using hpre
      have hb:=positive_r3_additions_free_bound f n 0 (H+3+T) hw hpre0
        (by simpa only [H,Nat.add_assoc] using hpos) hf
      change cN (fun x=>f x=true) n (H+3+T)≤2*cN P n (H+3+T)+1 at hb
      rw [hAc] at hb
      rw [hSz] at hRS
      change cN P n (H+3+T)<j+1 at hbad
      omega
    · change cN P n (H+3+T)<j+1 at hbad
      omega
  have hlastEq:=Recaman.MomentNoOld.last_count_eq_local f n H 3 T z rfl
    (by simpa only [H,Nat.add_assoc] using hS4)
    (by simpa only [H,Nat.add_assoc] using hA4)
    (by simpa only [H,Nat.add_assoc] using hno)
  have hlocal6:=Recaman.AdjacentRunSupply.fourth_ray_local_le_six h M m L s U 3 T (by decide)
  have hlast : cN (EndN f 0) (n+H+3) T≤6 := by
    rw [hlastEq]
    simpa only [z,H,hhead,List.append_assoc] using hlocal6
  have hhead10:=Recaman.InitialSTargetBounds.three_run_count_of_manyS f n h M m L s U w hw hpre hs
    (by omega) hS hA hS2 hA2 hS3 hA3 (fun k hk hkH=>hpos k hk (by omega))
  have hsep : cN (EndN f 0) (n+H) 3=0 := by
    apply cN_zero_of
    intro x hx hxe he
    have hf:=hS4 x (by dsimp [H] at hx; omega) (by dsimp [H] at hxe; omega)
    have ht:=he.1
    rw [hf] at ht
    contradiction
  have he1:=cN_add (EndN f 0) n H 3
  have he2:=cN_add (EndN f 0) n (H+3) T
  have hpart:=addition_endable_partition f n (H+3+T)
  rw [hAc] at hpart
  change h+m+s+T=cN (EndN f 0) n (H+3+T)+cN P n (H+3+T) at hpart
  have hS15 : h+m+s≤15 := by
    change cN (EndN f 0) n H≤10 at hhead10
    change cN P n (H+3+T)<j+1 at hbad
    simp only [Nat.add_assoc] at he1 he2 hlast hpart hbad
    omega
  have hbudget : M≤j+2 := by
    have hpreA : seg f 0 (n+h)=w++List.replicate h false := by
      rw [seg_add,Nat.zero_add,hpre,seg_false f n h hS]
    have hE:=endable_A_run_count f (n+h) M (w++List.replicate h false) hpreA hA
    have hE2:=block_rayCount_after_S hw h M
    have hpartA:=addition_endable_partition f (n+h) M
    rw [count_A_run f (n+h) M hA] at hpartA
    have h1:=cN_add P n h M
    have h2:=cN_add P n (h+M) (m+L+s+U+3+T)
    change cN P n (H+3+T)<j+1 at hbad
    change M=cN (EndN f 0) (n+h) M+cN P (n+h) M at hpartA
    dsimp only [H] at hbad
    simp only [Nat.add_assoc] at h1 h2 hpartA hE hbad
    omega
  exact ⟨hT,hR,hS15,hbudget,hkey⟩

end Recaman.NoOldTargetBounds
