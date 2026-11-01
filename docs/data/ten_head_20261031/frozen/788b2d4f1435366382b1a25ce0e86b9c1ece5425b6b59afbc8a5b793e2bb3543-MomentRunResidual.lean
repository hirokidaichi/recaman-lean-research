import Recaman.MomentNoOld
import Recaman.FourRunSupplySeventeen

namespace Recaman.MomentRunResidual

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.MomentActualTarget Recaman.MomentNoOld Recaman.AdjacentRunSupply
open Recaman.FourRunSupplySeventeen Recaman.FourRunTargetArea

/-- A counterexample in the zero-mass moment-band three-run-head branch
has S<=16, free4..7, A<=23, j4..7, v<=3 and T<=9. All bounds are outputs
from the original actual history, not independent free or supply tags. -/
theorem moment_run_counter_residual (f : Nat → Bool) (n t h M m L s U v T j q i : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w) (ht : t<n)
    (hh : 1≤h) (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hU : 1≤U)
    (hzeroMass : M+L+U=h+m+s)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ k, k<M → f (n+h+k)=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → f x=false)
    (hA2 : ∀ k, k<L → f (n+h+M+m+k)=true)
    (hS3 : ∀ x, n+h+M+m+L≤x → x<n+h+M+m+L+s → f x=false)
    (hA3 : ∀ k, k<U → f (n+h+M+m+L+s+k)=true)
    (hS4 : ∀ x, n+h+M+m+L+s+U≤x → x<n+h+M+m+L+s+U+v → f x=false)
    (hA4 : ∀ k, k<T → f (n+h+M+m+L+s+U+v+k)=true)
    (B : Int) (haz : areaW (seg f n (h+M+m+L+s+U))= -B)
    (hlo : 4*((h+m+s : Nat) : Int)+6≤B) (hhi : B≤6*((h+m+s : Nat) : Int)+4)
    (hv : 1≤v) (hq : 1≤q) (hqv : q≤v) (hi : i<T) (hband : T≤i+j)
    (hgap : ∀ x, n+h+M+m+L+s+U+v+T≤x → x<n+h+M+m+L+s+U+v+T+j → f x=false)
    (htarget : Win f t (n+h+M+m+L+s+U+v+T+j-t))
    (hlocal : Win f (n+h+M+m+L+s+U+v-q) (q+i))
    (hpos : ∀ k, 0<k → k≤h+M+m+L+s+U+v+T →
      cN (EndN f 0) n k+1≤cN (fun x=>f x=false) n k)
    (hcounter : cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)<j+1) :
    h+m+s≤16 ∧ v≤3 ∧ 4≤j ∧ j≤7 ∧ T≤9 ∧ mass (w.drop t)≤2 ∧
      (w.drop t=[true] ∨ w.drop t=[true,true] ∨ w.drop t=[false,true,true,true]) ∧
      4≤cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T) ∧
      cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)≤7 ∧
      cN (fun x=>f x=true) n (h+M+m+L+s+U+v+T)≤23 := by
  let H:=h+M+m+L+s+U
  let S:=h+m+s
  let z:=seg f n H
  let P:=fun x=>f x=true ∧ ¬EndN f 0 x
  have hword:=four_run_word f n h M m L s U v T hS hA hS2 hA2 hS3 hA3 hS4 hA4
  have hhead:=Recaman.SeparatorSupplyReset.three_run_word f n h M m L s U hS hA hS2 hA2 hS3 hA3
  have hmz : mass z=0 := by
    simp only [z,H,hhead,mass_append,mass_rep_false,mass_replicate_A]
    omega
  have hSz : cntF z=S := by
    have hc:=mass_cntF z
    have hl : z.length=H := seg_length f n H
    rw [hmz,hl] at hc
    dsimp [H,S] at *
    omega
  have hsrc:=actual_final_S_source_A_budget f n t h M m L s U v T j q i w hw hpre ht
    hM hm hL hs hU hv hq hqv hi hband hword hS4 hA4 hgap htarget hlocal
  have hF4 : 4≤cN P n (H+v+T) := by
    by_cases hf : cN P n (H+v+T)≤3
    · have hpre0 : seg f 0 n=w++List.replicate 0 true := by simpa using hpre
      have hb:=positive_r3_additions_free_bound f n 0 (H+v+T) hw hpre0
        (by simpa only [H,Nat.add_assoc] using hpos) hf
      have hAbound : 2*(j+1)+2≤cN (fun x=>f x=true) n (H+v+T) := by
        simpa only [H,Nat.add_assoc] using hsrc.2.2
      change cN (fun x=>f x=true) n (H+v+T)≤2*cN P n (H+v+T)+1 at hb
      change cN P n (H+v+T)<j+1 at hcounter
      omega
    · omega
  have hR : 5≤j+1 := by change cN P n (H+v+T)<j+1 at hcounter; omega
  have hmass:=actual_moment_target_low_mass f n t H v T j q i w z hw hpre ht rfl hmz B haz
    (by rw [hSz]; exact hlo) (by rw [hSz]; exact hhi) hv hq hqv hi hband
    (by simpa only [H,Nat.add_assoc] using hS4)
    (by simpa only [H,Nat.add_assoc] using hA4)
    (by simpa only [H,Nat.add_assoc] using hgap)
    (by simpa only [H,Nat.add_assoc] using htarget)
    (by simpa only [H,Nat.add_assoc] using hlocal) hR
  have hno:=actual_moment_no_old f n H t v T j w z hw hpre ht rfl hmz B haz
    (by rw [hSz]; exact hlo) (by rw [hSz]; exact hhi) hv hmass.2.2.1 (by omega)
    (by simpa only [H,Nat.add_assoc] using hS4)
    (by simpa only [H,Nat.add_assoc] using hA4)
    (by simpa only [H,Nat.add_assoc] using hgap)
    (by simpa only [H,Nat.add_assoc] using htarget)
  have heq:=last_count_eq_local f n H v T z rfl
    (by simpa only [H,Nat.add_assoc] using hS4)
    (by simpa only [H,Nat.add_assoc] using hA4) hno
  have hlocal6:=fourth_ray_local_le_six h M m L s U v T hv
  have hElast : cN (EndN f 0) (n+H+v) T≤6 := by
    rw [heq]
    simpa only [z,H,hhead,List.append_assoc] using hlocal6
  have hEhead:=Recaman.InitialSTargetBounds.three_run_count_of_manyS f n h M m L s U w hw hpre hs
    (by omega) hS hA hS2 hA2 hS3 hA3 (fun k hk hkH=>hpos k hk (by omega))
  have hSzero : cN (EndN f 0) (n+H) v=0 := by
    apply cN_zero_of
    intro x hx hxv he
    have hf:=hS4 x (by dsimp [H] at *; omega) (by dsimp [H] at *; omega)
    have htrue:=he.1
    rw [hf] at htrue
    contradiction
  have h1:=cN_add (EndN f 0) n H v
  have h2:=cN_add (EndN f 0) n (H+v) T
  have hE16 : cN (EndN f 0) n (H+v+T)≤16 := by
    change cN (EndN f 0) n H≤10 at hEhead
    simp only [Nat.add_assoc] at *
    omega
  have hAcount : cN (fun x=>f x=true) n (H+v+T)=S+T := by
    have hc:=ones_seg_eq_count f n (H+v+T)
    change ones (seg f n (h+M+m+L+s+U+v+T))=_ at hc
    rw [hword] at hc
    simp only [ones_append,ones_replicate_A,ones_replicate_S] at hc
    dsimp [S]
    omega
  have hpart:=addition_endable_partition f n (H+v+T)
  rw [hAcount] at hpart
  change S+T=cN (EndN f 0) n (H+v+T)+cN P n (H+v+T) at hpart
  change cN P n (H+v+T)<j+1 at hcounter
  have hS16 : S≤16 := by
    have hb:=hmass.2.2.2.2.2
    omega
  have hj7 : j≤7 := by
    by_cases hj : j≤7
    · exact hj
    · have hp:=Int.mul_nonneg (show 0≤(j : Int)-8 by omega) (show 0≤(j : Int)+10 by omega)
      have hc:=hmass.2.2.2.2.1
      rw [hSz] at hc
      have hSc : (S : Int)≤16 := by omega
      grind only
  have hF7 : cN P n (H+v+T)≤7 := by omega
  have hA23 : cN (fun x=>f x=true) n (H+v+T)≤23 := by omega
  exact ⟨hS16,hmass.2.1,by omega,hj7,by omega,hmass.1,hmass.2.2.2.1,hF4,hF7,hA23⟩

end Recaman.MomentRunResidual
