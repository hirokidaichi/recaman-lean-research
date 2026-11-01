import Recaman.MomentFinalSGap
import Recaman.LowerMomentBoundary

namespace Recaman.LowerMomentFreeGap

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.MomentActualTarget Recaman.MomentNoOld Recaman.MomentMassTwoParameters
open Recaman.MomentMassTwoLocal Recaman.MomentMassTwoThreeGap

open Recaman.MomentRunResidual Recaman.FourRunSupplySeventeen Recaman.FourRunTargetArea
open Recaman.LowerMomentBoundary Recaman.LowerMomentOldClock Recaman.MomentMassOneGap

theorem lower_moment_final_S_free_gap (f : Nat → Bool) (n t h M m L s U v T j q i : Nat)
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
    (hlo : 4*((h+m+s : Nat) : Int)+5≤B) (hhi : B≤6*((h+m+s : Nat) : Int)+4)
    (hv : 1≤v) (hq : 1≤q) (hqv : q≤v) (hi : i<T) (hband : T≤i+j)
    (hgap : ∀ x, n+h+M+m+L+s+U+v+T≤x → x<n+h+M+m+L+s+U+v+T+j → f x=false)
    (htarget : Win f t (n+h+M+m+L+s+U+v+T+j-t))
    (hlocal : Win f (n+h+M+m+L+s+U+v-q) (q+i))
    (hpos : ∀ k, 0<k → k≤h+M+m+L+s+U+v+T →
      cN (EndN f 0) n k+1≤cN (fun x=>f x=false) n k)
 :
    j+1≤cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T) := by
  by_cases hstrong : 4*((h+m+s : Nat) : Int)+6≤B
  · exact Recaman.MomentFinalSGap.moment_final_S_free_gap f n t h M m L s U v T j q i w hw hpre ht hh hM hm hL hs hU hzeroMass
      hS hA hS2 hA2 hS3 hA3 hS4 hA4 B haz hstrong hhi hv hq hqv hi hband hgap htarget hlocal hpos
  have hB : B=4*((h+m+s : Nat) : Int)+5 := by omega
  by_cases hgood : j+1≤cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)
  · exact hgood
  have hcounter : cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)<j+1 := by omega
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

  have hprof:=Recaman.MomentTargetProfile.actual_target_word_profile f n t H v T j w z hpre ht rfl
    (by simpa only [H,Nat.add_assoc] using hS4)
    (by simpa only [H,Nat.add_assoc] using hA4)
    (by simpa only [H,Nat.add_assoc] using hgap)
    (by simpa only [H,Nat.add_assoc] using htarget)
  have hu : BlockWord (w.drop t) := block_suffix hw (w.take t) (w.drop t) (List.take_append_drop t w)
  have hne : w.drop t≠[] := by
    have hn : w.length=n := by rw [←hpre,seg_length]
    intro he
    have hl : (w.drop t).length=w.length-t := List.length_drop
    rw [he] at hl
    simp only [List.length_nil] at hl
    omega
  have hc:=lower_boundary_target (w.drop t) z hu hne hmz B haz (by rw [hSz]; exact hB)
    v T j hv hR (by have hi2:=hsrc.2.1; omega) hprof.1 hprof.2
  have hv1 : v=1 := hc.2.1
  have hS8 : 8≤h+m+s := by have hh:=hc.2.2.2; rw [hSz] at hh; exact Nat.le_trans (by decide) hh
  have hno:=actual_lower_band_no_old f n H t v T j w z hw hpre ht rfl hmz B haz
    (by rw [hSz]; exact hlo) (by rw [hSz]; exact hhi) hv (by omega) (by omega)
    (by simpa only [H,Nat.add_assoc] using hS4)
    (by simpa only [H,Nat.add_assoc] using hA4)
    (by simpa only [H,Nat.add_assoc] using hgap)
    (by simpa only [H,Nat.add_assoc] using htarget)
  have heq:=last_count_eq_local f n H v T z rfl
    (by simpa only [H,Nat.add_assoc] using hS4)
    (by simpa only [H,Nat.add_assoc] using hA4) hno
  have hlocalbound : rayCount (z++List.replicate v false) T≤v+3 := by
    have hb:=lower_short_gap_local_budget h M m L s U v T hs
      (by rw [←hhead]; exact hmz) B
      (by rw [←hhead]; exact haz)
      (by rw [←hhead]; change 3≤cntF z; rw [hSz]; dsimp [S]; omega)
      (by rw [←hhead]; change 4*(cntF z : Int)+4≤B; rw [hSz]; omega)
      (by rw [←hhead]; change B≤6*(cntF z : Int)+4; rw [hSz]; exact hhi) (Or.inl hv1)
    simpa only [z,H,hhead,List.append_assoc] using hb
  have hlast : cN (EndN f 0) (n+H+v) T≤v+3 := by rw [heq]; exact hlocalbound
  have hAcount : cN (fun x=>f x=true) n H=S := by
    have ha:=ones_seg_eq_count f n H
    change ones (seg f n (h+M+m+L+s+U))=_ at ha
    rw [hhead] at ha
    simp only [ones_append,ones_replicate_A,ones_replicate_S] at ha
    dsimp [S]
    omega
  have hF4 : 4≤cN P n H := by
    by_cases hf : cN P n H≤3
    · have hpre0 : seg f 0 n=w++List.replicate 0 true := by simpa using hpre
      have hb:=positive_r3_additions_free_bound f n 0 H hw hpre0
        (fun k hk hkH=>hpos k hk (by dsimp [H] at *; omega)) hf
      change cN (fun x=>f x=true) n H≤2*cN P n H+1 at hb
      rw [hAcount] at hb
      dsimp [S] at hb
      omega
    · omega
  have hgapfree:=actual_short_gap_charge f n H v T j hF4 hlast (by have he:=hc.2.2.1; omega)
    (by simpa only [H,Nat.add_assoc] using hS4)
    (by simpa only [H,Nat.add_assoc] using hA4)
  exact hgapfree

end Recaman.LowerMomentFreeGap
