import Recaman.LowerMomentFreeGap
import Recaman.LowerMomentBoundary

namespace Recaman.LowerFourFreeGap

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.MomentActualTarget Recaman.MomentNoOld Recaman.MomentMassTwoParameters
open Recaman.MomentMassTwoLocal Recaman.MomentMassTwoThreeGap

open Recaman.MomentRunResidual Recaman.FourRunSupplySeventeen Recaman.FourRunTargetArea
open Recaman.LowerMomentBoundary Recaman.LowerMomentOldClock Recaman.MomentMassOneGap

theorem lower_four_final_S_free_gap (f : Nat → Bool) (n t h M m L s U v T j q i : Nat)
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
    (hlo : 4*((h+m+s : Nat) : Int)+4≤B) (hhi : B≤6*((h+m+s : Nat) : Int)+4)
    (hv : 1≤v) (hq : 1≤q) (hqv : q≤v) (hi : i<T) (hband : T≤i+j)
    (hgap : ∀ x, n+h+M+m+L+s+U+v+T≤x → x<n+h+M+m+L+s+U+v+T+j → f x=false)
    (htarget : Win f t (n+h+M+m+L+s+U+v+T+j-t))
    (hlocal : Win f (n+h+M+m+L+s+U+v-q) (q+i))
    (hpos : ∀ k, 0<k → k≤h+M+m+L+s+U+v+T →
      cN (EndN f 0) n k+1≤cN (fun x=>f x=false) n k)
 :
    j+1≤cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T) := by
  by_cases hstrong : 4*((h+m+s : Nat) : Int)+5≤B
  · exact Recaman.LowerMomentFreeGap.lower_moment_final_S_free_gap f n t h M m L s U v T j q i w hw hpre ht hh hM hm hL hs hU hzeroMass
      hS hA hS2 hA2 hS3 hA3 hS4 hA4 B haz hstrong hhi hv hq hqv hi hband hgap htarget hlocal hpos
  have hB : B=4*((h+m+s : Nat) : Int)+4 := by omega
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
  have hEhead:=Recaman.InitialSTargetBounds.three_run_count_of_manyS f n h M m L s U w hw hpre hs
    (by omega) hS hA hS2 hA2 hS3 hA3 (fun k hk hkH=>hpos k hk (by dsimp [H]; omega))
  have hF6 : 6≤cN P n H := by
    have hp:=addition_endable_partition f n H
    rw [hAcount] at hp
    change S=cN (EndN f 0) n H+cN P n H at hp
    change cN (EndN f 0) n H≤10 at hEhead
    have hh:=hc.2.2.2
    rw [hSz] at hh
    omega
  have hSzero : cN P (n+H) v=0 := by
    apply cN_zero_of
    intro x hx hxv hp
    have hf:=hS4 x (by dsimp [H] at *; omega) (by dsimp [H] at *; omega)
    change f x=true ∧ ¬EndN f 0 x at hp
    rw [hf] at hp
    simp at hp
  have h1:=cN_add P n H v
  have h2:=cN_add P n (H+v) T
  have hpart:=addition_endable_partition f (n+H+v) T
  rw [count_A_run f (n+H+v) T (by simpa only [H,Nat.add_assoc] using hA4)] at hpart
  change T=cN (EndN f 0) (n+H+v) T+cN P (n+H+v) T at hpart
  have hT:=hc.2.2.1
  change j+1≤cN P n (H+v+T)
  simp only [Nat.add_assoc] at *
  omega

end Recaman.LowerFourFreeGap
