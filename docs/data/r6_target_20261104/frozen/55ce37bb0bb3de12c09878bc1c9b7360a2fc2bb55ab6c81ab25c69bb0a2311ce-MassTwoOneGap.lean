import Recaman.MassTwoShortLastThree

namespace Recaman.MassTwoOneGap

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

theorem mass_two_one_gap (f : Nat → Bool) (n t h M m L s U v T j C : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w) (ht : t<n)
    (hh : 1≤h) (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hU : 1≤U)
    (hv : v=1) (hC2 : C=2)
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
 :
    j+1≤cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T) := by
  apply Classical.byContradiction
  intro hnot
  have hbad : cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)<j+1 := by omega
  have hb:=Recaman.MassTwoShortCounter.mass_two_short_counter f n t h M m L s U v T j C w hw hpre ht
    hh hM hm hL hs hU hv hC2 hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad
  let H:=h+M+m+L+s+U
  let z:=seg f n H
  let P:=fun x=>f x=true ∧ ¬EndN f 0 x
  have hword:=Recaman.SeparatorSupplyReset.three_run_word f n h M m L s U hS hA hS2 hA2 hS3 hA3
  have hSz : cntF z=h+m+s := by
    have hc:=mass_cntF z
    have hl:=seg_length f n H
    have hmz : mass z=0 := by
      dsimp [z,H]
      rw [hword]
      simp only [mass_append,mass_rep_false,mass_replicate_A]
      omega
    rw [hmz,hl] at hc
    dsimp [H] at hc
    omega
  have hS8 : 8≤h+m+s := by
    have hu : BlockWord (w.drop t):=block_suffix hw (w.take t) (w.drop t) (List.take_append_drop t w)
    have hl:=block_area_quadratic_lower hu
    have hlo : -2≤runKey (w.drop t) := by unfold runKey; omega
    have hz:=runKey_count_lower z
    rw [hSz] at hz
    simp only [Int.natCast_add] at hz
    have hk:=hb.2.2.2
    rw [hv,hC2] at hk
    change runKey (w.drop t)= -runKey z-4*2*((h : Int)+(m : Int)+(s : Int)+1)+2*1^2-2*((j : Int)+1)^2 at hk
    by_cases hs8 : 8≤h+m+s
    · exact hs8
    have hp:=Int.mul_nonneg (show 0≤(h : Int)+(m : Int)+(s : Int) by omega)
      (show 0≤7-((h : Int)+(m : Int)+(s : Int)) by omega)
    have hr:=Int.mul_nonneg (show 0≤(j : Int)+1-5 by have hh:=hb.2.1; omega)
      (show 0≤(j : Int)+1+5 by omega)
    have he : ((h : Int)+(m : Int)+(s : Int))*(7-((h : Int)+(m : Int)+(s : Int)))=
      7*((h : Int)+(m : Int)+(s : Int))-((h : Int)+(m : Int)+(s : Int))^2 := by grind only
    have her : ((j : Int)+1-5)*((j : Int)+1+5)=((j : Int)+1)^2-25 := by grind only
    omega
  have hAc : cN (fun x=>f x=true) n H=h+m+s := by
    have hx:=ones_seg_eq_count f n H
    dsimp [H] at hx
    rw [hword] at hx
    simp only [ones_append,ones_replicate_A,ones_replicate_S] at hx
    omega
  have hf4 : 4≤cN P n H := by
    by_cases hf : cN P n H≤3
    · have hpre0 : seg f 0 n=w++List.replicate 0 true := by simpa using hpre
      have hc:=positive_r3_additions_free_bound f n 0 H hw hpre0
        (fun k hk hkH=>hpos k hk (by dsimp [H] at hkH; omega)) hf
      rw [hAc] at hc
      omega
    · omega
  have hlast:=Recaman.MassTwoShortLastThree.short_counter_last_source_three f n t h M m L s U v T j C w hw hpre ht
    hh hM hm hL hs hU hv hC2 hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad
  have hc1:=cN_add P n H v
  have hc2:=cN_add P n (H+v) T
  have hp:=addition_endable_partition f (n+H+v) T
  rw [count_A_run f (n+H+v) T (by simpa only [H,Nat.add_assoc] using hA4)] at hp
  change T=cN (EndN f 0) (n+H+v) T+cN P (n+H+v) T at hp
  have hTj : T=j := by have ht:=hb.1; omega
  change cN P n (H+v+T)<j+1 at hbad
  simp only [H,Nat.add_assoc] at hc1 hc2 hp hf4 hlast hbad
  omega

end Recaman.MassTwoOneGap
