import Recaman.FourMeasuredCounts
import Recaman.MixedShortAPairBudget

namespace Recaman.ShortEarlyHeadBudget

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.AdjacentRunSupply

theorem actual_short_head_budget (f : Nat → Bool) (n h M m L s U : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w)
    (hM : 1≤M) (hL : 1≤L) (hhM : M≤8) (hhL : L≤8) (hm : 1≤m) (hs : 1≤s)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ i, i<M → f (n+h+i)=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → f x=false)
    (hA2 : ∀ i, i<L → f (n+h+M+m+i)=true)
    (hS3 : ∀ x, n+h+M+m+L≤x → x<n+h+M+m+L+s → f x=false)
    (hA3 : ∀ i, i<U → f (n+h+M+m+L+s+i)=true)
    (hpos : ∀ k, 0<k → k≤h+M+m+L+s+U →
      cN (EndN f 0) n k+1≤cN (fun x=>f x=false) n k) :
    cN (EndN f 0) n (h+M+m+L+s+U)≤M+L+3 := by
  let C:=h+M+m+L+s
  let y:=List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false
  have hh : 1≤h := by
    by_cases he : 1≤h
    · exact he
    have hz : h=0 := by omega
    have hp:=hpos 1 (by omega) (by omega)
    have ha:=hA 0 hM
    simp only [hz,Nat.add_zero] at ha
    have hc : cN (fun x=>f x=false) n 1=0 := by simp [cN,ha]
    omega
  have hwC : seg f n C=y := by
    have he:=Recaman.SeparatorSupplyReset.three_run_word f n h M m L s 0
      hS hA hS2 hA2 hS3 (by intro i hi; omega)
    simpa only [Nat.add_zero,List.replicate_zero,List.append_nil] using he
  have hAC : cN (fun x=>f x=true) n C=M+L := by
    have he:=ones_seg_eq_count f n C
    rw [hwC] at he
    simp only [y,ones_append,ones_replicate_A,ones_replicate_S] at he
    omega
  have hf : 1≤cN (fun x=>f x=true ∧ ¬EndN f 0 x) n C := by
    by_cases he : 1≤cN (fun x=>f x=true ∧ ¬EndN f 0 x) n C
    · exact he
    have hz : cN (fun x=>f x=true ∧ ¬EndN f 0 x) n C=0 := by omega
    have hb:=positive_r3_additions_free_bound f n 0 C hw (by simpa using hpre)
      (fun k hk hkC=>hpos k hk (by dsimp [C] at hkC; omega)) (by omega)
    rw [hz,hAC] at hb
    omega
  have hp:=addition_endable_partition f n C
  rw [hAC] at hp
  have hlocal : rayCount y U≤3 := by
    have h1:=Recaman.MixedShortAPairBudget.pair_prefix_saving
      (List.replicate m false++(List.replicate L true++List.replicate s false)) h M U hhM
    have h2:=Recaman.MixedShortAPairBudget.pair_prefix_saving (List.replicate s false) m L U hhL
    have h3:=rayCount_A_S_le_one 0 s U hs
    simp only [List.replicate_zero,List.nil_append] at h3
    simp only [y,List.append_assoc] at h1 h2 ⊢
    omega
  have hy : 3≤cntF y := by
    simp only [y,cntF_append,cntF_replicate_S,Recaman.UnitTargetSASProfile.cntF_A]
    omega
  have hA3' : ∀ i, i<U → f (n+C+i)=true := by simpa only [C,Nat.add_assoc] using hA3
  have ho:=(Recaman.MixedFinalRayOldBudget.actual_mixed_ray_old_budget f n C U w y hw hpre hwC hy hA3').1
  have he:=cN_add (EndN f 0) n C U
  change cN (EndN f 0) n (C+U)=_ at he
  change cN (EndN f 0) n (C+U)≤M+L+3
  omega

end Recaman.ShortEarlyHeadBudget
