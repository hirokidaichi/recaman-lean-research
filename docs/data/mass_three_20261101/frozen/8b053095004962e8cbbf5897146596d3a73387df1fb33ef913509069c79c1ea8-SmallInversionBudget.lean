import Recaman.SmallInversionSources
import Recaman.InitialSTargetBounds

namespace Recaman.SmallInversionBudget

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.ThreeRunSupplyBudget Recaman.SourceFamilyFreeCount Recaman.SmallInversionSources

theorem three_run_count_from_local (f : Nat → Bool) (n h M m L s T : Nat) (w : List Bool)
    (hw : BlockWord w) (hpre : seg f 0 n=w) (hs : 1≤s) (hSsum : 3≤h+m+s)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ i, i<M → f (n+h+i)=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → f x=false)
    (hA2 : ∀ i, i<L → f (n+h+M+m+i)=true)
    (hS3 : ∀ x, n+h+M+m+L≤x → x<n+h+M+m+L+s → f x=false)
    (hA3 : ∀ i, i<T → f (n+h+M+m+L+s+i)=true)
    (C : Nat) (hlocal : rayCount (List.replicate h false++List.replicate M true++List.replicate m false++List.replicate L true++List.replicate s false) T≤C)
    (hpos : ∀ k, 0<k → k≤h+M+m+L+s+T →
      cN (EndN f 0) n k+1≤cN (fun x => f x=false) n k) :
    cN (EndN f 0) n (h+M+m+L+s+T)≤C+6 := by
  have hb2 := two_run_supply_of_positive f n h M m L w hw hpre hS hA hS2 hA2
    (fun hk => hpos _ hk (by omega))
  have hword := Recaman.SeparatorSupplyReset.three_run_word f n h M m L s 0
    hS hA hS2 hA2 hS3 (by intro i hi; omega)
  have hp : seg f 0 (n+h+M+m+L+s)=w++(List.replicate h false++List.replicate M true++
      List.replicate m false++List.replicate L true++List.replicate s false) := by
    rw [show n+h+M+m+L+s=n+(h+M+m+L+s) by omega,seg_add,Nat.zero_add,hpre]
    congr 1
    simpa using hword
  have hcS : 3≤cntF (List.replicate h false++List.replicate M true++
      List.replicate m false++List.replicate L true++List.replicate s false) := by
    simp only [cntF_append,cntF_replicate_S,cntF_A]
    omega
  have ho := block_rayCount_append hw _ hcS T
  have hl := hlocal
  have he := endable_A_run_count f (n+h+M+m+L+s) T _ hp hA3
  have hz : cN (EndN f 0) (n+h+M+m+L) s=0 := by
    apply cN_zero_of
    intro x hx hxs he
    have hh := he.1
    rw [hS3 x hx hxs] at hh
    contradiction
  have a := cN_add (EndN f 0) n (h+M+m+L) s
  have b := cN_add (EndN f 0) n (h+M+m+L+s) T
  simp only [Nat.add_assoc] at *
  omega

theorem small_inversion_three_run_count_eight (f : Nat → Bool) (n h M m L s T : Nat) (w : List Bool)
    (hw : BlockWord w) (hpre : seg f 0 n=w) (hs : 1≤s) (hSsum : 3≤h+m+s)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ i, i<M → f (n+h+i)=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → f x=false)
    (hA2 : ∀ i, i<L → f (n+h+M+m+i)=true)
    (hS3 : ∀ x, n+h+M+m+L≤x → x<n+h+M+m+L+s → f x=false)
    (hA3 : ∀ i, i<T → f (n+h+M+m+L+s+i)=true)
    (hM : 1≤M) (hm : 1≤m) (hL : 1≤L)
    (hI : (M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int)≤16)
    (hpos : ∀ k, 0<k → k≤h+M+m+L+s+T →
      cN (EndN f 0) n k+1≤cN (fun x => f x=false) n k) :
    cN (EndN f 0) n (h+M+m+L+s+T)≤8 := by
  have hl:=small_inversion_third_local_two h M m L s T hM hm hL hs hI
  have hb:=three_run_count_from_local f n h M m L s T w hw hpre hs hSsum
    hS hA hS2 hA2 hS3 hA3 2 hl hpos
  omega

theorem small_inversion_three_run_count_nine (f : Nat → Bool) (n h M m L s T : Nat) (w : List Bool)
    (hw : BlockWord w) (hpre : seg f 0 n=w) (hs : 1≤s) (hSsum : 3≤h+m+s)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ i, i<M → f (n+h+i)=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → f x=false)
    (hA2 : ∀ i, i<L → f (n+h+M+m+i)=true)
    (hS3 : ∀ x, n+h+M+m+L≤x → x<n+h+M+m+L+s → f x=false)
    (hA3 : ∀ i, i<T → f (n+h+M+m+L+s+i)=true)
    (hM : 1≤M) (hm : 1≤m) (hL : 1≤L)
    (hI : (M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int)≤36)
    (hpos : ∀ k, 0<k → k≤h+M+m+L+s+T →
      cN (EndN f 0) n k+1≤cN (fun x => f x=false) n k) :
    cN (EndN f 0) n (h+M+m+L+s+T)≤9 := by
  have hl:=small_inversion_third_local_three h M m L s T hM hm hL hs hI
  have hb:=three_run_count_from_local f n h M m L s T w hw hpre hs hSsum
    hS hA hS2 hA2 hS3 hA3 3 hl hpos
  omega

end Recaman.SmallInversionBudget
