import Recaman.OldTargetAreaBudget

namespace Recaman.OldTargetFirstRun

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.RunSupplyKeys Recaman.TwoRunSupply Recaman.RunSupplyBudget Recaman.BlockOldRay
open Recaman.ThreeRunSupplyBudget Recaman.InitialSTargetBounds Recaman.OldTargetAreaBudget
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

private theorem cntF_A (k : Nat) : cntF (List.replicate k true)=0 := by
  have hc := cntF_int (List.replicate k true)
  rw [List.length_replicate,ones_replicate_A] at hc
  omega

private theorem no_supply_in_S (f : Nat → Bool) (n K : Nat)
    (hS : ∀ x, n≤x → x<n+K → f x=false) : cN (EndN f 0) n K=0 := by
  apply cN_zero_of
  intro x hx hxK he
  have hh := he.1
  rw [hS x hx hxK] at hh
  contradiction

theorem first_run_supply_le_one (f : Nat → Bool) (n h M : Nat) (w : List Bool)
    (hw : BlockWord w) (hpre : seg f 0 n=w) (hM : M≤3)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ i, i<M → f (n+h+i)=true) : cN (EndN f 0) (n+h) M≤1 := by
  by_cases hM2 : M≤2
  · have hz : cN (EndN f 0) (n+h) M=0 := by
      apply cN_zero_of
      intro x hx hxM he
      have hn := first_two_A_not_supplied f n h M w hw hpre hS hA (x-(n+h)) (by omega) (by omega)
      rw [Nat.add_sub_cancel' hx] at hn
      exact hn he
    omega
  · have hM3 : M=3 := by omega
    have hz : cN (EndN f 0) (n+h) 2=0 := by
      apply cN_zero_of
      intro x hx hxM he
      have hn := first_two_A_not_supplied f n h M w hw hpre hS hA (x-(n+h)) (by omega) (by omega)
      rw [Nat.add_sub_cancel' hx] at hn
      exact hn he
    have hc := cN_succ_le (EndN f 0) (n+h) 2
    rw [hM3]
    omega

theorem two_run_small_first_count_of_manyS (f : Nat → Bool) (n h M m L : Nat) (w : List Bool)
    (hw : BlockWord w) (hpre : seg f 0 n=w)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ i, i<M → f (n+h+i)=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → f x=false)
    (hA2 : ∀ i, i<L → f (n+h+M+m+i)=true) (hM : M≤3) (hsum : 3≤h+m) :
    cN (EndN f 0) n (h+M+m+L)≤4 := by
  have hp1 : seg f 0 (n+h)=w++List.replicate h false := by
    rw [seg_add,show 0+n=n by omega,hpre,seg_false f n h hS]
  have hr1 := endable_A_run_count f (n+h) M _ hp1 hA
  have hb1 := first_run_supply_le_one f n h M w hw hpre hM hS hA
  have hp2 : seg f 0 (n+h+M+m)=
      w++(List.replicate h false++List.replicate M true++List.replicate m false) := by
    have hsegA : seg f (n+h) M=List.replicate M true := by
      apply seg_A
      intro x hx hxM
      simpa only [Nat.add_sub_cancel' hx] using hA (x-(n+h)) (by omega)
    rw [show n+h+M+m=(n+h+M)+m by omega,seg_add,
      show 0+(n+h+M)=n+h+M by omega,seg_false f (n+h+M) m hS2,
      show n+h+M=(n+h)+M by omega,seg_add,show 0+(n+h)=n+h by omega,hp1,hsegA]
    simp only [List.append_assoc]
  have hr2 := endable_A_run_count f (n+h+M+m) L _ hp2 hA2
  have hcnt : cntF (List.replicate h false++List.replicate M true++List.replicate m false)=h+m := by
    have aux : ∀ k : Nat, cntF (List.replicate k true)=0 := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih => simp [List.replicate_succ,cntF,ih]
    have ha := aux M
    simp only [cntF_append,cntF_replicate_S,ha,Nat.add_zero]
  have hb2 := block_rayCount_append hw
      (List.replicate h false++List.replicate M true++List.replicate m false) (by omega) L
  have hl := rayCount_S_A_S h M m L
  have h0 := no_supply_in_S f n h hS
  have h2 := no_supply_in_S f (n+h+M) m hS2
  have hc1 := cN_add (EndN f 0) n h M
  have hc2 := cN_add (EndN f 0) n (h+M) m
  have hc3 := cN_add (EndN f 0) n (h+M+m) L
  simp only [Nat.add_assoc] at *
  omega

theorem two_run_small_first_positive (f : Nat → Bool) (n h M m L : Nat) (w : List Bool)
    (hw : BlockWord w) (hpre : seg f 0 n=w) (hM : M≤3)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ i, i<M → f (n+h+i)=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → f x=false)
    (hA2 : ∀ i, i<L → f (n+h+M+m+i)=true)
    (hpos : 0<h+M+m+L → cN (EndN f 0) n (h+M+m+L)+1≤cN (fun x => f x=false) n (h+M+m+L)) :
    cN (EndN f 0) n (h+M+m+L)≤4 := by
  by_cases hs : 3≤h+m
  · exact two_run_small_first_count_of_manyS f n h M m L w hw hpre hS hA hS2 hA2 hM hs
  · by_cases hb : 0<h+M+m+L
    · have hp := hpos hb
      have hword := Recaman.SeparatorSupplyReset.three_run_word f n h M m L 0 0
        hS hA hS2 hA2 (by intro x hx hx0; omega) (by intro i hi; omega)
      have hs0 : seg f n (h+M+m+L)=List.replicate h false++List.replicate M true++
          List.replicate m false++List.replicate L true := by simpa using hword
      have hc := cntF_seg f n (h+M+m+L)
      rw [hs0] at hc
      simp only [cntF_append,cntF_replicate_S,cntF_A] at hc
      omega
    · have h0 : h+M+m+L=0 := by omega
      rw [h0]
      change 0≤4
      omega

theorem three_run_count_small_first (f : Nat → Bool) (n h M m L s T : Nat) (w : List Bool)
    (hw : BlockWord w) (hpre : seg f 0 n=w) (hM : M≤3) (hs : 1≤s) (hSsum : 3≤h+m+s)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ i, i<M → f (n+h+i)=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → f x=false)
    (hA2 : ∀ i, i<L → f (n+h+M+m+i)=true)
    (hS3 : ∀ x, n+h+M+m+L≤x → x<n+h+M+m+L+s → f x=false)
    (hA3 : ∀ i, i<T → f (n+h+M+m+L+s+i)=true)
    (hpos : ∀ k, 0<k → k≤h+M+m+L+s+T →
      cN (EndN f 0) n k+1≤cN (fun x => f x=false) n k) :
    cN (EndN f 0) n (h+M+m+L+s+T)≤9 := by
  have hb2 := two_run_small_first_positive f n h M m L w hw hpre hM hS hA hS2 hA2
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
  have hl := third_ray_four_source_bound h M m L s T hs
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

end Recaman.OldTargetFirstRun
