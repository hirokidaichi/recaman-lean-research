import Recaman.OldTargetAreaBudget

namespace Recaman.OldTargetFirstRun

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.RunSupplyKeys Recaman.TwoRunSupply Recaman.RunSupplyBudget Recaman.BlockOldRay
open Recaman.ThreeRunSupplyBudget Recaman.InitialSTargetBounds Recaman.OldTargetAreaBudget Recaman.MiddleSTargetFreeGap
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
    change cN (EndN f 0) (n+h) 3≤cN (EndN f 0) (n+h) 2+1 at hc
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

theorem old_target_mass_six (f : Nat → Bool) (n t h M m L s T j : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w) (ht : t<n)
    (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hT : 1≤T)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ i, i<M → f (n+h+i)=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → f x=false)
    (hA2 : ∀ i, i<L → f (n+h+M+m+i)=true)
    (hS3 : ∀ x, n+h+M+m+L≤x → x<n+h+M+m+L+s → f x=false)
    (hA3 : ∀ i, i<T → f (n+h+M+m+L+s+i)=true)
    (hB : 0<h+M+m+L+s+T)
    (hpos : ∀ k, 0<k → k≤h+M+m+L+s+T →
      cN (EndN f 0) n k+1≤cN (fun x => f x=false) n k)
    (hgap : ∀ x, n+h+M+m+L+s+T≤x → x<n+h+M+m+L+s+T+j → f x=false)
    (he : EndN f 0 (n+h+M+m+L+s+T+j))
    (hbad : cN (fun x => f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+T)<j+1)
    (hwin : Win f t (n+h+M+m+L+s+T+j-t)) :
    mass (seg f t (n-t))≤6 ∧ h+m+s≤15 ∧ (seg f t (n-t)).length≤15 := by
  have hb := old_target_counterexample_band f n t h M m L s T j w hw hpre ht hs
    hS hA hS2 hA2 hS3 hA3 hB hpos hgap he hbad hwin
  have hshape := Recaman.SeparatorSupplyReset.three_run_word f n h M m L s T hS hA hS2 hA2 hS3 hA3
  have hword : seg f n (h+M+m+L+s+T+j)=
      List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate T true++List.replicate j false := by
    rw [seg_add,show n+(h+M+m+L+s+T)=n+h+M+m+L+s+T by omega,
      seg_false f (n+h+M+m+L+s+T) j hgap,hshape]
  have ho := actual_old_target_budget f n t h M m L s T j w hw hpre ht hword hwin
  have hprior : 3≤h+m+s := by omega
  have hc10 := three_run_count_of_manyS f n h M m L s T w hw hpre hs hprior
    hS hA hS2 hA2 hS3 hA3 hpos
  have hc := ones_seg_eq_count f n (h+M+m+L+s+T)
  rw [hshape] at hc
  simp only [ones_append,ones_replicate_S,ones_replicate_A] at hc
  have hp := addition_endable_partition f n (h+M+m+L+s+T)
  let A : Int := (M : Int)+(L : Int)+(T : Int)
  let R : Int := (j : Int)+1
  let E : Int := A-R
  let C := mass (seg f t (n-t))
  let I : Int := (M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int)
  have hE9 : E≤9 := by dsimp [E,A,R]; omega
  have hE0 : 0≤E := by dsimp [E,A,R]; omega
  have hR5 : 5≤R := by dsimp [R]; omega
  have hRprod := Int.mul_nonneg (show 0≤R-5 by omega) (show 0≤R+5 by omega)
  have hquad : C^2+2*I≤E^2-R^2+1 := by
    have hq := ho.2.2.2.1
    change C^2+2*I≤A*(A-2*R)+1 at hq
    dsimp [E]
    grind
  have hI0 : 0≤I := by
    have h1 := Int.mul_nonneg (show 0≤(M : Int) by omega) (show 0≤(m : Int)+(s : Int) by omega)
    have h2 := Int.mul_nonneg (show 0≤(L : Int) by omega) (show 0≤(s : Int) by omega)
    dsimp [I]
    omega
  have hC2 : C^2≤40 := by
    by_cases hM3 : M≤3
    · have hc9 := three_run_count_small_first f n h M m L s T w hw hpre hM3 hs hprior
        hS hA hS2 hA2 hS3 hA3 hpos
      have hE8 : E≤8 := by dsimp [E,A,R]; omega
      have hEprod := Int.mul_nonneg (show 0≤8-E by omega) (show 0≤8+E by omega)
      grind
    · have hB2 : 2≤(m : Int)+(s : Int) := by omega
      have hMp := Int.mul_nonneg (show 0≤(M : Int)-4 by omega) (show 0≤(m : Int)+(s : Int) by omega)
      have hLp := Int.mul_pos (show 0<(L : Int) by omega) (show 0<(s : Int) by omega)
      have hI9 : 9≤I := by dsimp [I]; grind
      have hEprod := Int.mul_nonneg (show 0≤9-E by omega) (show 0≤9+E by omega)
      grind
  have hC6 : C≤6 := by
    by_cases hh : C≤6
    · exact hh
    · have hcp := Int.mul_nonneg (show 0≤C-7 by omega) (show 0≤C+7 by dsimp [C]; omega)
      grind
  have hdense := dense_of_block ho.1 [] (seg f t (n-t)) rfl
  have hmassC := mass_cntF (seg f t (n-t))
  have hlen : (seg f t (n-t)).length≤15 := by dsimp [C] at hC6; omega
  exact ⟨hC6,by dsimp [C,E,A,R] at *; omega,hlen⟩

end Recaman.OldTargetFirstRun
