import Recaman.OldTargetFirstRun
import Recaman.RunClockClassifier

namespace Recaman.OldTargetMassFive

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.RunSupplyKeys Recaman.TwoRunSupply Recaman.RunSupplyBudget Recaman.BlockOldRay
open Recaman.ThreeRunSupplyBudget Recaman.InitialSTargetBounds Recaman.OldTargetAreaBudget
open Recaman.OldTargetFirstRun Recaman.RunClockClassifier Recaman.MiddleSTargetFreeGap
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

private theorem six_parameters (h M m L s T j : Nat)
    (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s)
    (hR : 5≤(j : Int)+1)
    (hE0 : 0≤(M : Int)+(L : Int)+(T : Int)-((j : Int)+1))
    (hE9 : (M : Int)+(L : Int)+(T : Int)-((j : Int)+1)≤9)
    (hsmall : M≤3 → (M : Int)+(L : Int)+(T : Int)-((j : Int)+1)≤8)
    (hbal : (6 : Int)=(h : Int)+(m : Int)+(s : Int)+((j : Int)+1)-((M : Int)+(L : Int)+(T : Int)))
    (hq : (36 : Int)+2*((M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int))≤
      ((M : Int)+(L : Int)+(T : Int)-((j : Int)+1))^2-((j : Int)+1)^2+1) :
    h=13 ∧ M=4 ∧ m=1 ∧ s=1 ∧ j=4 ∧ ((L=1 ∧ T=9) ∨ (L=2 ∧ T=8)) := by
  let R : Int := (j : Int)+1
  let E : Int := (M : Int)+(L : Int)+(T : Int)-R
  let I : Int := (M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int)
  change 5≤R at hR
  change 0≤E at hE0
  change E≤9 at hE9
  change M≤3 → E≤8 at hsmall
  change 36+2*I≤E^2-R^2+1 at hq
  have hpR := Int.mul_nonneg (show 0≤R-5 by omega) (show 0≤R+5 by omega)
  have hpE := Int.mul_nonneg (show 0≤9-E by omega) (show 0≤9+E by omega)
  have hmp := Int.mul_nonneg (show 0≤(M : Int) by omega) (show 0≤(m : Int)+(s : Int)-2 by omega)
  have hls := Int.mul_pos (show 0<(L : Int) by omega) (show 0<(s : Int) by omega)
  have hi : 2*(M : Int)+1≤I := by dsimp [I]; grind
  have hM4 : 4≤M := by
    by_cases hh : 4≤M
    · exact hh
    · exfalso
      have he8 := hsmall (by omega)
      have hp8 := Int.mul_nonneg (show 0≤8-E by omega) (show 0≤8+E by omega)
      grind
  have hr5 : R=5 := by
    by_cases hh : R=5
    · exact hh
    · exfalso
      have hp6 := Int.mul_nonneg (show 0≤R-6 by omega) (show 0≤R+6 by omega)
      grind
  have he9 : E=9 := by
    by_cases hh : E=9
    · exact hh
    · exfalso
      have hp8 := Int.mul_nonneg (show 0≤8-E by omega) (show 0≤8+E by omega)
      grind
  have hi10 : I≤10 := by rw [hr5,he9] at hq; simp only [Int.reduceAdd,Int.reduceSub,Int.reducePow] at hq; omega
  have hm4 : M=4 := by omega
  have hms : m=1 ∧ s=1 := by
    subst M
    dsimp [I] at hi10
    grind
  rcases hms with ⟨rfl,rfl⟩
  subst M
  have hl2 : L≤2 := by dsimp [I] at hi10; simp only [Int.mul_one] at hi10; omega
  dsimp [R,E] at hr5 he9
  refine ⟨by omega,rfl,rfl,rfl,by omega,?_⟩
  by_cases hh : L=1
  · exact Or.inl ⟨hh,by omega⟩
  · exact Or.inr ⟨by omega,by omega⟩

private theorem two_shape_clocks :
    thirdFastCount 13 4 1 1 1 9=1 ∧ thirdFastCount 13 4 1 2 1 8=1 := by decide

theorem old_target_mass_five (f : Nat → Bool) (n t h M m L s T j : Nat)
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
    mass (seg f t (n-t))≤5 ∧ h+m+s≤14 ∧ (seg f t (n-t)).length≤12 := by
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
  have hb6 := old_target_mass_six f n t h M m L s T j w hw hpre ht hM hm hL hs hT
    hS hA hS2 hA2 hS3 hA3 hB hpos hgap he hbad hwin
  have hC5 : C≤5 := by
    by_cases hh : C≤5
    · exact hh
    · have hC6 : C=6 := by dsimp [C] at *; omega
      have hsmall : M≤3 → E≤8 := by
        intro hM3
        have hc9 := three_run_count_small_first f n h M m L s T w hw hpre hM3 hs hprior
          hS hA hS2 hA2 hS3 hA3 hpos
        dsimp [E,A,R]
        omega
      have hbal : (6 : Int)=(h : Int)+(m : Int)+(s : Int)+((j : Int)+1)-
          ((M : Int)+(L : Int)+(T : Int)) := by
        have hh := ho.2.2.1
        change C=_ at hh
        omega
      have hqq : (36 : Int)+2*((M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int))≤
          ((M : Int)+(L : Int)+(T : Int)-((j : Int)+1))^2-((j : Int)+1)^2+1 := by
        rw [hC6] at hquad
        dsimp [I,E,A,R] at hquad
        simpa only [Int.reducePow] using hquad
      have hpar := six_parameters h M m L s T j hM hm hL hs hR5 hE0 hE9 hsmall hbal hqq
      have hword0 := Recaman.SeparatorSupplyReset.three_run_word f n h M m L s 0
        hS hA hS2 hA2 hS3 (by intro i hi; omega)
      have hp3 : seg f 0 (n+h+M+m+L+s)=w++(List.replicate h false++List.replicate M true++
          List.replicate m false++List.replicate L true++List.replicate s false) := by
        rw [show n+h+M+m+L+s=n+(h+M+m+L+s) by omega,seg_add,Nat.zero_add,hpre]
        congr 1
        simpa using hword0
      have hcS : 3≤cntF (List.replicate h false++List.replicate M true++
          List.replicate m false++List.replicate L true++List.replicate s false) := by
        have aux : ∀ k : Nat, cntF (List.replicate k true)=0 := by
          intro k
          induction k with
          | zero => rfl
          | succ k ih => simp [List.replicate_succ,cntF,ih]
        simp only [cntF_append,cntF_replicate_S,aux]
        omega
      have hold := block_rayCount_append hw _ hcS T
      have hlocal := third_ray_fast_bound h M m L s T hs
      have hactual := endable_A_run_count f (n+h+M+m+L+s) T _ hp3 hA3
      have hpartition := addition_endable_partition f (n+h+M+m+L+s) T
      rw [count_A_run f _ T hA3] at hpartition
      have hfree := cN_add (fun x => f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s) T
      have hfast : thirdFastCount h M m L s T=1 := by
        rcases hpar with ⟨rfl,rfl,rfl,rfl,_,⟨rfl,rfl⟩|⟨rfl,rfl⟩⟩
        · exact two_shape_clocks.1
        · exact two_shape_clocks.2
      rw [hfast] at hlocal
      have hT8 : 8≤T := by rcases hpar.2.2.2.2.2 with hh|hh <;> omega
      have hj4 := hpar.2.2.2.2.1
      simp only [Nat.add_assoc] at *
      omega
  have hdense := dense_of_block ho.1 [] (seg f t (n-t)) rfl
  have hmassC := mass_cntF (seg f t (n-t))
  have hlen : (seg f t (n-t)).length≤12 := by dsimp [C] at hC5; omega
  exact ⟨hC5,by dsimp [C,E,A,R] at *; omega,hlen⟩

end Recaman.OldTargetMassFive
