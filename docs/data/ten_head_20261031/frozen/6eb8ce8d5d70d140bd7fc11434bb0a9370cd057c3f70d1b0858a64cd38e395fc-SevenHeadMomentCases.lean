import Recaman.FourthClockClassifier
import Recaman.MomentTargetProfile

namespace Recaman.SevenHeadMomentCases

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.SourceFamilyFreeCount Recaman.FourthClockClassifier

/-- The measured zero-mass three-run head exposes its exact integer
moment. This is an identity used for pruning, not an assumed free bound. -/
theorem three_head_moment (h M m L s U : Nat) (hzero : M+L+U=h+m+s) (B : Int)
    (ha : areaW (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true)= -B) :
    B=((h : Int)+(m : Int)+(s : Int))^2-
      2*((M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int)) := by
  have hm : mass (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true)=0 := by
    simp only [mass_append,mass_rep_false,mass_replicate_A]
    omega
  have hk : runKey (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true)= -2*B := by
    unfold runKey
    rw [hm,ha]
    grind only
  rw [runKey_append_A,runKey_five_runs] at hk
  grind only

/-- The low-head target parameters collapse to S7/v2/R5/B39. The
quadratic and moment are supplied from the same actual target/head. -/
theorem small_mass_one_numbers (S v T j : Nat) (B I : Int)
    (hS : S≤7) (hv : v=1 ∨ v=2) (hR : 5≤j+1) (hbal : T=v+j)
    (hkey : B=((j : Int)+1)^2+2*((S : Int)+(v : Int))-(v : Int)^2)
    (hcircle : ((j : Int)+1)^2≤4*(S : Int)+4)
    (hmoment : B=(S : Int)^2-2*I) (hI : 0≤I) :
    S=7 ∧ v=2 ∧ T=6 ∧ j=4 ∧ B=39 ∧ I=5 := by
  have hp:=Int.mul_nonneg (show 0≤(j : Int)-4 by omega) (show 0≤(j : Int)+6 by omega)
  have hR25 : 25≤((j : Int)+1)^2 := by grind only
  have hS67 : S=6 ∨ S=7 := by omega
  have hj4 : j=4 := by
    by_cases hh : j=4
    · exact hh
    · have hq:=Int.mul_nonneg (show 0≤(j : Int)-5 by omega) (show 0≤(j : Int)+7 by omega)
      grind only
  subst j
  rcases hS67 with rfl|rfl <;> rcases hv with rfl|rfl
  · have he : B=38 := by grind only
    rw [he] at hmoment
    grind only
  · have he : B=37 := by grind only
    rw [he] at hmoment
    omega
  · have he : B=40 := by grind only
    rw [he] at hmoment
    omega
  · have he : B=39 := by grind only
    refine ⟨rfl,rfl,by omega,rfl,he,?_⟩
    rw [he] at hmoment
    omega

private theorem five_head_cases (h M m L s U : Nat)
    (hh : 1≤h) (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hU : 1≤U)
    (hS : h+m+s=7) (hA : M+L+U=7)
    (hI : (M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int)=5) :
    (h=5 ∧ M=2 ∧ m=1 ∧ L=1 ∧ s=1 ∧ U=4) ∨
    (h=5 ∧ M=1 ∧ m=1 ∧ L=3 ∧ s=1 ∧ U=3) ∨
    (h=4 ∧ M=1 ∧ m=2 ∧ L=2 ∧ s=1 ∧ U=4) ∨
    (h=3 ∧ M=1 ∧ m=3 ∧ L=1 ∧ s=1 ∧ U=5) ∨
    (h=4 ∧ M=1 ∧ m=1 ∧ L=1 ∧ s=2 ∧ U=5) := by
  have hmp:=Int.mul_nonneg (show 0≤(M : Int) by omega) (show 0≤(m : Int)+(s : Int)-2 by omega)
  have hlp:=Int.mul_nonneg (show 0≤(L : Int)-1 by omega) (show 0≤(s : Int) by omega)
  have hM12 : M=1 ∨ M=2 := by grind only
  rcases hM12 with rfl|rfl
  · have hs2 : s≤2 := by grind only
    have hs12 : s=1 ∨ s=2 := by omega
    rcases hs12 with rfl|rfl
    · have hm3 : m=1 ∨ m=2 ∨ m=3 := by omega
      rcases hm3 with rfl|rfl|rfl <;> omega
    · omega
  · have hms : m+s=2 := by grind only
    have hm1 : m=1 := by omega
    have hs1 : s=1 := by omega
    rw [hm1,hs1] at hI
    omega

/-- Thirty scalar clock cells suffice AFTER the five-head classification;
no full word table or unproved tuple-coverage premise is used. -/
theorem seven_head_local_four (h M m L s U : Nat)
    (hh : 1≤h) (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hU : 1≤U)
    (hS : h+m+s=7) (hA : M+L+U=7)
    (hI : (M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int)=5) :
    rayCount (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true++List.replicate 2 false) 6≤4 := by
  have hb:=fourth_ray_fast_bound h M m L s U 2 6 (by decide)
  have hc:=five_head_cases h M m L s U hh hM hm hL hs hU hS hA hI
  rcases hc with ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩|⟨rfl,rfl,rfl,rfl,rfl,rfl⟩|
    ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩|⟨rfl,rfl,rfl,rfl,rfl,rfl⟩|⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
  all_goals exact Nat.le_trans hb (by decide)

end Recaman.SevenHeadMomentCases
