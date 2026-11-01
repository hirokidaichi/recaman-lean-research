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
  have hi10 : I≤10 := by rw [hr5,he9] at hq; simp only [Int.reduceAdd,Int.reduceSub,Int.reduceMul,Int.reducePow] at hq; omega
  have hm4 : M=4 := by omega
  have hms : m=1 ∧ s=1 := by
    subst M
    dsimp [I] at hi10
    grind
  rcases hms with ⟨rfl,rfl⟩
  subst M
  have hl2 : L≤2 := by dsimp [I] at hi10; simp only [Int.natCast_one,Int.mul_one] at hi10; omega
  dsimp [R,E] at hr5 he9
  refine ⟨by omega,rfl,rfl,rfl,by omega,?_⟩
  by_cases hh : L=1
  · exact Or.inl ⟨hh,by omega⟩
  · exact Or.inr ⟨by omega,by omega⟩

private theorem two_shape_clocks :
    thirdFastCount 13 4 1 1 1 9=1 ∧ thirdFastCount 13 4 1 2 1 8=1 := by decide

