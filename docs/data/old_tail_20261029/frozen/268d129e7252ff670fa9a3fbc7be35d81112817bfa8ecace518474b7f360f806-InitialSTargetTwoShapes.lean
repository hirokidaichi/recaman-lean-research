import Recaman.InitialSTargetTail

namespace Recaman.InitialSTargetTwoShapes

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.ASourceReuse
open Recaman.RunClockClassifier Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.SourceFamilyFreeCount Recaman.OldTargetLocalTail Recaman.OldTargetClockCollision
open Recaman.OldTargetMiddleCharge Recaman.InitialSTargetBounds Recaman.InitialSTargetTail
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

theorem large_first_two_shapes (q M m L s T j : Nat)
    (hM : j+1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hj : 4≤j)
    (hhead : M+L≤7) (hbudget : M+L+T≤20)
    (hmt : mass (List.replicate q false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate T true++List.replicate j false)=1)
    (hat : areaW (List.replicate q false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate T true++List.replicate j false)=0) :
    (q=5 ∧ M=5 ∧ m=1 ∧ L=2 ∧ s=1 ∧ T=5 ∧ j=4) ∨
    (q=4 ∧ M=5 ∧ m=2 ∧ L=1 ∧ s=3 ∧ T=8 ∧ j=4) := by
  have ht := initial_S_target_equations q M m L s T j (by omega) hm hmt hat
  have hp := initial_S_critical_pairs q M m L s T j (by omega) hm hj hbudget hmt hat
  rcases hp with ⟨rfl,hA⟩|⟨rfl,hA⟩|⟨rfl,hA⟩|⟨rfl,hA⟩
  · have hsum : (q : Int)+(m : Int)+(s : Int)=7 := by omega
    have hI : (M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int)=12 := by
      have he := ht.2.1
      rw [hsum] at he
      simp only [Int.reduceAdd,Int.reducePow,Int.reduceSub] at he
      grind
    have hML : (M=5 ∧ L=1) ∨ (M=5 ∧ L=2) ∨ (M=6 ∧ L=1) := by omega
    rcases hML with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · have hc : 5*(m : Int)+6*(s : Int)=12 := by grind
      omega
    · have hc : 5*(m : Int)+7*(s : Int)=12 := by grind
      left
      exact ⟨by omega,rfl,by omega,rfl,by omega,by omega,rfl⟩
    · have hc : 6*(m : Int)+7*(s : Int)=12 := by grind
      omega
  · have hsum : (q : Int)+(m : Int)+(s : Int)=9 := by omega
    have hI : (M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int)=28 := by
      have he := ht.2.1
      rw [hsum] at he
      simp only [Int.reduceAdd,Int.reducePow,Int.reduceSub] at he
      grind
    have hML : (M=5 ∧ L=1) ∨ (M=5 ∧ L=2) ∨ (M=6 ∧ L=1) := by omega
    rcases hML with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · have hc : 5*(m : Int)+6*(s : Int)=28 := by grind
      right
      exact ⟨by omega,rfl,by omega,rfl,by omega,by omega,rfl⟩
    · have hc : 5*(m : Int)+7*(s : Int)=28 := by grind
      omega
    · have hc : 6*(m : Int)+7*(s : Int)=28 := by grind
      omega
  · have hM6 : M=6 := by omega
    have hL1 : L=1 := by omega
    have hsum : (q : Int)+(m : Int)+(s : Int)=8 := by omega
    have hI : 6*(m : Int)+7*(s : Int)=14 := by
      have he := ht.2.1
      rw [hsum] at he
      rw [hM6,hL1] at he
      simp only [Int.reduceAdd,Int.reducePow,Int.reduceSub] at he
      grind
    omega
  · omega

theorem two_shape_clock (h i : Nat) :
    (thirdClock h 5 1 2 1 i=true → i=2) ∧ (thirdClock h 5 2 1 3 i=true → i=2) := by
  constructor
  · intro hc
    simp only [thirdClock,decide_eq_true_eq] at hc
    rcases hc with hi|⟨hq,hqh,heq⟩|⟨he,heM,heq⟩|⟨hv,hvm,heq⟩
    · exact hi
    · have hp := Int.mul_nonneg (show 0≤(i : Int)+1 by omega) (show 0≤(i : Int)+11 by omega)
      grind
    · grind
    · grind
  · intro hc
    simp only [thirdClock,decide_eq_true_eq] at hc
    rcases hc with hi|⟨hq,hqh,heq⟩|⟨he,heM,heq⟩|⟨hv,hvm,heq⟩
    · exact hi
    · by_cases hi3 : i≤2
      · have his : i=0 ∨ i=1 ∨ i=2 := by omega
        rcases his with rfl|rfl|rfl <;> simp at heq
      · have hp := Int.mul_nonneg (show 0≤(i : Int)-3 by omega) (show 0≤(i : Int)+13 by omega)
        grind
    · grind
    · grind

theorem two_shape_local_count (h T : Nat) :
    rayCount (List.replicate h false++List.replicate 5 true++List.replicate 1 false++
      List.replicate 2 true++List.replicate 1 false) T≤1 ∧
    rayCount (List.replicate h false++List.replicate 5 true++List.replicate 2 false++
      List.replicate 1 true++List.replicate 3 false) T≤1 := by
  constructor
  · unfold rayCount
    apply cN_le_one_of_unique
    intro i _ k _ hi hk
    have hci := thirdClock_sound h 5 1 2 1 i (by omega) hi
    have hck := thirdClock_sound h 5 1 2 1 k (by omega) hk
    exact ((two_shape_clock h i).1 hci).trans ((two_shape_clock h k).1 hck).symm
  · unfold rayCount
    apply cN_le_one_of_unique
    intro i _ k _ hi hk
    have hci := thirdClock_sound h 5 2 1 3 i (by omega) hi
    have hck := thirdClock_sound h 5 2 1 3 k (by omega) hk
    exact ((two_shape_clock h i).2 hci).trans ((two_shape_clock h k).2 hck).symm

end Recaman.InitialSTargetTwoShapes
