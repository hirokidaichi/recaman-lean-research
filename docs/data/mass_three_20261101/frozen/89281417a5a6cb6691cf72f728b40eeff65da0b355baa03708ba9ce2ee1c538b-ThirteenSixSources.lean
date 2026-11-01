import Recaman.ThirteenRunFactors
import Recaman.SmallInversionJoint

namespace Recaman.ThirteenSixSources

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.SmallInversionSources Recaman.FourthSourceFamilies Recaman.SourceFamilyFreeCount

def sixShapes (M m L s : Nat) : Prop :=
    (M=4 ∧ m=1 ∧ L=6 ∧ s=2) ∨ (M=4 ∧ m=1 ∧ L=3 ∧ s=3) ∨
    (M=6 ∧ m=2 ∧ L=5 ∧ s=1) ∨ (M=6 ∧ m=2 ∧ L=6 ∧ s=1) ∨
    (M=3 ∧ m=4 ∧ L=8 ∧ s=1) ∨ (M=3 ∧ m=4 ∧ L=9 ∧ s=1)

private theorem initial_absent (M m L s q i : Nat) (hq : 1≤q)
    (hex : sixShapes M m L s)
    (hbal : (M : Int)+(L : Int)+(i : Int)=(q : Int)+(m : Int)+(s : Int)+1)
    (hkey : ((q : Int)+(m : Int)+(s : Int))^2=
      2*((M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int))+1) : False := by
  have hI : (M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int)≤25 := by
    rcases hex with h|h|h|h|h|h <;> rcases h with ⟨rfl,rfl,rfl,rfl⟩ <;> decide
  have hQ7 : (q : Int)+(m : Int)+(s : Int)≤7 := by
    by_cases hh : (q : Int)+(m : Int)+(s : Int)≤7
    · exact hh
    · have hp:=Int.mul_nonneg (show 0≤(q : Int)+(m : Int)+(s : Int)-8 by omega)
        (show 0≤(q : Int)+(m : Int)+(s : Int)+8 by omega)
      grind only
  rcases hex with h|h|h|h|h|h <;> rcases h with ⟨rfl,rfl,rfl,rfl⟩
  · omega
  · have hv : q=2 ∨ q=3 := by omega
    rcases hv with rfl|rfl <;> omega
  · omega
  · omega
  · omega
  · omega

theorem six_shape_third_one (h M m L s K : Nat) (hs : 1≤s) (hex : sixShapes M m L s) :
    rayCount (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false) K≤1 := by
  have hpoint : ∀ i, Recaman.ThreeNonsuppliedData.localSupply
      (List.replicate h false++List.replicate M true++List.replicate m false++
        List.replicate L true++List.replicate s false++List.replicate i true)=true → i=2 := by
    intro i hi
    rcases (local_third_sources h M m L s i hs).mp hi with ha|ha|ha|ha
    · obtain ⟨q,hq,_,hbal,hkey⟩:=ha
      have hk : runKey (List.replicate q false++List.replicate M true++List.replicate m false++
          List.replicate L true++List.replicate s false)= -2 := by simpa only [List.append_assoc] using hkey
      rw [runKey_five_runs] at hk
      simp only [mass_append,mass_rep_false,mass_replicate_A] at hbal
      exact False.elim (initial_absent M m L s q i hq hex (by omega) (by grind only))
    · obtain ⟨e,he,_,hbal,hkey⟩:=ha
      have hk:=runKey_five_runs 0 e m L s
      simp only [List.replicate_zero,List.nil_append] at hk
      simp only [List.append_assoc] at hk hkey
      rw [hk] at hkey
      simp only [mass_append,mass_rep_false,mass_replicate_A] at hbal
      rcases hex with h|h|h|h|h|h <;> rcases h with ⟨rfl,rfl,rfl,rfl⟩ <;> omega
    · obtain ⟨q,hq,hqm,hbal,hkey⟩:=ha
      have hk : runKey (List.replicate q false++List.replicate L true++List.replicate s false)= -2 := by
        simpa only [List.append_assoc] using hkey
      rw [runKey_S_A_S] at hk
      have hq4 : q=1 ∨ q=2 ∨ q=3 ∨ q=4 := by
        rcases hex with h|h|h|h|h|h <;> rcases h with ⟨rfl,rfl,rfl,rfl⟩ <;> omega
      rcases hq4 with rfl|rfl|rfl|rfl <;>
        rcases hex with h|h|h|h|h|h <;> rcases h with ⟨rfl,rfl,rfl,rfl⟩ <;> omega
    · exact ha
  apply cN_le_one_of_unique
  intro a haK b hbK haP hbP
  rw [hpoint a haP,hpoint b hbP]

end Recaman.ThirteenSixSources
