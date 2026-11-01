import Recaman.SmallInversionSources
import Recaman.RunClockClassifier

namespace Recaman.SmallInversionJoint

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.SmallInversionSources Recaman.FourthSourceFamilies Recaman.SourceFamilyFreeCount

private theorem second_numbers (M m L s q i : Int)
    (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hq : 1≤q)
    (hi : 0≤i) (hiL : i<L) (hI : M*(m+s)+L*s≤16)
    (hbal : M+i=q+m+1) (hkey : (q+m)^2=2*(M*m)+1) :
    i=2 ∨ (M=4 ∧ m=1 ∧ i=0) := by
  have hp:=Int.mul_nonneg (show 0≤s-1 by omega) (show 0≤M+L by omega)
  have hbound : M*m+M+L≤16 := by grind only
  have hQ5 : q+m≤5 := by
    by_cases hh : q+m≤5
    · exact hh
    · have hn:=Int.mul_nonneg (show 0≤q+m-6 by omega) (show 0≤q+m+6 by omega)
      grind only
  have hv : q+m=2 ∨ q+m=3 ∨ q+m=4 ∨ q+m=5 := by omega
  have hQ3 : q+m=3 := by
    rcases hv with h|h|h|h
    · rw [h] at hkey; omega
    · exact h
    · rw [h] at hkey; omega
    · rw [h] at hkey; omega
  have hMm : M*m=4 := by rw [hQ3] at hkey; omega
  have hm2 : m=1 ∨ m=2 := by omega
  rcases hm2 with rfl|rfl
  · right; exact ⟨by omega,rfl,by omega⟩
  · left; omega

theorem second_local_clock (h M m L s i : Nat)
    (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s)
    (hI : (M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int)≤16)
    (hi : i<L) (he : Recaman.ThreeNonsuppliedData.localSupply
      (List.replicate h false++List.replicate M true++List.replicate m false++List.replicate i true)=true) :
    i=2 ∨ (M=4 ∧ m=1 ∧ i=0) := by
  have hc:=Recaman.RunClockClassifier.secondClock_sound h M m i hm he
  simp only [Recaman.RunClockClassifier.secondClock,decide_eq_true_eq] at hc
  rcases hc with hc|hc
  · exact Or.inl hc
  · have hn:=second_numbers (M : Int) (m : Int) (L : Int) (s : Int)
      ((i : Int)+(M : Int)-(m : Int)-1) (i : Int)
      (by omega) (by omega) (by omega) (by omega) hc.1 (by omega) (by omega)
      hI (by omega) (by grind only)
    rcases hn with hn|hn
    · left; omega
    · right; omega

theorem exceptional_third_one (h M m L s K : Nat)
    (hM : M=4) (hm : m=1) (hL : 3≤L) (hs : 1≤s)
    (hI : (M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int)≤16) :
    rayCount (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false) K≤1 := by
  have hp : ∀ i, Recaman.ThreeNonsuppliedData.localSupply
      (List.replicate h false++List.replicate M true++List.replicate m false++
        List.replicate L true++List.replicate s false++List.replicate i true)=true → i=2 := by
    intro i hi
    rcases (local_third_sources h M m L s i hs).mp hi with ha|ha|ha|ha
    · obtain ⟨q,hq,_,hbal,hkey⟩:=ha
      have hk : runKey (List.replicate q false++List.replicate M true++List.replicate m false++
          List.replicate L true++List.replicate s false)= -2 := by
        simpa only [List.append_assoc] using hkey
      rw [runKey_five_runs] at hk
      simp only [mass_append,mass_rep_false,mass_replicate_A] at hbal
      have heq : ((q : Int)+(m : Int)+(s : Int))^2=
          2*((M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int))+1 := by grind only
      have hlo : 6≤(q : Int)+(m : Int)+(s : Int) := by omega
      have hn:=Int.mul_nonneg (show 0≤(q : Int)+(m : Int)+(s : Int)-6 by omega)
        (show 0≤(q : Int)+(m : Int)+(s : Int)+6 by omega)
      grind only
    · have hc:=small_inversion_first_A M m L s i (by omega) (by omega) (by omega) hs hI ha
      rcases hc with hc|hc <;> omega
    · have hc:=small_inversion_second_S M m L s i (by omega) (by omega) (by omega) hs hI ha
      rcases hc with hc|hc <;> omega
    · exact ha
  apply cN_le_one_of_unique
  intro a haK b hbK haP hbP
  have hh:=hp a haP
  have hh':=hp b hbP
  omega

/-- The same inversion constrains both rays, so their separate maxima
cannot be added independently. All initial-S sources remain admitted. -/
theorem small_inversion_joint_count (h M m L s K : Nat)
    (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s)
    (hI : (M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int)≤16) :
    rayCount (List.replicate h false++List.replicate M true++List.replicate m false) L+
      rayCount (List.replicate h false++List.replicate M true++List.replicate m false++
        List.replicate L true++List.replicate s false) K≤3 := by
  by_cases hex : M=4 ∧ m=1 ∧ 3≤L
  · have ha:=rayCount_S_A_S h M m L
    have hb:=exceptional_third_one h M m L s K hex.1 hex.2.1 hex.2.2 hs hI
    omega
  · have ha : rayCount (List.replicate h false++List.replicate M true++List.replicate m false) L≤1 := by
      apply cN_le_one_of_unique
      intro a haL b hbL haP hbP
      have ca:=second_local_clock h M m L s a hM hm hL hs hI (by omega) haP
      have cb:=second_local_clock h M m L s b hM hm hL hs hI (by omega) hbP
      rcases ca with ca|ca <;> rcases cb with cb|cb
      · omega
      · exact False.elim (hex ⟨cb.1,cb.2.1,by omega⟩)
      · exact False.elim (hex ⟨ca.1,ca.2.1,by omega⟩)
      · omega
    have hb:=small_inversion_third_local_two h M m L s K hM hm hL hs hI
    omega

end Recaman.SmallInversionJoint
