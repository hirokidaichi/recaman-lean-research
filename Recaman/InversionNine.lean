import Recaman.SmallInversionJoint

namespace Recaman.InversionNine

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.SmallInversionSources Recaman.FourthSourceFamilies Recaman.SourceFamilyFreeCount

theorem third_local_one (h M m L s K : Nat)
    (hM : 2≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s)
    (hI : (M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int)≤9) :
    rayCount (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false) K≤1 := by
  have hp : ∀ i, Recaman.ThreeNonsuppliedData.localSupply
      (List.replicate h false++List.replicate M true++List.replicate m false++
        List.replicate L true++List.replicate s false++List.replicate i true)=true → i=2 := by
    intro i hi
    rcases (local_third_sources h M m L s i hs).mp hi with ha|ha|ha|ha
    · obtain ⟨q,hq,_,_,hkey⟩:=ha
      have hk : runKey (List.replicate q false++List.replicate M true++List.replicate m false++
          List.replicate L true++List.replicate s false)= -2 := by simpa only [List.append_assoc] using hkey
      rw [runKey_five_runs] at hk
      have heq : ((q : Int)+(m : Int)+(s : Int))^2=
          2*((M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int))+1 := by grind only
      have hQ3 : 3≤(q : Int)+(m : Int)+(s : Int) := by omega
      have hQ4 : (q : Int)+(m : Int)+(s : Int)≤4 := by
        by_cases hh : (q : Int)+(m : Int)+(s : Int)≤4
        · exact hh
        · have hn:=Int.mul_nonneg (show 0≤(q : Int)+(m : Int)+(s : Int)-5 by omega)
            (show 0≤(q : Int)+(m : Int)+(s : Int)+5 by omega)
          grind only
      have hpa:=Int.mul_nonneg (show 0≤(M : Int)-2 by omega) (show 0≤(m : Int)+(s : Int) by omega)
      have hpb:=Int.mul_nonneg (show 0≤(L : Int)-1 by omega) (show 0≤(s : Int) by omega)
      have hI5 : 5≤(M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int) := by grind only
      have hv : (q : Int)+(m : Int)+(s : Int)=3 ∨ (q : Int)+(m : Int)+(s : Int)=4 := by omega
      rcases hv with hh|hh <;> rw [hh] at heq <;> omega
    · have hc:=small_inversion_first_A M m L s i (by omega) hm hL hs (by omega) ha
      rcases hc with hc|⟨rfl,rfl,rfl,rfl,_⟩
      · exact hc
      · omega
    · have hc:=small_inversion_second_S M m L s i (by omega) hm hL hs (by omega) ha
      rcases hc with hc|⟨rfl,rfl,hm2,_⟩
      · exact hc
      · have hp:=Int.mul_nonneg (show 0≤(M : Int)-2 by omega) (show 0≤(m : Int)+1 by omega)
        grind only
    · exact ha
  apply cN_le_one_of_unique
  intro a haK b hbK haP hbP
  have hh:=hp a haP
  have hh':=hp b hbP
  omega

theorem second_local_one (h M m L s : Nat)
    (hM : 2≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s)
    (hI : (M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int)≤9) :
    rayCount (List.replicate h false++List.replicate M true++List.replicate m false) L≤1 := by
  have hnot : ¬(M=4 ∧ m=1 ∧ 3≤L) := by
    rintro ⟨rfl,rfl,hL3⟩
    have hp:=Int.mul_nonneg (show 0≤(L : Int)-3 by omega) (show 0≤(s : Int) by omega)
    grind only
  apply cN_le_one_of_unique
  intro a haL b hbL haP hbP
  have ca:=Recaman.SmallInversionJoint.second_local_clock h M m L s a (by omega) hm hL hs (by omega) haL haP
  have cb:=Recaman.SmallInversionJoint.second_local_clock h M m L s b (by omega) hm hL hs (by omega) hbL hbP
  rcases ca with ca|ca <;> rcases cb with cb|cb <;> omega

end Recaman.InversionNine
