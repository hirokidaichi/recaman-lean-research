import Recaman.SourceCrossSurplus

namespace Recaman.MassTwoPrefixKey

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply Recaman.BlockOldRay
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

theorem mass_two_key_bounds (u : List Bool) (hu : BlockWord u) (hm : mass u=2) :
    -2≤runKey u ∧ runKey u≤0 := by
  rcases block_mass_two hu hm with rfl|rfl <;> decide

/-- A zero-mass prefix before the middle-S source cannot realize the required square key. -/
theorem middle_prefix_key_excluded (u : List Bool) (hu : BlockWord u) (h M p : Nat)
    (hC : mass u=2) (hM : 3≤M)
    (hm : mass (u++(List.replicate h false++List.replicate M true++List.replicate p false))=0) :
    runKey (u++(List.replicate h false++List.replicate M true++List.replicate p false))≠
      2-2*((M : Int)-1)^2 := by
  intro hk
  have hb:=mass_two_key_bounds u hu hC
  have hmass : (h : Int)+(p : Int)=(M : Int)+2 := by
    simp only [mass_append,mass_rep_false,mass_replicate_A,hC] at hm
    omega
  rw [runKey_append,runKey_S_A_S,hC] at hk
  have hs : (cntF (List.replicate h false++List.replicate M true++List.replicate p false) : Int)=
      (h : Int)+(p : Int) := by
    have hc:=cntF_int (List.replicate h false++List.replicate M true++List.replicate p false)
    simp only [List.length_append,List.length_replicate,ones_append,ones_replicate_A,ones_replicate_S] at hc
    omega
  rw [hs] at hk
  have he : 4*(M : Int)*(p : Int)=4*(M : Int)-8-runKey u := by
    rw [hmass] at hk
    grind only
  by_cases hp0 : p=0
  · rw [hp0] at he
    omega
  · have hp:=Int.mul_nonneg (show 0≤(M : Int) by omega) (show 0≤(p : Int)-1 by omega)
    have hid : (M : Int)*((p : Int)-1)=(M : Int)*(p : Int)-(M : Int) := by grind only
    omega

end Recaman.MassTwoPrefixKey
