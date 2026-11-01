import Recaman.NoOldLocalFive

namespace Recaman.NoOldLocalFour

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.FourthSourceFamilies Recaman.NoOldLocalFive

/-- Initial-S sources are absent; first-A and third-S sources merge into
clocks0/2. Only the second-S and second-A source families remain separate.
No length, area or old-history enumeration is used. -/
theorem target_local_count_four (u : List Bool) (hu : BlockWord u) (hcu : mass u=3)
    (h M m L s U R K : Nat) (hR : 5≤R) (hzero : M+L+U=h+m+s)
    (hS15 : h+m+s≤15) (hbudget : M≤R+1) (B : Int)
    (hB : runKey (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true)= -2*B)
    (hkeyTarget : runKey u=2*B-12*((h : Int)+(m : Int)+(s : Int))-18-2*(R : Int)^2) :
    rayCount (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true++List.replicate 3 false) K≤4 := by
  let P:=fun i : Nat=>i=0 ∨ i=2
  let Q:=sourceAt false m (List.replicate L true++List.replicate s false++List.replicate U true++List.replicate 3 false)
  let A:=sourceAt true L (List.replicate s false++List.replicate U true++List.replicate 3 false)
  have hc : rayCount (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true++List.replicate 3 false) K≤
      cN (fun i=>P i ∨ Q i ∨ A i) 0 K := by
    apply cN_mono
    intro i _ _ hi
    have hh:=target_local_five_sources u hu hcu h M m L s U R i hR hzero hS15 hbudget B hB hkeyTarget
      (by simpa only [List.append_assoc] using hi)
    rcases hh with h0|hQ|hA|hS|h2
    · exact Or.inl (Or.inl h0)
    · exact Or.inr (Or.inl hQ)
    · exact Or.inr (Or.inr hA)
    · obtain ⟨q,hq,hqs,hbal,hkey⟩:=hS
      have hi02:=Recaman.ShortGapSourceClocks.tail_S_small_gap_clock q U 3 i hq (by decide) (by decide)
        (by simpa only [List.append_assoc] using hbal)
        (by simpa only [List.append_assoc] using hkey)
      exact Or.inl hi02
    · exact Or.inl (Or.inr h2)
  have hp : cN P 0 K≤2 := zero_two_count K
  have hq : cN Q 0 K≤1 := sourceAt_count_le_one false m _ K
  have ha : cN A 0 K≤1 := sourceAt_count_le_one true L _ K
  have ho1:=cN_or_le P (fun i=>Q i ∨ A i) K
  have ho2:=cN_or_le Q A K
  omega

end Recaman.NoOldLocalFour
