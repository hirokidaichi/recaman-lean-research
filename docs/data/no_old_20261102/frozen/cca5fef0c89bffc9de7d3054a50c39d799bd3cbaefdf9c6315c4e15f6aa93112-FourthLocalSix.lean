import Recaman.FourthSourceFamilies

namespace Recaman.FourthLocalSix

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.FourthSourceFamilies

/-- Six actual local source families, uniformly in every run length.
The terminal A/S pair shares clock two and costs one rather than two. -/
theorem fourth_local_six (h M m L s U v K : Nat) (hv : 1≤v) :
    rayCount (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false) K≤6 := by
  let A:=sourceAt false h (List.replicate M true++List.replicate m false++List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false)
  let B:=sourceAt true M (List.replicate m false++List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false)
  let C:=sourceAt false m (List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false)
  let D:=sourceAt true L (List.replicate s false++List.replicate U true++List.replicate v false)
  let E:=sourceAt false s (List.replicate U true++List.replicate v false)
  have hc : rayCount (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false) K≤
      cN (fun i=>A i ∨ B i ∨ C i ∨ D i ∨ E i ∨ i=2) 0 K := by
    apply cN_mono
    intro i _ _ hi
    exact (local_fourth_sources h M m L s U v i hv).mp (by simpa only [List.append_assoc] using hi)
  have ha : cN A 0 K≤1 := sourceAt_count_le_one false h _ K
  have hb : cN B 0 K≤1 := sourceAt_count_le_one true M _ K
  have hd : cN C 0 K≤1 := sourceAt_count_le_one false m _ K
  have he : cN D 0 K≤1 := sourceAt_count_le_one true L _ K
  have hf : cN E 0 K≤1 := sourceAt_count_le_one false s _ K
  have h2 : cN (fun i=>i=2) 0 K≤1 := by apply cN_le_one_of_unique; intros; omega
  have h1:=cN_or_le A (fun i=>B i ∨ C i ∨ D i ∨ E i ∨ i=2) K
  have h3:=cN_or_le B (fun i=>C i ∨ D i ∨ E i ∨ i=2) K
  have h4:=cN_or_le C (fun i=>D i ∨ E i ∨ i=2) K
  have h5:=cN_or_le D (fun i=>E i ∨ i=2) K
  have h6:=cN_or_le E (fun i=>i=2) K
  omega

end Recaman.FourthLocalSix
