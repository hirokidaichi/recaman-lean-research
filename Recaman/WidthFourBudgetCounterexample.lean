import Recaman.FloorSupplyFreeBudget
import Recaman.InitialSPaddingPositive

namespace Recaman.WidthFourBudgetCounterexample

open Recaman.InitialSPaddingPositive Recaman.BlockSuffixPositivity Recaman.SingleWindowEquality
open Recaman.CapacityEqualityInduction Recaman.AdditionRankSlack

private def word : List Bool :=
  aasW++[false,false,false,false,true,true,true,true,false,true]

private def f : Nat → Bool := finiteSign word

private theorem supplied (t : Nat) (ht : 4≤t) (ht14 : t<14) :
    EndN f 0 t ↔ t=10 ∨ t=11 ∨ t=13 := by
  have he : t=4 ∨ t=5 ∨ t=6 ∨ t=7 ∨ t=8 ∨ t=9 ∨
      t=10 ∨ t=11 ∨ t=12 ∨ t=13 := by omega
  rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact ⟨fun h => (by decide : f 4≠true) h.1 |>.elim,by simp⟩
  · exact ⟨fun h => (by decide : f 5≠true) h.1 |>.elim,by simp⟩
  · exact ⟨fun h => (by decide : f 6≠true) h.1 |>.elim,by simp⟩
  · exact ⟨fun h => (by decide : f 7≠true) h.1 |>.elim,by simp⟩
  · refine ⟨fun h => ?_,by simp⟩
    have hl := (localSupply_seg_iff f 0 8 (by decide) (by decide)).mpr h
    have hn : Recaman.ThreeNonsuppliedData.localSupply (seg f 0 (8-0))=false := by decide
    rw [hn] at hl
    cases hl
  · refine ⟨fun h => ?_,by simp⟩
    have hl := (localSupply_seg_iff f 0 9 (by decide) (by decide)).mpr h
    have hn : Recaman.ThreeNonsuppliedData.localSupply (seg f 0 (9-0))=false := by decide
    rw [hn] at hl
    cases hl
  · exact ⟨fun _ => Or.inl rfl,fun _ => (localSupply_seg_iff f 0 10 (by decide) (by decide)).mp (by decide)⟩
  · exact ⟨fun _ => Or.inr (Or.inl rfl),fun _ => (localSupply_seg_iff f 0 11 (by decide) (by decide)).mp (by decide)⟩
  · exact ⟨fun h => (by decide : f 12≠true) h.1 |>.elim,by simp⟩
  · exact ⟨fun _ => Or.inr (Or.inr rfl),fun _ => (localSupply_seg_iff f 0 13 (by decide) (by decide)).mp (by decide)⟩

/-- A full width-four and strict positive tail can have five additions
and only two free additions. This falsifies the width-three A budget
with width raised to four. -/
theorem width_four_breaks_double_free :
    BlockWord (seg f 0 4) ∧
    (∀ i, 4≤i → i≤14 → -2≤Fw f i ∧ Fw f i≤2) ∧
    (∀ k, 0<k → k≤10 → cN (EndN f 0) 4 k+1≤cN (fun i => f i=false) 4 k) ∧
    additions f 4 10=5 ∧ free f 4 10=2 := by
  have hWord : seg f 0 4=aasW := by decide
  have hE : cN (EndN f 0) 4 10=3 := by
    rw [cN_congr (EndN f 0) (fun t => t=10∨t=11∨t=13) 4 10
      (fun i hi hik => supplied i hi (by omega))]
    simp [cN]
  have hA : additions f 4 10=5 := by
    simp [additions,cN,f,finiteSign,word,aasW]
  have hfree := additions_split f 4 10
  refine ⟨?_,?_,?_,hA,by omega⟩
  · rw [hWord]
    exact BlockWord.aas BlockWord.nil
  · intro i hi hj
    have he : i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨
        i=10 ∨ i=11 ∨ i=12 ∨ i=13 ∨ i=14 := by omega
    rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  · intro k hk hk10
    by_cases hK : 4≤k
    · have h1 := count_prefix_le (EndN f 0) 4 k 10 hk10
      have h2 := count_prefix_le (fun i => f i=false) 4 4 k hK
      have hS : cN (fun i => f i=false) 4 4=4 := by simp [cN,f,finiteSign,word,aasW]
      omega
    · have hz : cN (EndN f 0) 4 k=0 := by
        apply cN_zero_of
        intro i hi hik h
        rcases (supplied i hi (by omega)).mp h with hs|hs|hs <;> omega
      have h1 := count_prefix_le (fun i => f i=false) 4 1 k (by omega)
      have hS : cN (fun i => f i=false) 4 1=1 := by simp [cN,f,finiteSign,word,aasW]
      omega

end Recaman.WidthFourBudgetCounterexample
