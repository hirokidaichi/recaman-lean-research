import Recaman.InitialSOneHeadPositive
import Recaman.InitialSPaddingPositive

namespace Recaman.PaddedInitialSTrimBoundary

open Recaman.InitialSPaddingPositive Recaman.AdditionRankSlack
open Recaman.BlockSuffixPositivity Recaman.SingleWindowEquality Recaman.CapacityEqualityInduction

private def f : Nat → Bool := finiteSign (aasW++List.replicate 4 false++List.replicate 4 true)
private def g : Nat → Bool := finiteSign (aasW++List.replicate 3 false++List.replicate 4 true)

private theorem f_supplied (t : Nat) (ht : 4≤t) (ht12 : t<12) :
    EndN f 0 t ↔ t=10 ∨ t=11 := by
  have hh : t=4 ∨ t=5 ∨ t=6 ∨ t=7 ∨ t=8 ∨ t=9 ∨ t=10 ∨ t=11 := by omega
  rcases hh with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first
  | exact ⟨fun h => (by decide : f _≠true) h.1 |>.elim,by simp⟩
  | (refine ⟨fun _ => by simp,fun _ => (localSupply_seg_iff f 0 _ (by decide) (by decide)).mp (by decide)⟩)
  | (refine ⟨fun h => ?_,by simp⟩
     have hl := (localSupply_seg_iff f 0 _ (by decide) (by decide)).mpr h
     revert hl
     decide)

private theorem g_supplied (t : Nat) (ht : 4≤t) (ht11 : t<11) :
    EndN g 0 t ↔ t=9 := by
  have hh : t=4 ∨ t=5 ∨ t=6 ∨ t=7 ∨ t=8 ∨ t=9 ∨ t=10 := by omega
  rcases hh with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first
  | exact ⟨fun h => (by decide : g _≠true) h.1 |>.elim,by simp⟩
  | (refine ⟨fun _ => by simp,fun _ => (localSupply_seg_iff g 0 _ (by decide) (by decide)).mp (by decide)⟩)
  | (refine ⟨fun h => ?_,by simp⟩
     have hl := (localSupply_seg_iff g 0 _ (by decide) (by decide)).mpr h
     revert hl
     decide)

/-- A single S deletion after the same original BlockWord loses an
actual target and increases free, despite the low ceiling and both
relative positive domains. The global-initial-S hypothesis is material. -/
theorem padded_prefix_one_S_trim_changes_actual_free :
    BlockWord (seg f 0 4) ∧ seg g 0 4=seg f 0 4 ∧
    (∀ i, 4≤i → i<8 → f i=false) ∧
    (∀ i, 4≤i → i<7 → g i=false) ∧
    (∀ i, i≤4 → f (8+i)=g (7+i)) ∧
    (∀ i, 8≤i → i≤12 → Fw f i≤Fw f 8+4) ∧
    (∀ k, 0<k → k≤8 → cN (EndN f 0) 4 k+1≤cN (fun i => f i=false) 4 k) ∧
    (∀ k, 0<k → k≤7 → cN (EndN g 0) 4 k+1≤cN (fun i => g i=false) 4 k) ∧
    EndN f 0 11 ∧ ¬EndN g 0 10 ∧ free f 4 8=2 ∧ free g 4 7=3 := by
  have hpre : seg f 0 4=aasW := by decide
  have hE : cN (EndN f 0) 4 8=2 := by
    rw [cN_congr (EndN f 0) (fun t => t=10 ∨ t=11) 4 8
      (fun t ht htK => f_supplied t ht (by omega))]
    simp [cN]
  have hgE : cN (EndN g 0) 4 7=1 := by
    rw [cN_congr (EndN g 0) (fun t => t=9) 4 7
      (fun t ht htK => g_supplied t ht (by omega))]
    simp [cN]
  have hA : additions f 4 8=4 := by simp [additions,cN,f,finiteSign,aasW]
  have hgA : additions g 4 7=4 := by simp [additions,cN,g,finiteSign,aasW]
  have hFs := additions_split f 4 8
  have hgFs := additions_split g 4 7
  refine ⟨by rw [hpre]; exact BlockWord.aas BlockWord.nil,by decide,?_,?_,?_,?_,?_,?_,?_,?_,by omega,by omega⟩
  · intro i hi hj
    have hh : i=4 ∨ i=5 ∨ i=6 ∨ i=7 := by omega
    rcases hh with rfl|rfl|rfl|rfl <;> decide
  · intro i hi hj
    have hh : i=4 ∨ i=5 ∨ i=6 := by omega
    rcases hh with rfl|rfl|rfl <;> decide
  · intro i hi
    have hh : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 := by omega
    rcases hh with rfl|rfl|rfl|rfl|rfl <;> decide
  · intro i hi hj
    have hh : i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 := by omega
    rcases hh with rfl|rfl|rfl|rfl|rfl <;> decide
  · intro k hk hk8
    by_cases hk4 : 4≤k
    · have he := count_prefix_le (EndN f 0) 4 k 8 hk8
      have hs := count_prefix_le (fun i => f i=false) 4 4 k hk4
      have hS4 : cN (fun i => f i=false) 4 4=4 := by simp [cN,f,finiteSign,aasW]
      omega
    · have he0 : cN (EndN f 0) 4 k=0 := by
        apply cN_zero_of
        intro i hi hiK he
        rcases (f_supplied i hi (by omega)).mp he with h|h <;> omega
      have hs := count_prefix_le (fun i => f i=false) 4 1 k (by omega)
      have hS1 : cN (fun i => f i=false) 4 1=1 := by simp [cN,f,finiteSign,aasW]
      omega
  · intro k hk hk7
    by_cases hk3 : 3≤k
    · have he := count_prefix_le (EndN g 0) 4 k 7 hk7
      have hs := count_prefix_le (fun i => g i=false) 4 3 k hk3
      have hS3 : cN (fun i => g i=false) 4 3=3 := by simp [cN,g,finiteSign,aasW]
      omega
    · have he0 : cN (EndN g 0) 4 k=0 := by
        apply cN_zero_of
        intro i hi hiK he
        have hh := (g_supplied i hi (by omega)).mp he
        omega
      have hs := count_prefix_le (fun i => g i=false) 4 1 k (by omega)
      have hS1 : cN (fun i => g i=false) 4 1=1 := by simp [cN,g,finiteSign,aasW]
      omega
  · exact (f_supplied 11 (by omega) (by omega)).mpr (Or.inr rfl)
  · intro he
    have hh := (g_supplied 10 (by omega) (by omega)).mp he
    omega

end Recaman.PaddedInitialSTrimBoundary
