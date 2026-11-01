import Recaman.FourEventFast
import Recaman.PrefixMassBarrier

namespace Recaman.FourEventPruned

open Recaman.LeadingRunSupply
open Recaman.BlockSuffixPositivity
open Recaman.PrefixMassBarrier
open Recaman.FourNonsuppliedData
open Recaman.FourEventFast

theorem stepA_true_admitted (s t : State) (h : stepA s true=some t) :
    Recaman.ThreeNonsuppliedData.localSupply s.word=true ∨
      (s.subtractions<19 ∧ Recaman.ThreeNonsuppliedData.oldSignature s.word=true) := by
  unfold stepA at h
  simp only [ite_true] at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq] at hc
    exact hc.1.1
  · contradiction

theorem macro_true_gap_half_bound (s t : State) (j : Nat)
    (hones : ones s.word≤(s.additions : Int)) (ha : s.additions≤10)
    (h : macroA s j true=some t) : 2*j+2≤s.additions := by
  have hadmit := stepA_true_admitted (gap s j) t h
  have hraw : (Recaman.ThreeNonsuppliedData.localSupply (s.word++List.replicate j false) ||
      Recaman.ThreeNonsuppliedData.oldSignature (s.word++List.replicate j false))=true := by
    by_cases hsat : min 19 (s.subtractions+j)=19
    · have hs : (gap s j).subtractions=19 := by simp [gap,hsat]
      have hw : (gap s j).word=trim (s.word++List.replicate j false) := by simp [gap,hsat]
      rcases hadmit with hl|ho
      · have hc : ones (s.word++List.replicate j false)≤10 := by
          rw [ones_append,ones_replicate_S]
          omega
        rw [hw,four_localSupply_trim _ hc] at hl
        simp [hl]
      · rw [hs] at ho
        omega
    · have hw : (gap s j).word=s.word++List.replicate j false := by simp [gap,hsat]
      rcases hadmit with hl|ho
      · rw [hw] at hl
        simp [hl]
      · rw [hw] at ho
        simp [ho.2]
  have hb := wordSupply_gap_half_bound s.word j hraw
  omega

theorem macro_true_none_of_large_gap (s : State) (j : Nat)
    (hones : ones s.word≤(s.additions : Int)) (ha : s.additions≤10)
    (hj : ¬2*j+2≤s.additions) : macroA s j true=none := by
  cases h : macroA s j true with
  | none => rfl
  | some t => exact False.elim (hj (macro_true_gap_half_bound s t j hones ha h))

-- Reject cheap budget/balance failures before computing a suffix scan.
def budgetStepA (s : State) (e : Bool) : Option State :=
  let an := s.nonsupplied+(if e then 0 else 1)
  if decide (an≤4) &&
      decide (s.subtractions=19 ∨ 1≤(s.subtractions : Int)-(s.additions+1 : Nat)+an) then
    fastStepA s e else none

private theorem guard_option (a b c : Bool) (v : Option State) :
    (if b && c then (if a && b && c then v else none) else none)=
      (if a && b && c then v else none) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem budgetStepA_eq (s : State) (e : Bool) : budgetStepA s e=fastStepA s e := by
  cases e <;> simp only [budgetStepA,fastStepA,ite_true,ite_false]
  · exact guard_option _ _ _ _
  · exact guard_option _ _ _ _

def prunedMacroA (s : State) (j : Nat) (e : Bool) : Option State :=
  if e && !(decide (2*j+2≤s.additions)) then none else budgetStepA (gap s j) e

theorem prunedMacroA_eq (s : State) (j : Nat) (e : Bool)
    (hones : ones s.word≤(s.additions : Int)) (ha : s.additions≤10) :
    prunedMacroA s j e=macroA s j e := by
  cases e
  · simp [prunedMacroA,budgetStepA_eq,fastStepA_eq,macroA]
  · by_cases hj : 2*j+2≤s.additions
    · simp [prunedMacroA,hj,budgetStepA_eq,fastStepA_eq,macroA]
    · simp [prunedMacroA,hj,macro_true_none_of_large_gap s j hones ha hj]

def prunedSuccessors (s : State) : List State :=
  (List.range 20).flatMap fun j => [prunedMacroA s j false,prunedMacroA s j true].filterMap id

theorem successors_eq_pruned (s : State)
    (hones : ones s.word≤(s.additions : Int)) (ha : s.additions≤10) :
    Recaman.FourEventProof.successors s=prunedSuccessors s := by
  simp only [Recaman.FourEventProof.successors,prunedSuccessors,prunedMacroA_eq s _ _ hones ha]

example : (prunedMacroA ⟨[],10,0,3⟩ 20 false).map (fun s => s.additions)=some 11 := by decide

end Recaman.FourEventPruned
