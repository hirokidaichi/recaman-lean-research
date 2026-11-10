import Recaman.BlockSameMassSpan

namespace Recaman.OldZeroMassPhaseTwo

open Recaman.BlockSuffixPositivity Recaman.SingleWindowEquality
open Recaman.CapacityEqualityInduction Recaman.LeadingRunSupply

private def atoms : List (List Bool) := [[true],aasW,tripW]
private def bases : List (List Bool) := [[],[true],[true,true],aasW]

private theorem small_base (w : List Bool) (hw : BlockWord w) (hm : mass w≤2) :
    w∈bases := by
  by_cases hz : w=[]
  · rw [hz]; decide
  · have hp := (sufPos_block hw [] w rfl hz).1
    by_cases h1 : mass w=1
    · rw [block_mass_one hw h1]; decide
    · rcases block_mass_two hw (by omega) with hAA|hSA
      · rw [hAA]; decide
      · rw [hSA]; decide

private theorem atom_floor (B : List Bool) (hB : B∈atoms) (j : Nat) :
    -2≤mass (B.take j) := by
  have hcert : atoms.all (fun B => (List.range (B.length+1)).all
      (fun k => decide (-2≤mass (B.take k))))=true := by decide
  let k := min j B.length
  have hk : k≤B.length := Nat.min_le_right _ _
  have hcheck := of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp hcert B hB)
    k (List.mem_range.mpr (by omega)))
  by_cases h : j≤B.length
  · simpa only [k,Nat.min_eq_left h] using hcheck
  · rw [List.take_of_length_le (by omega)]
    simpa only [k,Nat.min_eq_right (show B.length≤j by omega),
      List.take_of_length_le (Nat.le_refl _)] using hcheck

private def phaseWords : List (List Bool) :=
  [[true,false],[false,true],[false,true,true,true,false,false]]

private theorem append_phase_two (w B : List Bool) (hw : BlockWord w) (hB : B∈atoms)
    (ih : ∀ k, mass (w.take k)=0 → (w.take k).length%4=2 → w.take k∈phaseWords)
    (k : Nat) (hm : mass ((w++B).take k)=0) (hmod : ((w++B).take k).length%4=2) :
    (w++B).take k∈phaseWords := by
  by_cases hk : k≤w.length
  · rw [List.take_append_of_le_length hk] at hm hmod ⊢
    exact ih k hm hmod
  · rw [List.take_append,List.take_of_length_le (show w.length≤k by omega)] at hm hmod ⊢
    let j := min (k-w.length) B.length
    have hj : j≤B.length := Nat.min_le_right _ _
    have ht : B.take (k-w.length)=B.take j := by
      dsimp [j]
      by_cases h : k-w.length≤B.length
      · rw [Nat.min_eq_left h]
      · rw [Nat.min_eq_right (by omega),List.take_of_length_le (by omega),
          List.take_of_length_le (Nat.le_refl _)]
    rw [ht] at hm hmod ⊢
    have hl := atom_floor B hB j
    have hb : w∈bases := by
      apply small_base w hw
      rw [mass_append] at hm
      omega
    have hcert : bases.all (fun v => atoms.all (fun x =>
        (List.range (x.length+1)).all (fun r => decide (
          mass (v++x.take r)=0 → (v++x.take r).length%4=2 → v++x.take r∈phaseWords))))=true := by decide
    have hcheck := List.all_eq_true.mp (List.all_eq_true.mp
      (List.all_eq_true.mp hcert w hb) B hB) j (List.mem_range.mpr (by omega))
    exact of_decide_eq_true hcheck hm hmod

/-- A zero-mass BlockWord prefix in phase two has one of three words. The
length-six word has area three; the two length-two words have area ±1. -/
theorem zero_mass_phase_two_prefix (w : List Bool) (hw : BlockWord w) :
    ∀ k, mass (w.take k)=0 → (w.take k).length%4=2 →
      w.take k=[true,false] ∨ w.take k=[false,true] ∨
      w.take k=[false,true,true,true,false,false] := by
  have h : ∀ k, mass (w.take k)=0 → (w.take k).length%4=2 → w.take k∈phaseWords := by
    induction hw with
    | nil => simp
    | free hw ih => exact append_phase_two _ _ hw (by decide) ih
    | aas hw ih => exact append_phase_two _ _ hw (by decide) ih
    | triple hw ih => exact append_phase_two _ _ hw (by decide) ih
  intro k hm hk
  simpa only [phaseWords,List.mem_cons,List.not_mem_nil,or_false] using h k hm hk

end Recaman.OldZeroMassPhaseTwo
