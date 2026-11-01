import Recaman.TenHeadTargetCases

namespace Recaman.TenHeadLocalCount

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.RunClockClassifier
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

def triples : List (Nat × Nat × Nat) :=
  ((List.range 8).flatMap (fun a => (List.range 8).map (fun b => (a+1,b+1,10-(a+1)-(b+1))))).filter
    (fun c => 1≤c.2.2)

def head (c d : Nat × Nat × Nat) : List Bool :=
  List.replicate c.1 false++List.replicate d.1 true++List.replicate c.2.1 false++
    List.replicate d.2.1 true++List.replicate c.2.2 false++List.replicate d.2.2 true

def rows : List ((Nat × Nat × Nat) × (Nat × Nat × Nat)) :=
  (triples.flatMap (fun c => triples.map (fun d => (c,d)))).filter
    (fun cd => areaW (head cd.1 cd.2)= -46 ∨ areaW (head cd.1 cd.2)= -56)

/-- Structural inclusion of every positive three-composition of ten. -/
theorem mem_triples (h m s : Nat) (hh : 1≤h) (hm : 1≤m) (hs : 1≤s)
    (he : h+m+s=10) : (h,m,s)∈triples := by
  apply List.mem_filter.mpr
  refine ⟨?_,by simpa using hs⟩
  apply List.mem_flatMap.mpr
  refine ⟨h-1,List.mem_range.mpr (by omega),?_⟩
  apply List.mem_map.mpr
  refine ⟨m-1,List.mem_range.mpr (by omega),?_⟩
  simp only [show h-1+1=h by omega,show m-1+1=m by omega]
  congr 2
  omega

private theorem checked_local_rows :
    rows.all (fun cd =>
      if areaW (head cd.1 cd.2)= -46
      then decide (rayBoolCount (head cd.1 cd.2++[false]) 5≤2)
      else decide (rayBoolCount (head cd.1 cd.2++[false,false]) 7≤2))=true := by decide

/-- Exhaustive local certificate after the target-derived area pruning.
The two finite rays contain at most two local supply clocks for every
positive three-A-run head with ten A and ten S signs. -/
theorem ten_head_local_count (h M m L s U : Nat)
    (hh : 1≤h) (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hU : 1≤U)
    (hS : h+m+s=10) (hA : M+L+U=10) (B : Int)
    (haz : areaW (head (h,m,s) (M,L,U))= -B) (hB : B=46 ∨ B=56) :
    (B=46 → rayCount (head (h,m,s) (M,L,U)++[false]) 5≤2) ∧
    (B=56 → rayCount (head (h,m,s) (M,L,U)++[false,false]) 7≤2) := by
  have hmem : ((h,m,s),(M,L,U))∈rows := by
    apply List.mem_filter.mpr
    refine ⟨?_,?_⟩
    · apply List.mem_flatMap.mpr
      refine ⟨(h,m,s),mem_triples h m s hh hm hs hS,?_⟩
      exact List.mem_map.mpr ⟨(M,L,U),mem_triples M L U hM hL hU hA,rfl⟩
    · simp only [haz,decide_eq_true_eq]
      rcases hB with h|h <;> omega
  have hc:=List.all_eq_true.mp checked_local_rows _ hmem
  constructor
  · intro he
    have ha : areaW (head (h,m,s) (M,L,U))= -46 := by rw [haz,he]
    simp only [ha,ite_true] at hc
    rw [rayCount_eq_boolCount]
    exact of_decide_eq_true hc
  · intro he
    have ha : ¬areaW (head (h,m,s) (M,L,U))= -46 := by rw [haz,he]; decide
    simp only [ha,ite_false] at hc
    rw [rayCount_eq_boolCount]
    exact of_decide_eq_true hc

end Recaman.TenHeadLocalCount
