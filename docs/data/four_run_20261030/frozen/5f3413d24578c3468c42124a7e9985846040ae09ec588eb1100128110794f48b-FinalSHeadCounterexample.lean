import Recaman.FreePrefixCounterexample

namespace Recaman.FinalSHeadCounterexample

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.RunSupplyBudget Recaman.RunClockClassifier Recaman.CapacityEqualityInduction
open Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.FreePrefixCounterexample (supplied supplied_iff boolCount)

/-- The old prefix is A. The four A-run lengths are 1,4,6,10;
S lengths 6,4,1,2 and the final S gap is8. -/
def word : List Bool := [true]++List.replicate 6 false++[true]++
  List.replicate 4 false++List.replicate 4 true++[false]++
  List.replicate 6 true++List.replicate 2 false++List.replicate 10 true++
  List.replicate 8 false++[true]

def f (k : Nat) : Bool := word[k]?.getD false

private theorem count_bool (g : Nat → Bool) (n : Nat) : ∀ K,
    cN (fun i => g i=true) n K=boolCount g n K
  | 0 => rfl
  | K+1 => by
    have ih := count_bool g n K
    cases hg : g (n+K)
    · rw [cN_succ_neg (fun i => g i=true) n K (by simpa using hg)]
      simpa [boolCount,List.range_succ,List.filter_append,hg] using ih
    · rw [cN_succ_pos (fun i => g i=true) n K (by simpa using hg)]
      simp [boolCount,List.range_succ,List.filter_append,hg] at ih ⊢
      exact ih

private theorem count_supplied (g : Nat → Bool) (n K : Nat) :
    cN (EndN g 0) n K=boolCount (supplied g) n K := by
  have he : cN (EndN g 0) n K=cN (fun i => supplied g i=true) n K := by
    apply cN_congr
    intro i _ _
    exact (supplied_iff g i).symm
  exact he.trans (count_bool (supplied g) n K)

private theorem count_S (g : Nat → Bool) (n K : Nat) :
    cN (fun x => g x=false) n K=boolCount (fun i => !(g i)) n K := by
  have he : cN (fun x => g x=false) n K=cN (fun i => (g i).not=true) n K := by
    apply cN_congr
    intro i _ _
    cases g i <;> simp
  exact he.trans (count_bool (fun i => !(g i)) n K)


private theorem literal_counts :
    boolCount (supplied f) 0 1=0 ∧ boolCount (fun i => !(f i)) 0 1=0 ∧
    boolCount f 1 24=11 ∧ boolCount (supplied f) 1 24=3 ∧
    boolCount f 1 34=21 ∧ boolCount (supplied f) 1 34=4 := by decide

private theorem positive_certificate :
    (List.range 44).all (fun k => decide (k≤1) ||
      decide (boolCount (supplied f) 0 k+1≤boolCount (fun i => !(f i)) 0 k))=true := by decide

/-- A counterexample to charging j+1 entirely to the first three A runs,
even when the final-band local source is in the final S separator.
The full-tail free count17 is above9, so this does not refute the full
four-run free-gap claim or the completed C1 setting. -/
theorem final_S_head_counterexample :
    BlockWord (seg f 0 1) ∧
    cN (EndN f 0) 0 1=cN (fun x => f x=false) 0 1 ∧
    (∀ k, 1<k → k≤43 → cN (EndN f 0) 0 k+1≤cN (fun x => f x=false) 0 k) ∧
    Win f 0 43 ∧ Win f 24 3 ∧ f 43=true ∧ f 27=true ∧ f 24=false ∧
    (10 : Nat)≤2+8 ∧
    cN (fun x => f x=true ∧ ¬EndN f 0 x) 1 24=8 ∧
    cN (fun x => f x=true ∧ ¬EndN f 0 x) 1 34=17 := by
  have hc := literal_counts
  have hE1 := count_supplied f 0 1
  have hS1 := count_S f 0 1
  have hA24 := count_bool f 1 24
  have hE24 := count_supplied f 1 24
  have hA34 := count_bool f 1 34
  have hE34 := count_supplied f 1 34
  have hp24 := addition_endable_partition f 1 24
  have hp34 := addition_endable_partition f 1 34
  refine ⟨?_,by omega,?_,?_,?_,by decide,by decide,by decide,by decide,by omega,by omega⟩
  · have hs : seg f 0 1=[true] := by decide
    rw [hs]
    exact BlockWord.free BlockWord.nil
  · intro k hk hk43
    have hh := List.all_eq_true.mp positive_certificate k (List.mem_range.mpr (by omega))
    have hn : decide (k≤1)=false := by simp; omega
    rw [hn,Bool.false_or,decide_eq_true_eq] at hh
    rw [count_supplied,count_S]
    exact hh
  · unfold Win
    decide
  · unfold Win
    decide

end Recaman.FinalSHeadCounterexample
