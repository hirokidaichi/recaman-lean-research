import Recaman.ThreeRunFreeGap

namespace Recaman.FreePrefixCounterexample

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.RunSupplyBudget Recaman.RunClockClassifier Recaman.CapacityEqualityInduction
open Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

def word : List Bool := [true]++List.replicate 6 false++List.replicate 6 true++
  List.replicate 2 false++[true,false]++List.replicate 6 true++List.replicate 4 false++[true]

def f (k : Nat) : Bool := word[k]?.getD false

def supplied (g : Nat → Bool) (k : Nat) : Bool :=
  g k && Recaman.ThreeNonsuppliedData.localSupply (seg g 0 k)

theorem supplied_iff (g : Nat → Bool) (k : Nat) : supplied g k=true ↔ EndN g 0 k := by
  by_cases hg : g k=true
  · simp only [supplied,hg,Bool.true_and]
    simpa only [Nat.sub_zero] using localSupply_seg_iff g 0 k (Nat.zero_le _) hg
  · have hf : g k=false := Bool.eq_false_iff.mpr hg
    simp only [supplied,hf,Bool.false_and,Bool.false_eq_true]
    exact ⟨False.elim,fun he => hg he.1⟩

def boolCount (g : Nat → Bool) (n K : Nat) : Nat :=
  ((List.range K).filter (fun i => g (n+i))).length

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
    boolCount f 1 11=5 ∧ boolCount (supplied f) 1 11=1 ∧
    boolCount f 1 22=13 ∧ boolCount (supplied f) 1 22=3 := by decide

private theorem positive_certificate :
    (List.range 28).all (fun k => decide (k≤1) ||
      decide (boolCount (supplied f) 0 k+1≤boolCount (fun i => !(f i)) 0 k))=true := by decide

/-- A real source/count counterexample to replacing the preceding A
count by preceding free count. It is an abstract sign history satisfying
the local prefix-zero/positive-deficit hypotheses, not all conditions of
the completed C1 setting D or a standard Recaman orbit counterexample. -/
theorem free_before_source_counterexample :
    BlockWord (seg f 0 1) ∧
    cN (EndN f 0) 0 1=cN (fun x => f x=false) 0 1 ∧
    (∀ k, 1<k → k≤27 → cN (EndN f 0) 0 k+1≤cN (fun x => f x=false) 0 k) ∧
    Win f 0 27 ∧ Win f 12 7 ∧ f 27=true ∧ f 19=true ∧
    cN (fun x => f x=true) 1 11=5 ∧
    cN (fun x => f x=true ∧ ¬EndN f 0 x) 1 11=4 ∧
    cN (fun x => f x=true ∧ ¬EndN f 0 x) 1 22=10 := by
  have hc := literal_counts
  have hE1 := count_supplied f 0 1
  have hS1 := count_S f 0 1
  have hA11 := count_bool f 1 11
  have hE11 := count_supplied f 1 11
  have hA22 := count_bool f 1 22
  have hE22 := count_supplied f 1 22
  have hp11 := addition_endable_partition f 1 11
  have hp22 := addition_endable_partition f 1 22
  refine ⟨?_,by omega,?_,?_,?_,by decide,by decide,by omega,by omega,by omega⟩
  · have hs : seg f 0 1=[true] := by decide
    rw [hs]
    exact BlockWord.free BlockWord.nil
  · intro k hk hk27
    have hh := List.all_eq_true.mp positive_certificate k (List.mem_range.mpr (by omega))
    have hn : decide (k≤1)=false := by simp; omega
    rw [hn,Bool.false_or,decide_eq_true_eq] at hh
    rw [count_supplied,count_S]
    exact hh
  · unfold Win
    decide
  · unfold Win
    decide

private theorem literal_interval (s K : Nat) (b : Bool)
    (hc : (List.range K).all (fun i => decide (f (s+i)=b))=true) :
    ∀ x, s≤x → x<s+K → f x=b := by
  intro x hx hxK
  have hh := List.all_eq_true.mp hc (x-s) (List.mem_range.mpr (by omega))
  have hb := of_decide_eq_true hh
  simpa only [Nat.add_sub_cancel' hx] using hb

/-- Nonvacuity/regression control only. The full three-run theorem is
instantiated from independently checked signs, windows and counts;
its free-count conclusion is not used as an input. -/
theorem three_run_bound_replay :
    5≤cN (fun x => f x=true ∧ ¬EndN f 0 x) 1 22 ∧
    cN (fun x => f x=true ∧ ¬EndN f 0 x) 1 22=10 := by
  rcases free_before_source_counterexample with
    ⟨hw,hzero,hpos,hW,hlocal,hAt,hAi,hAcount,hfree,hall⟩
  have hp : seg f 0 1=[true] := by decide
  have hE : EndN f 0 27 := ⟨hAt,0,27,Nat.zero_le _,rfl,hW⟩
  have hb := Recaman.ThreeRunFreeGap.three_run_free_gap_from_zero f 1 6 6 2 1 1 6 4
    [true] (BlockWord.free BlockWord.nil) hp (by decide) (by decide) (by decide) (by decide) (by decide)
    (literal_interval 1 6 false (by decide))
    (by intro i hi; exact literal_interval 7 6 true (by decide) (7+i) (by omega) (by omega))
    (literal_interval 13 2 false (by decide))
    (by intro i hi; exact literal_interval 15 1 true (by decide) (15+i) (by omega) (by omega))
    (literal_interval 16 1 false (by decide))
    (by intro i hi; exact literal_interval 17 6 true (by decide) (17+i) (by omega) (by omega))
    hzero hpos (literal_interval 23 4 false (by decide)) hE
  exact ⟨hb,hall⟩

end Recaman.FreePrefixCounterexample
