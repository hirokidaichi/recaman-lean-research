import Recaman.MixedPrefixDistinctRadius
import Recaman.InitialSPaddingPositive

namespace Recaman.ReversedClockActualControl

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- A nonempty actual example: prefix S2 A4 has exactly three free A,
while the outer primitive source uses clock0 and the inner source clock2. -/
theorem actual_reversed_clock_example :
    ∃ f : Nat → Bool,
      seg f 0 7=[false,false,true,true,true,true,false] ∧
      (∀ k, 0<k → k≤6 → cN (EndN f 0) 0 k+1≤cN (fun x=>f x=false) 0 k) ∧
      cN (fun x=>f x=true ∧ ¬EndN f 0 x) 0 6=3 ∧
      EndN f 0 7 ∧ EndN f 0 9 := by
  let v:=[false,false,true,true,true,true,false]
  let f:=Recaman.InitialSPaddingPositive.finiteSign v
  let p:=[false,false,true,true,true,true]
  have hpreS : seg f 0 2=List.replicate 2 false := by decide
  have hsegp : seg f 0 6=p := by decide
  have hS (x : Nat) (hx : x<2) : f x=false := by
    have hc : x=0 ∨ x=1 := by omega
    rcases hc with rfl|rfl <;> decide
  have hA (x : Nat) (hx : x<4) : f (2+x)=true := by
    have hc : x=0 ∨ x=1 ∨ x=2 ∨ x=3 := by omega
    rcases hc with rfl|rfl|rfl|rfl <;> decide
  have hES : cN (EndN f 0) 0 2=0 := by
    apply cN_zero_of
    intro x hx hx2 he
    have ha:=he.1
    rw [hS x (by omega)] at ha
    cases ha
  have hEAray:=endable_A_run_count f 2 4 (List.replicate 2 false) hpreS hA
  have hRay:=rayCount_const_append false 2 [] 4
  simp only [List.append_nil,rayCount_nil] at hRay
  have hEA : cN (EndN f 0) 2 4≤1 := by omega
  have hEadd:=cN_add (EndN f 0) 0 2 4
  simp only [Nat.zero_add,Nat.reduceAdd] at hEadd
  have hEupper : cN (EndN f 0) 0 6≤1 := by omega
  have hlocal : Recaman.ThreeNonsuppliedData.localSupply (seg f 0 4)=true := by decide
  have hend4 : EndN f 0 4 := (localSupply_seg_iff f 0 4 (by decide) (by decide)).mp hlocal
  have hE4:=cN_succ_pos (EndN f 0) 0 4 (by simpa only [Nat.zero_add] using hend4)
  simp only [Nat.zero_add,Nat.reduceAdd] at hE4
  have hE56:=count_prefix_le (EndN f 0) 0 5 6 (by decide)
  have hElower : 1≤cN (EndN f 0) 0 6 := by omega
  have hS2:=cntF_seg f 0 2
  rw [hpreS,cntF_replicate_S] at hS2
  have hpos : ∀ k, 0<k → k≤6 → cN (EndN f 0) 0 k+1≤cN (fun x=>f x=false) 0 k := by
    intro k hk hk6
    by_cases hk2 : k≤2
    · have he:=count_prefix_le (EndN f 0) 0 k 2 hk2
      have hc:=cntF_seg f 0 k
      rw [seg_false f 0 k (by intro x hx hxk; exact hS x (by omega)),cntF_replicate_S] at hc
      omega
    · have he:=count_prefix_le (EndN f 0) 0 k 6 hk6
      have hs:=count_prefix_le (fun x=>f x=false) 0 2 k (by omega)
      omega
  have hones:=ones_seg_eq_count f 0 6
  have hop : ones (seg f 0 6)=4 := by decide
  have hpart:=addition_endable_partition f 0 6
  have hfree : cN (fun x=>f x=true ∧ ¬EndN f 0 x) 0 6=3 := by omega
  have hlast (r : Nat) (hr : r≤max 2 0) : f (7+r)=true := by
    exact Recaman.InitialSPaddingPositive.finiteSign_after v r
  obtain ⟨hir,hi12,hj17,hend9,hend7⟩:=
    Recaman.MixedPrefixDistinctRadius.actual_distinct_small_free_clock_radius f 0 6 7 2 0 [] p [false]
      BlockWord.nil rfl hsegp hpos (by omega) (by decide) hlast
      (by decide) (by decide) (by decide) (by decide) (by decide)
  exact ⟨f,by decide,hpos,hfree,hend7,hend9⟩

end Recaman.ReversedClockActualControl
