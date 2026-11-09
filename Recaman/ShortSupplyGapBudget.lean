import Recaman.ShortSourceTriples

namespace Recaman.ShortSupplyGapBudget

open Recaman.AdditionRankSlack Recaman.ShortSourceTriples Recaman.SingleWindowEquality
open Recaman.CapacityEqualityInduction Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.LeadingRunSupply Recaman.LineCapacityPeriodic

/-- The complementary supplied endpoints, counted in the original
history. An endpoint with both a short and an old source counts as short. -/
noncomputable def otherSupplies (f : Nat → Bool) (n K : Nat) : Nat :=
  cN (fun t=>EndN f 0 t ∧ ¬shortEndpoint f n t) n K

theorem original_short_supply_charge (f : Nat → Bool) (n K : Nat) :
    2*cN (shortEndpoint f n) n K≤free f n K+otherSupplies f n K ∧
    2*additions f n K≤3*(free f n K+otherSupplies f n K) := by
  have hpart := cN_split (P := EndN f 0) (Q := shortEndpoint f n) (s := n) K
  have heq := cN_congr
    (P := fun t => EndN f 0 t ∧ shortEndpoint f n t) (Q := shortEndpoint f n) (s := n) K
    (fun t _ _=>⟨fun h=>h.2,fun h=>⟨short_endpoint_supplied f n t h,h⟩⟩)
  rw [heq] at hpart
  change cN (EndN f 0) n K=cN (shortEndpoint f n) n K+otherSupplies f n K at hpart
  have hA:=additions_split f n K
  have h3:=short_endpoints_triple_budget f n K
  omega

/-- In any run count, the original A budget for the final S gap must
be paid by free A and by supplies that do not have an interior SAA source. -/
theorem original_gap_other_supply_budget (f : Nat → Bool) (n a b j : Nat) (w : List Bool)
    (hw : BlockWord w) (hpre : seg f 0 n=w++List.replicate a true)
    (hnb : n<b) (hS : ∀ t, b≤t → t<b+j → f t=false) (htarget : EndN f 0 (b+j)) :
    4*(j+1)≤3*(free f n (b-n)+otherSupplies f n (b-n)) := by
  have hA:=supplied_after_S_gap_half_bound f n a b j hw hpre hnb hS htarget
  have he : ones (seg f n (b-n))=(additions f n (b-n) : Int) :=
    ones_seg_eq_count f n (b-n)
  rw [he] at hA
  have hcharge:=(original_short_supply_charge f n (b-n)).2
  omega

theorem counter_needs_other_supplies (f : Nat → Bool) (n a b j : Nat) (w : List Bool)
    (hw : BlockWord w) (hpre : seg f 0 n=w++List.replicate a true)
    (hnb : n<b) (hS : ∀ t, b≤t → t<b+j → f t=false) (htarget : EndN f 0 (b+j))
    (hcounter : free f n (b-n)≤j) :
    j+4≤3*otherSupplies f n (b-n) := by
  have h:=original_gap_other_supply_budget f n a b j w hw hpre hnb hS htarget
  omega

theorem at_most_one_other_supply_free_gap (f : Nat → Bool) (n a b j : Nat) (w : List Bool)
    (hw : BlockWord w) (hpre : seg f 0 n=w++List.replicate a true)
    (hnb : n<b) (hS : ∀ t, b≤t → t<b+j → f t=false) (htarget : EndN f 0 (b+j))
    (hOther : otherSupplies f n (b-n)≤1) :
    j+1≤free f n (b-n) := by
  have h:=original_gap_other_supply_budget f n a b j w hw hpre hnb hS htarget
  omega

end Recaman.ShortSupplyGapBudget
