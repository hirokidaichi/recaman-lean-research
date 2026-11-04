import Recaman.ZeroHeadCounterCost

namespace Recaman.UnitDefectCost

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- Actual positivity charges the head mass at the original base. -/
theorem mass_free_charge (f : Nat → Bool) (n B : Nat)
    (hpos : cN (EndN f 0) n B+1≤cN (fun x=>f x=false) n B) :
    mass (seg f n B)+1≤(cN (fun x=>f x=true ∧ ¬EndN f 0 x) n B : Int) := by
  have hm:=seg_mass f n B
  have hw:=cN_walk f n B
  have hp:=addition_endable_partition f n B
  omega

/-- Same-base counter accounting needs no zero-head assumption. -/
theorem counter_cost (f : Nat → Bool) (n B v T j K : Nat)
    (hT : T=j+1)
    (hA : ∀ k, k<T → f (n+B+v+k)=true)
    (hbad : cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (B+v+T)<j+1)
    (hlast : cN (EndN f 0) (n+B+v) T≤K) :
    cN (fun x=>f x=true ∧ ¬EndN f 0 x) n B<K := by
  let P:=fun x=>f x=true ∧ ¬EndN f 0 x
  have ha:=cN_add P n B v
  have hb:=cN_add P n (B+v) T
  have hc:=addition_endable_partition f (n+B+v) T
  rw [count_A_run f (n+B+v) T hA] at hc
  change T=cN (EndN f 0) (n+B+v) T+cN P (n+B+v) T at hc
  change cN P n (B+v+T)<j+1 at hbad
  simp only [Nat.add_assoc] at ha hb hc hlast hbad ⊢
  change cN P n B<K
  omega

end Recaman.UnitDefectCost
