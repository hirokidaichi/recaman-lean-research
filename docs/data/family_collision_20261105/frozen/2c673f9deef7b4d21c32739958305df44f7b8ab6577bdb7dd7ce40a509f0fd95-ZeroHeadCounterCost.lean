import Recaman.MomentTargetProfile

namespace Recaman.ZeroHeadCounterCost

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.BlockOldRay Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- Count decomposition on the same zero head and actual target. This
is a reusable bookkeeping input, not a new research claim by itself. -/
theorem counter_count_cost (f : Nat → Bool) (n B t v T j C K : Nat) (w z : List Bool)
    (hpre : seg f 0 n=w) (hz : seg f n B=z) (hmz : mass z=0) (ht : t<n)
    (hC : mass (w.drop t)=(C : Int))
    (hS : ∀ x, n+B≤x → x<n+B+v → f x=false)
    (hA : ∀ k, k<T → f (n+B+v+k)=true)
    (hgap : ∀ x, n+B+v+T≤x → x<n+B+v+T+j → f x=false)
    (htarget : Win f t (n+B+v+T+j-t))
    (hbad : cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (B+v+T)<j+1)
    (hlast : cN (EndN f 0) (n+B+v) T≤K) :
    T+C=v+j+1 ∧ cN (fun x=>f x=true ∧ ¬EndN f 0 x) n B+v+1≤K+C := by
  have hp:=Recaman.MomentTargetProfile.actual_target_word_profile f n t B v T j w z hpre ht hz hS hA hgap htarget
  have hbalance : T+C=v+j+1 := by
    have hh:=hp.1
    simp only [mass_append,hmz,hC,mass_rep_false,mass_replicate_A] at hh
    omega
  let P:=fun x=>f x=true ∧ ¬EndN f 0 x
  have hs0 : cN P (n+B) v=0 := by
    apply cN_zero_of
    intro x hx hxb he
    have hf:=hS x hx hxb
    have ha:=he.1
    rw [hf] at ha
    contradiction
  have ha:=cN_add P n B v
  have hb:=cN_add P n (B+v) T
  have hc:=addition_endable_partition f (n+B+v) T
  rw [count_A_run f (n+B+v) T hA] at hc
  change T=cN (EndN f 0) (n+B+v) T+cN P (n+B+v) T at hc
  change cN P n (B+v+T)<j+1 at hbad
  exact ⟨hbalance,by omega⟩

theorem zero_head_free_pos (f : Nat → Bool) (n B : Nat) (hmz : mass (seg f n B)=0)
    (hpos : cN (EndN f 0) n B+1≤cN (fun x=>f x=false) n B) :
    1≤cN (fun x=>f x=true ∧ ¬EndN f 0 x) n B := by
  have hm:=seg_mass f n B
  have hw:=cN_walk f n B
  have hp:=addition_endable_partition f n B
  omega

end Recaman.ZeroHeadCounterCost
