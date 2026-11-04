import Recaman.UnitDefectCost
import Recaman.FourRunSourceBase

namespace Recaman.OldTargetFreeAccounting

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- An arbitrary mixed tail retains the exact old-target mass charge.
Only original-base endpoint positivity is needed; no run or head-mass
assumption, source truncation, or BlockWord reset is made. -/
theorem old_target_free_charge (f : Nat → Bool) (n t B j C : Nat) (ht : t≤n)
    (hC : mass (seg f t (n-t))=(C : Int))
    (hpos : cN (EndN f 0) n B+1≤cN (fun x=>f x=false) n B)
    (hgap : ∀ x, n+B≤x → x<n+B+j → f x=false)
    (htarget : Win f t (n+B+j-t)) :
    j+2≤cN (fun x=>f x=true ∧ ¬EndN f 0 x) n B+C := by
  have hmt : mass (seg f t (n+B+j-t))=1 := by
    rw [seg_mass]
    have he:=htarget.2.1
    rw [show t+(n+B+j-t)=n+B+j by omega] at he ⊢
    omega
  have hs : seg f t (n+B+j-t)=seg f t (n-t)++seg f n B++List.replicate j false := by
    rw [show n+B+j-t=(n-t+B)+j by omega,seg_add,
      show t+(n-t+B)=n+B by omega,seg_false f (n+B) j hgap,
      seg_add,show t+(n-t)=n by omega]
  rw [hs,mass_append,mass_append,hC,mass_rep_false] at hmt
  have hf:=Recaman.UnitDefectCost.mass_free_charge f n B hpos
  omega

/-- Arbitrary original Int p, same P2 target and actual Endable counts.
Absolute zero and endpoint positivity supply the relative count internally. -/
theorem old_target_free_charge_int (e : Int → Bool) (p : Int) (n t B j C : Nat) (ht : t≤n)
    (hC : mass (segment e (p+(t : Int)) (n-t))=(C : Int))
    (hzero : endableCount e p n=subtractionCount e p n)
    (hpos : endableCount e p (n+B)+1≤subtractionCount e p (n+B))
    (hgap : ∀ x, n+B≤x → x<n+B+j → e (p+(x : Int))=false)
    (htarget : P2 (past e (p+((n+B+j : Nat) : Int)) (n+B+j-t))) :
    j+2≤countP (fun x=>e x=true ∧ ¬Endable e p x) (p+(n : Int)) B+C := by
  simp only [endableCount_shift,subtractionCount_shift] at hzero hpos
  simp only [nonsupplied_count_shift]
  have hrel : cN (EndN (fun k=>e (p+(k : Int))) 0) n B+1≤
      cN (fun k=>e (p+(k : Int))=false) n B := by
    have he:=cN_add (EndN (fun k=>e (p+(k : Int))) 0) 0 n B
    have hs:=cN_add (fun k=>e (p+(k : Int))=false) 0 n B
    simp only [Nat.zero_add] at he hs
    omega
  have hW : Win (fun k=>e (p+(k : Int))) t (n+B+j-t) := by
    apply Recaman.FourRunSourceBase.P2_shifted_window e p t (n+B+j-t) (by omega)
    simpa only [show t+(n+B+j-t)=n+B+j by omega] using htarget
  rw [segment_seg e p (p+(t : Int)) t rfl] at hC
  exact old_target_free_charge (fun k=>e (p+(k : Int))) n t B j C ht hC hrel hgap hW

/-- Mass one is eliminated at every run count by accounting alone.
This corollary is not an additional source-collision mechanism. -/
theorem unit_old_target_gap (f : Nat → Bool) (n t B j : Nat) (ht : t≤n)
    (hC : mass (seg f t (n-t))=1)
    (hpos : cN (EndN f 0) n B+1≤cN (fun x=>f x=false) n B)
    (hgap : ∀ x, n+B≤x → x<n+B+j → f x=false)
    (htarget : Win f t (n+B+j-t)) :
    j+1≤cN (fun x=>f x=true ∧ ¬EndN f 0 x) n B := by
  have hc:=old_target_free_charge f n t B j 1 ht hC hpos hgap htarget
  omega

theorem old_target_counter_mass (f : Nat → Bool) (n t B j C : Nat) (ht : t≤n)
    (hC : mass (seg f t (n-t))=(C : Int))
    (hpos : cN (EndN f 0) n B+1≤cN (fun x=>f x=false) n B)
    (hgap : ∀ x, n+B≤x → x<n+B+j → f x=false)
    (htarget : Win f t (n+B+j-t))
    (hbad : cN (fun x=>f x=true ∧ ¬EndN f 0 x) n B<j+1) : 2≤C := by
  have hc:=old_target_free_charge f n t B j C ht hC hpos hgap htarget
  omega

end Recaman.OldTargetFreeAccounting
