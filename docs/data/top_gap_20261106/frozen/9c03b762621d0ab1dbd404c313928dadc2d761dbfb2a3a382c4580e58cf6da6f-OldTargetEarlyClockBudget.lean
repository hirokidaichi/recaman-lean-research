import Recaman.OldSourceKeyOrder
import Recaman.LocalSourcePrefixBudget
import Recaman.RayCountFromBase

namespace Recaman.OldTargetEarlyClockBudget

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- All old and small-A-prefix local sources share one early clock band.
Every clock outside it retains a literal witness at or after the cutoff. -/
theorem old_target_early_clock_budget (f : Nat → Bool) (n t B Q T j : Nat)
    (hw : BlockWord (seg f 0 n)) (ht : t<n) (hQB : Q≤B) (hj : 2≤j)
    (hQ : cN (fun x=>f x=true) n Q≤j)
    (hA : ∀ i, i<T → f (n+B+i)=true)
    (hgap : ∀ x, n+B+T≤x → x<n+B+T+j → f x=false)
    (htarget : Win f t (n+B+T+j-t)) :
    cN (EndN f 0) (n+B) T≤(T-j)+cN (EndN f (n+Q)) (n+B) T := by
  apply Recaman.RayCountFromBase.count_with_initial_segment f (n+Q) (n+B) T (T-j)
  intro i hi hband he
  obtain ⟨hAi,r,l,_,hrl,hW⟩ := he
  have hwin : Win f r (n+B+i-r) := by rwa [show n+B+i-r=l by omega]
  have hlate : T≤i+j := by omega
  by_cases hcut : n+Q≤r
  · exact ⟨hAi,r,l,hcut,hrl,hW⟩
  · exfalso
    by_cases hrold : r<n
    · have hp:=Recaman.OldSourceKeyOrder.actual_old_target_prior_clock f n r t B i T j
        hw hrold ht (by omega) hj hA hgap hwin htarget
      have htime:=hp.2
      omega
    · have hp:=Recaman.LocalSourcePrefixBudget.actual_local_source_prefix_A f n t r B i T j
        hw ht (by omega) (by omega) hi hj hlate hA hgap hwin htarget
      have hsplit:=cN_add (fun x=>f x=true) n (r-n) (Q-(r-n))
      rw [show r-n+(Q-(r-n))=Q by omega] at hsplit
      omega

end Recaman.OldTargetEarlyClockBudget
