import Recaman.DelayedSourcePrefix
import Recaman.OldTargetEarlyClockBudget

namespace Recaman.DelayedOldTargetBudget

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- A delay-sensitive common clock budget for all sources before a
literal cutoff, retaining every later actual window at that cutoff. -/
theorem delayed_clock_budget (f : Nat → Bool) (n t B Q T j A0 : Nat)
    (hw : BlockWord (seg f 0 n)) (ht : t<n) (hQB : Q≤B) (hj : 2≤j)
    (hC : 2≤mass (seg f t (n-t))) (hQ : cN (fun x=>f x=true) n Q≤A0)
    (hA : ∀ i, i<T → f (n+B+i)=true)
    (hgap : ∀ x, n+B+T≤x → x<n+B+T+j → f x=false)
    (htarget : Win f t (n+B+T+j-t)) :
    cN (EndN f 0) (n+B) T≤max (T-j) (A0+T-(2*j+1))+cN (EndN f (n+Q)) (n+B) T := by
  apply Recaman.RayCountFromBase.count_with_initial_segment f (n+Q) (n+B) T (max (T-j) (A0+T-(2*j+1)))
  intro i hi hband he
  obtain ⟨hAi,r,l,_,hrl,hW⟩ := he
  have hwin : Win f r (n+B+i-r) := by rwa [show n+B+i-r=l by omega]
  have hearly : T-j≤i := Nat.le_trans (Nat.le_max_left ..) hband
  have hdelay : A0+T-(2*j+1)≤i := Nat.le_trans (Nat.le_max_right ..) hband
  have hlate : T≤i+j := by omega
  by_cases hcut : n+Q≤r
  · exact ⟨hAi,r,l,hcut,hrl,hW⟩
  · exfalso
    by_cases hrold : r<n
    · have hp:=Recaman.OldSourceKeyOrder.actual_old_target_prior_clock f n r t B i T j
        hw hrold ht (by omega) hj hA hgap hwin htarget
      have htime:=hp.2
      omega
    · have hp:=Recaman.DelayedSourcePrefix.actual_delay_source_prefix_A f n t r B i T j
        hw hC ht (by omega) (by omega) hi hj hlate hA hgap hwin htarget
      have hsplit:=cN_add (fun x=>f x=true) n (r-n) (Q-(r-n))
      rw [show r-n+(Q-(r-n))=Q by omega] at hsplit
      omega

theorem delayed_word_budget (f : Nat → Bool) (n t B T j A0 : Nat) (a z : List Bool)
    (hw : BlockWord (seg f 0 n)) (ht : t<n) (hj : 2≤j) (hC : 2≤mass (seg f t (n-t)))
    (hword : seg f n B=a++z) (hcut : ones a≤(A0 : Int))
    (hA : ∀ i, i<T → f (n+B+i)=true)
    (hgap : ∀ x, n+B+T≤x → x<n+B+T+j → f x=false)
    (htarget : Win f t (n+B+T+j-t)) :
    cN (EndN f 0) (n+B) T≤max (T-j) (A0+T-(2*j+1))+rayCount z T := by
  obtain ⟨hlen,hAcount,hRay⟩:=Recaman.OldTargetEarlyClockBudget.prefix_word_ray_measure
    f n B T a z hword hA
  have hcnt : cN (fun x=>f x=true) n a.length≤A0 := by omega
  have h := delayed_clock_budget f n t B a.length T j A0 hw ht hlen hj hC hcnt hA hgap htarget
  rwa [hRay] at h

end Recaman.DelayedOldTargetBudget
