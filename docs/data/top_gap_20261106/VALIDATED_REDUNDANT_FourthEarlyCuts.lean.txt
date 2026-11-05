import Recaman.OldTargetEarlyClockBudget
import Recaman.AdjacentRunSupply

namespace Recaman.FourthEarlyCuts

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.OldTargetEarlyClockBudget Recaman.AdjacentRunSupply

/-- Three literal cutoffs for the same final ray. The old and discarded
local sources share the early band, and the residual A/S pair costs one. -/
theorem fourth_early_cuts (f : Nat → Bool) (n t B h M m L s U v T j : Nat)
    (hw : BlockWord (seg f 0 n)) (ht : t<n) (hj : 2≤j) (hv : 1≤v)
    (hword : seg f n B=List.replicate h false++(List.replicate M true++
      List.replicate m false++List.replicate L true++List.replicate s false++
      List.replicate U true++List.replicate v false))
    (hA : ∀ i, i<T → f (n+B+i)=true)
    (hgap : ∀ x, n+B+T≤x → x<n+B+T+j → f x=false)
    (htarget : Win f t (n+B+T+j-t)) :
    cN (EndN f 0) (n+B) T≤(T-j)+5 ∧
    (M≤j → cN (EndN f 0) (n+B) T≤(T-j)+3) ∧
    (M+L≤j → cN (EndN f 0) (n+B) T≤(T-j)+1) := by
  let z:=List.replicate U true++List.replicate v false
  have hpair : rayCount z T≤1 := rayCount_A_S_le_one U v T hv
  have hcut (a x : List Bool) (ha : ones a≤(j : Int)) (he : seg f n B=a++x) :
      cN (EndN f 0) (n+B) T≤(T-j)+rayCount x T :=
    old_target_early_word_budget f n t B T j a x hw ht hj he ha hA hgap htarget
  refine ⟨?_,?_,?_⟩
  · let r := [(true,M),(false,m),(true,L),(false,s)]
    have he := hcut (List.replicate h false) (runWord r++z)
      (by simp only [ones_replicate_S]; omega)
      (by simpa only [r,z,runWord,List.append_nil,List.append_assoc] using hword)
    have hr:=run_prefix_ray_budget r z T
    change rayCount (runWord r++z) T≤4+rayCount z T at hr
    omega
  · intro hM
    let a := List.replicate h false++List.replicate M true++List.replicate m false
    let r := [(true,L),(false,s)]
    have ha : ones a≤(j : Int) := by
      simp only [a,ones_append,ones_replicate_A,ones_replicate_S]
      omega
    have he := hcut a (runWord r++z) ha
      (by simpa only [a,r,z,runWord,List.append_nil,List.append_assoc] using hword)
    have hr:=run_prefix_ray_budget r z T
    change rayCount (runWord r++z) T≤2+rayCount z T at hr
    omega
  · intro hML
    let a := List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false
    have ha : ones a≤(j : Int) := by
      simp only [a,ones_append,ones_replicate_A,ones_replicate_S]
      omega
    have he:=hcut a z ha (by simpa only [a,z,List.append_assoc] using hword)
    omega

end Recaman.FourthEarlyCuts
