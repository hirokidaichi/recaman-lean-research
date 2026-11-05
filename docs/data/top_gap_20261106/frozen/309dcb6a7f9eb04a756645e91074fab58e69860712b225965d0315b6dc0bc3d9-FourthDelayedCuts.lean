import Recaman.DelayedOldTargetBudget
import Recaman.AdjacentRunSupply

namespace Recaman.FourthDelayedCuts

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.DelayedOldTargetBudget Recaman.AdjacentRunSupply

/-- The second and third separator cuts retain the delay cost of the
sources discarded before them. -/
theorem fourth_delayed_cuts (f : Nat → Bool) (n t B h M m L s U v T j : Nat)
    (hw : BlockWord (seg f 0 n)) (ht : t<n) (hj : 2≤j) (hv : 1≤v)
    (hC : 2≤mass (seg f t (n-t)))
    (hword : seg f n B=List.replicate h false++(List.replicate M true++
      List.replicate m false++List.replicate L true++List.replicate s false++
      List.replicate U true++List.replicate v false))
    (hA : ∀ i, i<T → f (n+B+i)=true)
    (hgap : ∀ x, n+B+T≤x → x<n+B+T+j → f x=false)
    (htarget : Win f t (n+B+T+j-t)) :
    cN (EndN f 0) (n+B) T≤max (T-j) (M+T-(2*j+1))+3 ∧
    cN (EndN f 0) (n+B) T≤max (T-j) (M+L+T-(2*j+1))+1 := by
  let z:=List.replicate U true++List.replicate v false
  have hpair : rayCount z T≤1 := rayCount_A_S_le_one U v T hv
  constructor
  · let a:=List.replicate h false++List.replicate M true++List.replicate m false
    let r:=[(true,L),(false,s)]
    have hsplit : seg f n B=a++(runWord r++z) := by
      simpa only [a,r,z,runWord,List.append_nil,List.append_assoc] using hword
    have hcount : ones a≤(M : Int) := by
      simp only [a,ones_append,ones_replicate_A,ones_replicate_S,Int.zero_add,Int.add_zero]
      omega
    have he := delayed_word_budget f n t B T j M a (runWord r++z) hw ht hj hC hsplit hcount hA hgap htarget
    have hr := run_prefix_ray_budget r z T
    change rayCount (runWord r++z) T≤2+rayCount z T at hr
    omega
  · let a:=List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false
    have hsplit : seg f n B=a++z := by simpa only [a,z,List.append_assoc] using hword
    have hcount : ones a≤((M+L : Nat) : Int) := by
      simp only [a,ones_append,ones_replicate_A,ones_replicate_S,Int.zero_add,Int.add_zero,Int.natCast_add]
      omega
    have he := delayed_word_budget f n t B T j (M+L) a z hw ht hj hC hsplit hcount hA hgap htarget
    omega

end Recaman.FourthDelayedCuts
