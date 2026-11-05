import Recaman.DelayedOldTargetBudget
import Recaman.ThirdSeparatorClock

namespace Recaman.FourthDelayedWitness

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.DelayedOldTargetBudget Recaman.FourthSourceFamilies Recaman.ThirdSeparatorClock

/-- Outside the delayed band after the third S separator, only the
terminal A/S pair supplies a final-ray clock. -/
theorem fourth_delayed_pair_support (f : Nat → Bool) (n t B h M m L s U v T j i : Nat)
    (hw : BlockWord (seg f 0 n)) (ht : t<n) (hj : 2≤j) (hv : 1≤v)
    (hC : 2≤mass (seg f t (n-t)))
    (hword : seg f n B=List.replicate h false++(List.replicate M true++
      List.replicate m false++List.replicate L true++List.replicate s false++
      List.replicate U true++List.replicate v false))
    (hA : ∀ i, i<T → f (n+B+i)=true)
    (hgap : ∀ x, n+B+T≤x → x<n+B+T+j → f x=false)
    (htarget : Win f t (n+B+T+j-t))
    (hi : i<T) (hband : max (T-j) (M+L+T-(2*j+1))≤i) (he : EndN f 0 (n+B+i)) :
    i=2 := by
  let a:=List.replicate h false++List.replicate M true++List.replicate m false++
    List.replicate L true++List.replicate s false
  let z:=List.replicate U true++List.replicate v false
  have ha : ones a≤((M+L : Nat) : Int) := by
    simp only [a,ones_append,ones_replicate_A,ones_replicate_S,Int.zero_add,Int.add_zero,Int.natCast_add]
    omega
  have hs : seg f n B=a++z := by simpa only [a,z,List.append_assoc] using hword
  have h := delayed_word_support f n t B T j (M+L) i a z hw ht hj hC hs ha hA hgap htarget hi hband he
  exact (Recaman.AdjacentRunSupply.local_A_S_clock_iff U v i hv).mp h

/-- At the cutoff after a specified A in the second run, the source
uses at most the remaining k A signs there, or the later separator/pair. -/
theorem fourth_second_A_tail_support (f : Nat → Bool) (n t B h M m L s U v T j i k : Nat)
    (hw : BlockWord (seg f 0 n)) (ht : t<n) (hj : 2≤j) (hv : 1≤v) (hk : k<L)
    (hC : 2≤mass (seg f t (n-t)))
    (hword : seg f n B=List.replicate h false++(List.replicate M true++
      List.replicate m false++List.replicate L true++List.replicate s false++
      List.replicate U true++List.replicate v false))
    (hA : ∀ i, i<T → f (n+B+i)=true)
    (hgap : ∀ x, n+B+T≤x → x<n+B+T+j → f x=false)
    (htarget : Win f t (n+B+T+j-t))
    (hi : i<T) (hband : max (T-j) (M+(L-k-1)+T-(2*j+1))≤i)
    (he : EndN f 0 (n+B+i)) :
    sourceAt true k (List.replicate s false++(List.replicate U true++List.replicate v false)) i ∨
    sourceAt false s (List.replicate U true++List.replicate v false) i ∨ i=2 := by
  let a:=List.replicate h false++List.replicate M true++List.replicate m false++
    List.replicate (L-k-1) true
  let z:=List.replicate k true++(List.replicate s false++(List.replicate U true++List.replicate v false))
  have htake : (List.replicate L true).take (L-k)=List.replicate (L-k) true := by
    rw [List.take_replicate,Nat.min_eq_left (by omega)]
  have hdrop : (List.replicate L true).drop (L-k)=List.replicate k true := by
    rw [List.drop_replicate,show L-(L-k)=k by omega]
  have hlast : List.replicate (L-k) true=List.replicate (L-k-1) true++[true] := by
    rw [←List.replicate_succ',show L-k-1+1=L-k by omega]
  have hrep : List.replicate L true=(List.replicate (L-k-1) true++[true])++List.replicate k true := by
    rw [←hlast,←htake,←hdrop,List.take_append_drop]
  have ha : ones a≤((M+(L-k-1) : Nat) : Int) := by
    simp only [a,ones_append,ones_replicate_A,ones_replicate_S,Int.zero_add,Int.add_zero,Int.natCast_add]
    omega
  have hs : seg f n B=(a++[true])++z := by
    simpa only [a,z,hrep,List.append_assoc] using hword
  have h := delayed_after_A_word_support f n t B T j (M+(L-k-1)) i a z hw ht hj hC hs ha hA hgap htarget hi hband he
  exact second_A_or_third_separator_or_pair k s U v i hv h

theorem fourth_third_S_tail_support (f : Nat → Bool) (n t B h M m L s U v T j i : Nat)
    (hw : BlockWord (seg f 0 n)) (ht : t<n) (hj : 2≤j) (hv : 1≤v) (hL : 1≤L)
    (hC : 2≤mass (seg f t (n-t)))
    (hword : seg f n B=List.replicate h false++(List.replicate M true++
      List.replicate m false++List.replicate L true++List.replicate s false++
      List.replicate U true++List.replicate v false))
    (hA : ∀ i, i<T → f (n+B+i)=true)
    (hgap : ∀ x, n+B+T≤x → x<n+B+T+j → f x=false)
    (htarget : Win f t (n+B+T+j-t))
    (hi : i<T) (hband : max (T-j) (M+L-1+T-(2*j+1))≤i)
    (he : EndN f 0 (n+B+i)) :
    sourceAt false s (List.replicate U true++List.replicate v false) i ∨ i=2 := by
  have hb:=fourth_second_A_tail_support f n t B h M m L s U v T j i 0
    hw ht hj hv (by omega) hC hword hA hgap htarget hi
    (by simpa only [Nat.sub_zero,show M+(L-1)=M+L-1 by omega] using hband) he
  rcases hb with h|h
  · obtain ⟨q,hq,hq0,_,_⟩:=h
    omega
  · exact h

end Recaman.FourthDelayedWitness
