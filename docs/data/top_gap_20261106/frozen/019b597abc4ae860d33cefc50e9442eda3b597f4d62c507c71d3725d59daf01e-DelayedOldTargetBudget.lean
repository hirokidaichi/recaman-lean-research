import Recaman.DelayedSourcePrefix
import Recaman.OldTargetEarlyClockBudget

namespace Recaman.DelayedOldTargetBudget

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- Outside the common band, the original supply retains a witness at
or after the cutoff. The bound is on every prefix strictly before it. -/
theorem delayed_source_after_cut (f : Nat → Bool) (n t B Q T j A0 i : Nat)
    (hw : BlockWord (seg f 0 n)) (ht : t<n) (hQB : Q≤B) (hj : 2≤j)
    (hC : 2≤mass (seg f t (n-t))) (hQ : ∀ k, k<Q → cN (fun x=>f x=true) n k≤A0)
    (hA : ∀ i, i<T → f (n+B+i)=true)
    (hgap : ∀ x, n+B+T≤x → x<n+B+T+j → f x=false)
    (htarget : Win f t (n+B+T+j-t))
    (hi : i<T) (hband : max (T-j) (A0+T-(2*j+1))≤i)
    (he : EndN f 0 (n+B+i)) : EndN f (n+Q) (n+B+i) := by
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
      have hprefix:=hQ (r-n) (by omega)
      omega

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
  apply delayed_source_after_cut f n t B Q T j A0 i hw ht hQB hj hC _ hA hgap htarget hi hband he
  intro k hk
  have heq:=cN_add (fun x=>f x=true) n k (Q-k)
  rw [show k+(Q-k)=Q by omega] at heq
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

private theorem local_word_at_clock (f : Nat → Bool) (n B T i : Nat) (a z : List Bool)
    (hword : seg f n B=a++z) (hA : ∀ i, i<T → f (n+B+i)=true) (hi : i<T)
    (he : EndN f (n+a.length) (n+B+i)) :
    Recaman.ThreeNonsuppliedData.localSupply (z++List.replicate i true)=true := by
  have hlen : a.length≤B := by
    have hl:=congrArg List.length hword
    rw [seg_length,List.length_append] at hl
    omega
  have hd:=seg_drop f n B a.length hlen
  rw [hword,List.drop_left] at hd
  have hAi : seg f (n+B) i=List.replicate i true := by
    apply seg_A
    intro k hk hki
    simpa only [Nat.add_sub_cancel' hk] using hA (k-(n+B)) (by omega)
  have hs : seg f (n+a.length) (n+B+i-(n+a.length))=z++List.replicate i true := by
    rw [show n+B+i-(n+a.length)=(B-a.length)+i by omega,seg_add,
      show n+a.length+(B-a.length)=n+B by omega,←hd,hAi]
  have h:=localSupply_seg_iff f (n+a.length) (n+B+i) (by omega) (hA i hi)
  rw [hs] at h
  exact h.mpr he

theorem delayed_word_support (f : Nat → Bool) (n t B T j A0 i : Nat) (a z : List Bool)
    (hw : BlockWord (seg f 0 n)) (ht : t<n) (hj : 2≤j) (hC : 2≤mass (seg f t (n-t)))
    (hword : seg f n B=a++z) (hcut : ones a≤(A0 : Int))
    (hA : ∀ i, i<T → f (n+B+i)=true)
    (hgap : ∀ x, n+B+T≤x → x<n+B+T+j → f x=false)
    (htarget : Win f t (n+B+T+j-t))
    (hi : i<T) (hband : max (T-j) (A0+T-(2*j+1))≤i)
    (he : EndN f 0 (n+B+i)) :
    Recaman.ThreeNonsuppliedData.localSupply (z++List.replicate i true)=true := by
  obtain ⟨hlen,hAcount,_⟩:=Recaman.OldTargetEarlyClockBudget.prefix_word_ray_measure f n B T a z hword hA
  apply local_word_at_clock f n B T i a z hword hA hi
  apply delayed_source_after_cut f n t B a.length T j A0 i hw ht hlen hj hC _ hA hgap htarget hi hband he
  intro k hk
  have heq:=cN_add (fun x=>f x=true) n k (a.length-k)
  rw [show k+(a.length-k)=a.length by omega] at heq
  omega

/-- At a cutoff immediately after an A sign, every earlier start
has at most the A count *before* that last sign. -/
theorem delayed_after_A_word_support (f : Nat → Bool) (n t B T j A0 i : Nat) (a z : List Bool)
    (hw : BlockWord (seg f 0 n)) (ht : t<n) (hj : 2≤j) (hC : 2≤mass (seg f t (n-t)))
    (hword : seg f n B=(a++[true])++z) (hcut : ones a≤(A0 : Int))
    (hA : ∀ i, i<T → f (n+B+i)=true)
    (hgap : ∀ x, n+B+T≤x → x<n+B+T+j → f x=false)
    (htarget : Win f t (n+B+T+j-t))
    (hi : i<T) (hband : max (T-j) (A0+T-(2*j+1))≤i)
    (he : EndN f 0 (n+B+i)) :
    Recaman.ThreeNonsuppliedData.localSupply (z++List.replicate i true)=true := by
  obtain ⟨hlen,_,_⟩:=Recaman.OldTargetEarlyClockBudget.prefix_word_ray_measure f n B T (a++[true]) z hword hA
  obtain ⟨_,hAcount,_⟩:=Recaman.OldTargetEarlyClockBudget.prefix_word_ray_measure f n B T a ([true]++z)
    (by simpa only [List.append_assoc] using hword) hA
  apply local_word_at_clock f n B T i (a++[true]) z hword hA hi
  apply delayed_source_after_cut f n t B (a++[true]).length T j A0 i hw ht hlen hj hC _ hA hgap htarget hi hband he
  intro k hk
  simp only [List.length_append,List.length_cons,List.length_nil,Nat.zero_add] at hk
  have heq:=cN_add (fun x=>f x=true) n k (a.length-k)
  rw [show k+(a.length-k)=a.length by omega] at heq
  omega

end Recaman.DelayedOldTargetBudget
