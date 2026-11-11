import Recaman.PrefixMassBarrier

namespace Recaman.FirstSOneFreePrefix

open Recaman.PrefixMassBarrier Recaman.BlockSuffixPositivity Recaman.LeadingRunSupply
open Recaman.SingleWindowEquality Recaman.CapacityEqualityInduction

/-- In the weakened model requiring only an initial S, one original free
addition permits only one addition in total. Full prefix positivity is
not required; the all-run half-gap bound excludes every earlier supply. -/
theorem first_S_one_free_additions (f : Nat → Bool) (n a K : Nat)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n=w++List.replicate a true)
    (hFirst : f n=false) (hFree : cN (fun i => f i=true ∧ ¬EndN f 0 i) n K≤1) :
    cN (fun i => f i=true) n K=cN (fun i => f i=true ∧ ¬EndN f 0 i) n K ∧
      cN (fun i => f i=true) n K≤1 := by
  revert hFree
  induction K with
  | zero => intro _; simp [cN]
  | succ K ih =>
    intro hFree
    have hm := count_prefix_le (fun i => f i=true ∧ ¬EndN f 0 i) n K (K+1) (by omega)
    obtain ⟨ihEq,ihOne⟩ := ih (by omega)
    by_cases hA : f (n+K)=true
    · have hK : 0<K := by
        by_cases h0 : K=0
        · rw [h0,Nat.add_zero,hFirst] at hA
          cases hA
        · omega
      have hNo : ¬EndN f 0 (n+K) := by
        intro he
        have hTwo := supplied_after_S_gap_half_bound f n a (n+K) 0 hw hpre (by omega)
          (by intro i hi hj; omega) (by simpa only [Nat.add_zero] using he)
        rw [Nat.add_sub_cancel_left,ones_seg_eq_count] at hTwo
        change (2 : Int)≤(cN (fun i => f i=true) n K : Int) at hTwo
        omega
      rw [cN_succ_pos (fun i => f i=true ∧ ¬EndN f 0 i) n K ⟨hA,hNo⟩] at hFree
      rw [cN_succ_pos (fun i => f i=true) n K hA,
        cN_succ_pos (fun i => f i=true ∧ ¬EndN f 0 i) n K ⟨hA,hNo⟩]
      exact ⟨by omega,by omega⟩
    · rw [cN_succ_neg (fun i => f i=true) n K hA,
        cN_succ_neg (fun i => f i=true ∧ ¬EndN f 0 i) n K (fun h => hA h.1)]
      exact ⟨ihEq,ihOne⟩

end Recaman.FirstSOneFreePrefix
