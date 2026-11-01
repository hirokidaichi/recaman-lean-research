import Recaman.InitialSeparatorTrim

namespace Recaman.OldContextBudget

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.BlockOldRay Recaman.ThreeRunSupplyBudget
open Recaman.SeparatorSupplyReset Recaman.SeparatorTailFreeGap
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- An actual old window under a total future A budget can only use a short
suffix of the original padded BlockWord. No walk-depth bound is assumed. -/
theorem old_window_budget_radius (f : Nat → Bool) (n a t b B : Nat)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n=w++List.replicate a true)
    (htn : t<n) (hnb : n<b) (hwin : Win f t (b-t))
    (hbudget : ones (seg f n (b-n))≤(B : Int)) :
    2*((n-t : Nat) : Int)≤5*((B : Int)-1) := by
  have hc := old_window_count_barrier f n a t b hw hpre htn hnb hwin
  have hm := mass_eq (seg f n (b-n))
  rw [seg_mass,seg_length,show n+(b-n)=b by omega] at hm
  have hf := hwin.2.1
  rw [show t+(b-t)=b by omega] at hf
  have hd := block_prefix_suffix_length_bound f n a t hw hpre (by omega)
  omega

/-- The radius is derived from the A budget, rather than chosen as an
experimental length cutoff. Both local and old actual starts are retained. -/
theorem endable_budget_old_prefix_trim (f : Nat → Bool) (n a b B : Nat)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n=w++List.replicate a true)
    (hnb : n≤b) (hB : 1≤B) (hbudget : ones (seg f n (b-n))≤(B : Int)) :
    EndN f 0 b ↔ EndN f (n-(5*(B-1)/2)) b := by
  constructor
  · intro he
    by_cases hbn : b=n
    · subst b
      have hn := no_window_after_S_run f 0 n a 0 hw hpre (by intro i hi hj; omega)
      simp only [Nat.zero_add,Nat.add_zero] at hn
      exact False.elim (hn he)
    · obtain ⟨hA,t,k,ht0,htk,hwin⟩ := he
      have htq : n-(5*(B-1)/2)≤t := by
        by_cases htn : t<n
        · have hw' : Win f t (b-t) := by simpa only [show b-t=k by have hk:=hwin.1; omega] using hwin
          have hr := old_window_budget_radius f n a t b B hw hpre htn (by omega) hw' hbudget
          omega
        · omega
      exact ⟨hA,t,k,htq,htk,hwin⟩
  · exact end_mono f 0 (n-(5*(B-1)/2)) b (Nat.zero_le _)

private theorem ones_take_bound (x : List Bool) (k : Nat) : ones (x.take k)≤ones x := by
  have h := ones_append (x.take k) (x.drop k)
  rw [List.take_append_drop] at h
  have hd := ones_bounds (x.drop k)
  omega

/-- All clocks use the same old suffix radius, including an empty prefix. -/
theorem endable_budget_prefix_trim (f : Nat → Bool) (n a B : Nat) (x : List Bool)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n=w++List.replicate a true)
    (hword : seg f n x.length=x) (hB : 1≤B) (hbudget : ones x≤(B : Int))
    (k : Nat) (hk : k≤x.length) :
    EndN f 0 (n+k) ↔ EndN f (n-(5*(B-1)/2)) (n+k) := by
  have hs := seg_take f n x.length k hk
  rw [hword] at hs
  have ho := ones_take_bound x k
  apply endable_budget_old_prefix_trim f n a (n+k) B hw hpre (by omega) hB
  rw [Nat.add_sub_cancel_left,←hs]
  omega

/-- Counts are preserved only after proving the actual pointwise equivalence. -/
theorem old_prefix_budget_counts (f : Nat → Bool) (n a B : Nat) (x : List Bool)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n=w++List.replicate a true)
    (hword : seg f n x.length=x) (hB : 1≤B) (hbudget : ones x≤(B : Int))
    (k : Nat) (hk : k≤x.length) :
    cN (EndN f 0) n k=cN (EndN f (n-(5*(B-1)/2))) n k ∧
    cN (fun i => f i=true ∧ ¬EndN f 0 i) n k=
      cN (fun i => f i=true ∧ ¬EndN f (n-(5*(B-1)/2)) i) n k := by
  have heq : ∀ i, n≤i → i<n+k →
      (EndN f 0 i ↔ EndN f (n-(5*(B-1)/2)) i) := by
    intro i hi hik
    have h := endable_budget_prefix_trim f n a B x hw hpre hword hB hbudget (i-n) (by omega)
    simpa only [Nat.add_sub_cancel' hi] using h
  constructor
  · apply cN_congr
    exact heq
  · apply cN_congr
    intro i hi hik
    exact and_congr_right (fun _ => not_congr (heq i hi hik))

/-- The retained old prefix remains a genuine BlockWord, and every future
actual supply/free count is transported to the same shifted history. -/
theorem budget_context_rebase (f : Nat → Bool) (n a B : Nat) (x : List Bool)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n=w++List.replicate a true)
    (hword : seg f n x.length=x) (hB : 1≤B) (hbudget : ones x≤(B : Int)) :
    let q:=n-(5*(B-1)/2)
    let g:=fun i => f (q+i)
    BlockWord (seg g 0 (n-q)) ∧ n-q≤5*(B-1)/2 ∧
    seg g (n-q) x.length=x ∧
    (∀ k, k≤x.length → (EndN f 0 (n+k) ↔ EndN g 0 (n-q+k))) ∧
    (∀ k, k≤x.length →
      cN (EndN f 0) n k=cN (EndN g 0) (n-q) k ∧
      cN (fun i => f i=true ∧ ¬EndN f 0 i) n k=
        cN (fun i => g i=true ∧ ¬EndN g 0 i) (n-q) k) := by
  dsimp only
  let q:=n-(5*(B-1)/2)
  have hqn : q≤n := by dsimp [q]; omega
  have hqn' : q+(n-q)=n := by omega
  have hfull : BlockWord (seg f 0 n) := by
    rw [hpre]
    exact block_append hw (block_replicate_A a)
  have hsplit := suffix_split f 0 n q (Nat.zero_le _) (by omega)
  simp only [Nat.zero_add,Nat.sub_zero] at hsplit
  have hblock := block_suffix hfull (seg f 0 q) (seg f q (n-q)) hsplit.symm
  have hgpre : seg (fun i => f (q+i)) 0 (n-q)=seg f q (n-q) := by
    simpa only [Nat.add_zero] using seg_nat_shift f q 0 (n-q)
  have hgword : seg (fun i => f (q+i)) (n-q) x.length=x := by
    rw [seg_nat_shift,hqn',hword]
  have heq : ∀ k, k≤x.length →
      (EndN f 0 (n+k) ↔ EndN (fun i => f (q+i)) 0 (n-q+k)) := by
    intro k hk
    have h := endable_budget_prefix_trim f n a B x hw hpre hword hB hbudget k hk
    have ht := endN_nat_shift f q 0 (n-q+k)
    rw [Nat.add_zero,show q+(n-q+k)=n+k by omega] at ht
    exact h.trans ht
  refine ⟨?_,?_,hgword,heq,?_⟩
  · rw [hgpre]
    exact hblock
  · omega
  · intro k hk
    obtain ⟨he,hf⟩ := old_prefix_budget_counts f n a B x hw hpre hword hB hbudget k hk
    constructor
    · rw [he]
      have hshift := count_nat_shift (EndN f q) q (n-q) k
      rw [hqn'] at hshift
      rw [←hshift]
      apply cN_congr
      intro i _ _
      have ht := endN_nat_shift f q 0 i
      simpa only [Nat.add_zero] using ht
    · rw [hf]
      have ht := free_count_nat_shift f q (n-q) k
      rw [hqn'] at ht
      exact ht

/-- Positive relative deficit is preserved by the proved count equality;
it is not silently assumed again at the shortened prefix. -/
theorem budget_context_positive_transfer (f : Nat → Bool) (n a B : Nat) (x : List Bool)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n=w++List.replicate a true)
    (hword : seg f n x.length=x) (hB : 1≤B) (hbudget : ones x≤(B : Int))
    (hpos : ∀ k, 0<k → k≤x.length → cN (EndN f 0) n k+1≤cN (fun i => f i=false) n k) :
    let q:=n-(5*(B-1)/2)
    let g:=fun i => f (q+i)
    ∀ k, 0<k → k≤x.length →
      cN (EndN g 0) (n-q) k+1≤cN (fun i => g i=false) (n-q) k := by
  dsimp only
  let q:=n-(5*(B-1)/2)
  intro k hk hkx
  have hc := (budget_context_rebase f n a B x hw hpre hword hB hbudget).2.2.2.2 k hkx
  have hs := count_nat_shift (fun i => f i=false) q (n-q) k
  rw [show q+(n-q)=n by dsimp [q]; omega] at hs
  rw [hs,←hc.1]
  exact hpos k hk hkx

theorem endable_budget_old_prefix_trim_int (e : Int → Bool) (p : Int) (n a b B : Nat)
    {w : List Bool} (hw : BlockWord w) (hpre : segment e p n=w++List.replicate a true)
    (hnb : n≤b) (hB : 1≤B)
    (hbudget : ones (segment e (p+(n : Int)) (b-n))≤(B : Int)) :
    Endable e p (p+(b : Int)) ↔
      Endable e (p+((n-(5*(B-1)/2) : Nat) : Int)) (p+(b : Int)) := by
  rw [segment_seg e p p 0 (by simp)] at hpre
  rw [segment_seg e p (p+(n : Int)) n rfl] at hbudget
  rw [endable_iff e p p _ 0 b (by simp) rfl,
    endable_iff e p _ _ (n-(5*(B-1)/2)) b rfl rfl]
  exact endable_budget_old_prefix_trim (fun i => e (p+(i : Int))) n a b B hw hpre hnb hB hbudget

end Recaman.OldContextBudget
