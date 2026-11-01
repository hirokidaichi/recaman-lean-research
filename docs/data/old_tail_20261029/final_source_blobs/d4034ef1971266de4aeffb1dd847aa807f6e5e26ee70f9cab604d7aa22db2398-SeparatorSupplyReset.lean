import Recaman.ThreeRunSupplyBudget

namespace Recaman.SeparatorSupplyReset

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.BlockOldRay Recaman.ThreeRunSupplyBudget
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- An explicit total A budget makes a sufficiently long S separator erase
both the local earlier tail and every old BlockWord start. The endpoint sign
is part of EndN on both sides, never inferred from a possible window. -/
theorem endable_budget_separator_iff (f : Nat → Bool) (n a m B : Nat) (u x : List Bool)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n=w++List.replicate a true)
    (hword : seg f n (u.length+m+x.length)=u++(List.replicate m false++x))
    (hB : 1≤B) (hbudget : ones u+ones x≤(B : Int)) (hm : 2*(B : Int)-1≤(m : Int)) :
    EndN f 0 (n+(u.length+m+x.length)) ↔
      EndN f (n+u.length) (n+(u.length+m+x.length)) := by
  have hu := ones_bounds u
  have hx := ones_bounds x
  have hmx := mass_eq x
  have hpos : 0<u.length+m+x.length := by omega
  have hbarrier : mass (List.replicate m false++x)+ones u≤0 := by
    rw [mass_append,mass_rep_false]
    omega
  have herase := localSupply_erase_prefix u (List.replicate m false++x) hbarrier
  have hsuffix : seg f (n+u.length) (m+x.length)=List.replicate m false++x := by
    have hd := seg_drop f n (u.length+m+x.length) u.length (by omega)
    rw [hword,List.drop_append,List.drop_length,Nat.sub_self,List.drop_zero,List.nil_append] at hd
    simpa only [show u.length+m+x.length-u.length=m+x.length by omega] using hd.symm
  constructor
  · intro he
    obtain ⟨hA,t,l,ht0,htl,hwin⟩ := he
    by_cases htn : t<n
    · have hwin' : Win f t (n+(u.length+m+x.length)-t) := by
        have heq : n+(u.length+m+x.length)-t=l := by omega
        simpa only [heq] using hwin
      have hc := old_window_count_barrier f n a t (n+(u.length+m+x.length)) hw hpre htn (by omega) hwin'
      rw [Nat.add_sub_cancel_left,hword] at hc
      simp only [ones_append,ones_replicate_S,Int.natCast_add,Int.zero_add] at hc
      omega
    · have heLocal : EndN f n (n+(u.length+m+x.length)) :=
        ⟨hA,t,l,by omega,htl,hwin⟩
      have hl := (localSupply_seg_iff f n (n+(u.length+m+x.length)) (by omega) hA).mpr heLocal
      rw [Nat.add_sub_cancel_left,hword,herase] at hl
      apply (localSupply_seg_iff f (n+u.length) (n+(u.length+m+x.length)) (by omega) hA).mp
      rw [show n+(u.length+m+x.length)-(n+u.length)=m+x.length by omega,hsuffix]
      exact hl
  · intro he
    exact end_mono f 0 (n+u.length) _ (Nat.zero_le _) he

open Classical in
theorem endable_budget_separator_int (e : Int → Bool) (p : Int) (n a m B : Nat)
    (u x : List Bool) {w : List Bool} (hw : BlockWord w)
    (hpre : segment e p n=w++List.replicate a true)
    (hword : segment e (p+(n : Int)) (u.length+m+x.length)=u++(List.replicate m false++x))
    (hB : 1≤B) (hbudget : ones u+ones x≤(B : Int)) (hm : 2*(B : Int)-1≤(m : Int)) :
    Endable e p (p+((n+(u.length+m+x.length) : Nat) : Int)) ↔
      Endable e (p+((n+u.length : Nat) : Int)) (p+((n+(u.length+m+x.length) : Nat) : Int)) := by
  rw [segment_seg e p p 0 (by simp)] at hpre
  rw [segment_seg e p (p+(n : Int)) n rfl] at hword
  rw [endable_iff e p p _ 0 (n+(u.length+m+x.length)) (by simp) rfl,
    endable_iff e p (p+((n+u.length : Nat) : Int)) _ (n+u.length)
      (n+(u.length+m+x.length)) rfl rfl]
  exact endable_budget_separator_iff (fun i => e (p+(i : Int))) n a m B u x hw hpre hword hB hbudget hm


private theorem ones_take_bound (x : List Bool) (k : Nat) : ones (x.take k)≤ones x := by
  have he := ones_append (x.take k) (x.drop k)
  rw [List.take_append_drop] at he
  have hd := ones_bounds (x.drop k)
  omega

/-- The same reset holds at every prefix of a future word under the fixed
budget, so actual supply/free counts can be transported, not just one tag. -/
theorem endable_budget_separator_prefix (f : Nat → Bool) (n a m B : Nat) (u x : List Bool)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n=w++List.replicate a true)
    (hword : seg f n (u.length+m+x.length)=u++(List.replicate m false++x))
    (hB : 1≤B) (hbudget : ones u+ones x≤(B : Int)) (hm : 2*(B : Int)-1≤(m : Int))
    (k : Nat) (hk : k≤x.length) :
    EndN f 0 (n+(u.length+m+k)) ↔ EndN f (n+u.length) (n+(u.length+m+k)) := by
  have hprefix : seg f n (u.length+m+k)=u++(List.replicate m false++x.take k) := by
    have hs := seg_take f n (u.length+m+x.length) (u.length+m+k) (by omega)
    rw [hword,←List.append_assoc,List.take_append,
      List.take_of_length_le (by simp only [List.length_append,List.length_replicate]; omega),
      show u.length+m+k-(u++List.replicate m false).length=k by
        simp only [List.length_append,List.length_replicate]; omega] at hs
    simpa only [List.append_assoc] using hs.symm
  have he := endable_budget_separator_iff f n a m B u (x.take k) hw hpre (by simpa only [List.length_take,Nat.min_eq_left hk] using hprefix) hB
    (by have h := ones_take_bound x k; omega) hm
  simpa only [List.length_take,Nat.min_eq_left hk] using he

/-- Both supply and free-A counts over the entire future agree with the
new base only after the reset equivalence has been proved pointwise. -/
theorem separator_future_count_eq (f : Nat → Bool) (n a m B : Nat) (u x : List Bool)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n=w++List.replicate a true)
    (hword : seg f n (u.length+m+x.length)=u++(List.replicate m false++x))
    (hB : 1≤B) (hbudget : ones u+ones x≤(B : Int)) (hm : 2*(B : Int)-1≤(m : Int)) :
    cN (EndN f 0) (n+u.length+m) x.length=
      cN (EndN f (n+u.length)) (n+u.length+m) x.length ∧
    cN (fun i => f i=true ∧ ¬EndN f 0 i) (n+u.length+m) x.length=
      cN (fun i => f i=true ∧ ¬EndN f (n+u.length) i) (n+u.length+m) x.length := by
  have heq : ∀ i, n+u.length+m≤i → i<n+u.length+m+x.length →
      (EndN f 0 i ↔ EndN f (n+u.length) i) := by
    intro i hi hil
    have h := endable_budget_separator_prefix f n a m B u x hw hpre hword hB hbudget hm
      (i-(n+u.length+m)) (by omega)
    simpa only [show n+(u.length+m+(i-(n+u.length+m)))=i by omega] using h
  constructor
  · apply cN_congr
    exact heq
  · apply cN_congr
    intro i hi hil
    exact and_congr_right (fun _ => not_congr (heq i hi hil))


/-- The old count barrier already supplies a nontrivial counterfamily one
below the separator threshold. This is an existing family used as a sharp
boundary control, not a new counterexample to C1. -/
theorem separator_threshold_control (B : Nat) (hB : 3≤B) :
    BlockWord (List.replicate 1 false++List.replicate B true) ∧
    Recaman.ThreeNonsuppliedData.localSupply
      ((List.replicate 1 false++List.replicate B true)++
        List.replicate (2*B-2) false++List.replicate B true)=true ∧
    Recaman.ThreeNonsuppliedData.localSupply
      (List.replicate (2*B-2) false++List.replicate B true)=false := by
  obtain ⟨hw,hm,ha⟩ := old_count_barrier_sharp_family B hB
  refine ⟨hw,?_,?_⟩
  · apply (localSupply_iff _).mpr
    refine ⟨0,?_,?_,?_⟩
    · simp only [List.length_append,List.length_replicate]
      omega
    · simpa only [List.drop_zero] using hm
    · rw [List.drop_zero,checked_wordArea_eq]
      exact ha
  · have hiff := localSupply_three_runs_iff (2*B-2) B 0
    simp only [List.replicate_zero,List.append_nil,Nat.zero_add,Nat.mul_one] at hiff
    cases he : Recaman.ThreeNonsuppliedData.localSupply
        (List.replicate (2*B-2) false++List.replicate B true)
    · rfl
    · have hh := hiff.mp he
      omega


private theorem segment_after_prefix (f : Nat → Bool) (n : Nat) (u v : List Bool)
    (hword : seg f n (u.length+v.length)=u++v) : seg f (n+u.length) v.length=v := by
  have hd := seg_drop f n (u.length+v.length) u.length (by omega)
  rw [hword,List.drop_append,List.drop_length,Nat.sub_self,List.drop_zero,List.nil_append] at hd
  simpa only [Nat.add_sub_cancel_left] using hd.symm

/-- After the proved reset the actual supplied A clocks obey the pure
three-run classification, including r=0 and an arbitrary final S gap. -/
theorem long_separator_run_gap_iff (f : Nat → Bool) (n a m B r j : Nat) (u : List Bool)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n=w++List.replicate a true)
    (hword : seg f n (u.length+m+r+j)=
      u++(List.replicate m false++List.replicate r true++List.replicate j false))
    (hB : 1≤B) (hbudget : ones u+(r : Int)≤(B : Int)) (hm : 2*(B : Int)-1≤(m : Int))
    (hA : f (n+(u.length+m+r+j))=true) :
    EndN f 0 (n+(u.length+m+r+j)) ↔ r=2*(j+1) ∧ j+1≤m := by
  let x := List.replicate r true++List.replicate j false
  have hword' : seg f n (u.length+m+x.length)=u++(List.replicate m false++x) := by
    simpa only [x,List.length_append,List.length_replicate,Nat.add_assoc,List.append_assoc] using hword
  have he := endable_budget_separator_iff f n a m B u x hw hpre hword' hB
    (by simpa only [x,ones_append,ones_replicate_A,ones_replicate_S,Int.add_zero] using hbudget) hm
  have hv : seg f (n+u.length) (m+r+j)=
      List.replicate m false++List.replicate r true++List.replicate j false := by
    have h := segment_after_prefix f n u (List.replicate m false++x)
      (by simpa only [x,List.length_append,List.length_replicate,Nat.add_assoc,List.append_assoc] using hword')
    simpa only [x,List.length_append,List.length_replicate,Nat.add_assoc,List.append_assoc] using h
  have hlocal := localSupply_seg_iff f (n+u.length) (n+(u.length+m+r+j)) (by omega) hA
  rw [show n+(u.length+m+r+j)-(n+u.length)=m+r+j by omega,hv] at hlocal
  have hshape := localSupply_three_runs_iff m r j
  have hpoint : EndN f 0 (n+(u.length+m+r+j)) ↔
      EndN f (n+u.length) (n+(u.length+m+r+j)) := by
    simpa only [x,List.length_append,List.length_replicate,Nat.add_assoc] using he
  exact hpoint.trans (hlocal.symm.trans hshape)

/-- The long separator leaves at most one actual supplied A inside the
following A run. The possible clock is2; it may lie outside the run. -/
theorem long_separator_A_supply_count (f : Nat → Bool) (n a m B T : Nat) (u : List Bool)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n=w++List.replicate a true)
    (hword : seg f n (u.length+m+T)=u++(List.replicate m false++List.replicate T true))
    (hB : 1≤B) (hbudget : ones u+(T : Int)≤(B : Int)) (hm : 2*(B : Int)-1≤(m : Int)) :
    cN (EndN f 0) (n+u.length+m) T≤1 := by
  have hclock : ∀ i, i<T → EndN f 0 (n+u.length+m+i) → i=2 := by
    intro i hi he
    have hprefix : seg f n (u.length+m+i)=u++(List.replicate m false++List.replicate i true) := by
      have h := seg_take f n (u.length+m+T) (u.length+m+i) (by omega)
      rw [hword,←List.append_assoc,List.take_append,
        List.take_of_length_le (by simp only [List.length_append,List.length_replicate]; omega),
        show u.length+m+i-(u++List.replicate m false).length=i by
          simp only [List.length_append,List.length_replicate]; omega,
        List.take_replicate,Nat.min_eq_left (Nat.le_of_lt hi)] at h
      simpa only [List.append_assoc] using h.symm
    have hc := long_separator_run_gap_iff f n a m B i 0 u hw hpre
      (by simpa only [List.replicate_zero,List.append_nil,Nat.add_zero] using hprefix) hB
      (by omega) hm (by simpa only [Nat.add_assoc,Nat.add_zero] using he.1)
    have h := hc.mp (by simpa only [Nat.add_assoc,Nat.add_zero] using he)
    omega
  let start := n+u.length+m
  let P := fun i => start≤i ∧ i<start+T ∧ EndN f 0 i
  have hp : cN P 0 (start+T)≤1 := by
    apply cN_le_one_of_unique
    intro i _ j _ hi hj
    have hi2 := hclock (i-start) (by change start≤i ∧ i<start+T ∧ _ at hi; omega)
      (by simpa only [show n+u.length+m+(i-start)=i by change start≤i ∧ _ at hi; omega] using hi.2.2)
    have hj2 := hclock (j-start) (by change start≤j ∧ j<start+T ∧ _ at hj; omega)
      (by simpa only [show n+u.length+m+(j-start)=j by change start≤j ∧ _ at hj; omega] using hj.2.2)
    omega
  have hc : cN (EndN f 0) start T=cN P start T := by
    apply cN_congr
    intro i hi hil
    exact ⟨fun he => ⟨hi,hil,he⟩,fun he => he.2.2⟩
  have hsum := cN_add P 0 start T
  simp only [Nat.zero_add] at hsum
  change cN (EndN f 0) start T≤1
  omega

/-- A long final separator makes free-gap follow from the actual last
A-run alone, for arbitrary earlier tail u and without a deficit assumption. -/
theorem long_separator_free_gap (f : Nat → Bool) (n a m B T j : Nat) (u : List Bool)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n=w++List.replicate a true)
    (hword : seg f n (u.length+m+T)=u++(List.replicate m false++List.replicate T true))
    (hB : 1≤B) (hbudget : ones u+(T : Int)≤(B : Int)) (hm : 2*(B : Int)-1≤(m : Int))
    (hgap : ∀ x, n+u.length+m+T≤x → x<n+u.length+m+T+j → f x=false)
    (he : EndN f 0 (n+u.length+m+T+j)) :
    T=2*(j+1) ∧ 2*j+1≤cN (fun i => f i=true ∧ ¬EndN f 0 i) (n+u.length+m) T ∧
      j+1≤cN (fun i => f i=true ∧ ¬EndN f 0 i) (n+u.length+m) T := by
  have hwordj : seg f n (u.length+m+T+j)=
      u++(List.replicate m false++List.replicate T true++List.replicate j false) := by
    rw [seg_add,show n+(u.length+m+T)=n+u.length+m+T by omega,
      seg_false f (n+u.length+m+T) j hgap,hword]
    simp only [List.append_assoc]
  have hclass := long_separator_run_gap_iff f n a m B T j u hw hpre hwordj hB hbudget hm
    (by simpa only [Nat.add_assoc] using he.1)
  have hT := (hclass.mp (by simpa only [Nat.add_assoc] using he)).1
  have hs := long_separator_A_supply_count f n a m B T u hw hpre hword hB hbudget hm
  have hAword : seg f (n+u.length+m) T=List.replicate T true := by
    have h := segment_after_prefix f n (u++List.replicate m false) (List.replicate T true)
      (by simpa only [List.length_append,List.length_replicate,List.append_assoc] using hword)
    simpa only [List.length_append,List.length_replicate,Nat.add_assoc] using h
  have ha := ones_seg_eq_count f (n+u.length+m) T
  rw [hAword,ones_replicate_A] at ha
  have hp := addition_endable_partition f (n+u.length+m) T
  omega


private theorem segment_A_offsets (f : Nat → Bool) (n K : Nat)
    (hA : ∀ i, i<K → f (n+i)=true) : seg f n K=List.replicate K true := by
  apply seg_A
  intro x hx hxK
  simpa only [Nat.add_sub_cancel' hx] using hA (x-n) (by omega)

theorem three_run_word (f : Nat → Bool) (n h M m L s T : Nat)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ i, i<M → f (n+h+i)=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → f x=false)
    (hA2 : ∀ i, i<L → f (n+h+M+m+i)=true)
    (hS3 : ∀ x, n+h+M+m+L≤x → x<n+h+M+m+L+s → f x=false)
    (hA3 : ∀ i, i<T → f (n+h+M+m+L+s+i)=true) :
    seg f n (h+M+m+L+s+T)=List.replicate h false++List.replicate M true++
      List.replicate m false++List.replicate L true++List.replicate s false++List.replicate T true := by
  rw [seg_add,seg_add,seg_add,seg_add,seg_add,seg_false f n h hS,
    segment_A_offsets f (n+h) M hA,
    show n+(h+M)=n+h+M by omega,seg_false f (n+h+M) m hS2,
    show n+(h+M+m)=n+h+M+m by omega,segment_A_offsets f (n+h+M+m) L hA2,
    show n+(h+M+m+L)=n+h+M+m+L by omega,seg_false f (n+h+M+m+L) s hS3,
    show n+(h+M+m+L+s)=n+h+M+m+L+s by omega,segment_A_offsets f (n+h+M+m+L+s) T hA3]

/-- The A20 bound is derived from a genuine three-run counterexample,
then the long-separator theorem excludes every final S run of length>=39. -/
theorem three_run_counterexample_last_S_bound (f : Nat → Bool) (n h M m L s T j : Nat) (w : List Bool)
    (hw : BlockWord w) (hpre : seg f 0 n=w)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ i, i<M → f (n+h+i)=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → f x=false)
    (hA2 : ∀ i, i<L → f (n+h+M+m+i)=true)
    (hS3 : ∀ x, n+h+M+m+L≤x → x<n+h+M+m+L+s → f x=false)
    (hA3 : ∀ i, i<T → f (n+h+M+m+L+s+i)=true)
    (hB : 0<h+M+m+L+s+T)
    (hpos : ∀ k, 0<k → k≤h+M+m+L+s+T →
      cN (EndN f 0) n k+1≤cN (fun x => f x=false) n k)
    (hgap : ∀ x, n+h+M+m+L+s+T≤x → x<n+h+M+m+L+s+T+j → f x=false)
    (he : EndN f 0 (n+h+M+m+L+s+T+j))
    (hbad : cN (fun x => f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+T)<j+1) : s<39 := by
  have hr := three_run_free_gap_residual f n h M m L s T j w hw hpre hS hA hS2 hA2 hS3 hA3
    hB hpos hgap he hbad
  have hshape := three_run_word f n h M m L s T hS hA hS2 hA2 hS3 hA3
  have hones := ones_seg_eq_count f n (h+M+m+L+s+T)
  rw [hshape,ones_append,ones_append,ones_append,ones_append,ones_append,
    ones_replicate_S,ones_replicate_S,ones_replicate_S,ones_replicate_A,
    ones_replicate_A,ones_replicate_A] at hones
  let u := List.replicate h false++List.replicate M true++List.replicate m false++List.replicate L true
  have hul : u.length=h+M+m+L := by simp only [u,List.length_append,List.length_replicate]
  have huo : ones u=(M : Int)+(L : Int) := by simp only [u,ones_append,ones_replicate_S,ones_replicate_A]; omega
  have hword : seg f n (u.length+s+T)=u++(List.replicate s false++List.replicate T true) := by
    simpa only [u,List.length_append,List.length_replicate,List.append_assoc,Nat.add_assoc] using hshape
  have hp0 : seg f 0 n=w++List.replicate 0 true := by simpa using hpre
  by_cases hs : 39≤s
  · have hf := long_separator_free_gap f n 0 s 20 T j u hw hp0 hword (by omega)
      (by rw [huo]; omega) (by omega)
      (by simpa only [hul,Nat.add_assoc] using hgap) (by simpa only [hul,Nat.add_assoc] using he)
    have hc := cN_add (fun x => f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s) T
    simp only [hul,Nat.add_assoc] at hf hc hbad
    omega
  · omega

open Classical in
theorem long_separator_free_gap_int (e : Int → Bool) (p : Int) (n a m B T j : Nat)
    (u : List Bool) {w : List Bool} (hw : BlockWord w)
    (hpre : segment e p n=w++List.replicate a true)
    (hword : segment e (p+(n : Int)) (u.length+m+T)=u++(List.replicate m false++List.replicate T true))
    (hB : 1≤B) (hbudget : ones u+(T : Int)≤(B : Int)) (hm : 2*(B : Int)-1≤(m : Int))
    (hgap : ∀ i, n+u.length+m+T≤i → i<n+u.length+m+T+j → e (p+(i : Int))=false)
    (he : Endable e p (p+((n+u.length+m+T+j : Nat) : Int))) :
    T=2*(j+1) ∧
      2*j+1≤countP (fun x => e x=true ∧ ¬Endable e p x) (p+((n+u.length+m : Nat) : Int)) T ∧
      j+1≤countP (fun x => e x=true ∧ ¬Endable e p x) (p+((n+u.length+m : Nat) : Int)) T := by
  rw [segment_seg e p p 0 (by simp)] at hpre
  rw [segment_seg e p (p+(n : Int)) n rfl] at hword
  rw [nonsupplied_count_shift]
  apply long_separator_free_gap (fun i => e (p+(i : Int))) n a m B T j u hw hpre hword hB hbudget hm hgap
  exact (endable_iff e p p _ 0 (n+u.length+m+T+j) (by simp) rfl).mp he

end Recaman.SeparatorSupplyReset
