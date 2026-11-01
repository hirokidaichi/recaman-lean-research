import Recaman.SeparatorSupplyReset

namespace Recaman.SeparatorTailFreeGap

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.BlockOldRay Recaman.ThreeRunSupplyBudget
open Recaman.SeparatorSupplyReset
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- Natural-clock shifting changes neither the window nor its base relative
position; it is transported through the existing integer-clock equivalence. -/
theorem endN_nat_shift (f : Nat → Bool) (q s b : Nat) :
    EndN f (q+s) (q+b) ↔ EndN (fun i => f (q+i)) s b := by
  let e : Int → Bool := fun z => f z.toNat
  have e0 : (fun i : Nat => e (0+(i : Int)))=f := by
    funext i
    simp [e]
  have eq : (fun i : Nat => e ((q : Int)+(i : Int)))=(fun i => f (q+i)) := by
    funext i
    simp only [e,←Int.natCast_add,Int.toNat_natCast]
  have h1 := endable_iff e 0 ((q+s : Nat) : Int) ((q+b : Nat) : Int)
    (q+s) (q+b) (by omega) (by omega)
  have h2 := endable_iff e (q : Int) ((q+s : Nat) : Int) ((q+b : Nat) : Int)
    s b (by omega) (by omega)
  rw [e0] at h1
  rw [eq] at h2
  exact h1.symm.trans h2

theorem count_nat_shift (P : Nat → Prop) (q s K : Nat) :
    cN (fun i => P (q+i)) s K=cN P (q+s) K := by
  induction K with
  | zero => rfl
  | succ K ih =>
    by_cases hp : P (q+s+K)
    · rw [cN_succ_pos (fun i => P (q+i)) s K (by simpa only [Nat.add_assoc] using hp),
        cN_succ_pos P (q+s) K hp,ih]
    · rw [cN_succ_neg (fun i => P (q+i)) s K (by simpa only [Nat.add_assoc] using hp),
        cN_succ_neg P (q+s) K hp,ih]

theorem seg_nat_shift (f : Nat → Bool) (q s K : Nat) :
    seg (fun i => f (q+i)) s K=seg f (q+s) K := by
  simp only [seg,Nat.add_assoc]

theorem free_count_nat_shift (f : Nat → Bool) (q s K : Nat) :
    cN (fun i => f i=true ∧ ¬EndN f q i) (q+s) K=
      cN (fun i => f (q+i)=true ∧ ¬EndN (fun t => f (q+t)) 0 i) s K := by
  rw [←count_nat_shift (fun i => f i=true ∧ ¬EndN f q i) q s K]
  apply cN_congr
  intro i _ _
  have h := endN_nat_shift f q 0 i
  simp only [Nat.add_zero] at h
  exact and_congr_right (fun _ => not_congr h)

private theorem prefix_S_word (f : Nat → Bool) (s m : Nat) (x : List Bool)
    (hword : seg f s (m+x.length)=List.replicate m false++x) (k : Nat) (hk : k≤m) :
    seg f s k=List.replicate k false := by
  have h := seg_take f s (m+x.length) k (by omega)
  rw [hword,List.take_append_of_le_length (by simpa only [List.length_replicate] using hk),
    List.take_replicate,Nat.min_eq_left hk] at h
  exact h.symm

private theorem true_count_zero_of_S (f : Nat → Bool) (s K : Nat)
    (hword : seg f s K=List.replicate K false) : cN (fun i => f i=true) s K=0 := by
  have h := ones_seg_eq_count f s K
  rw [hword,ones_replicate_S] at h
  omega

/-- A separator longer than the entire possible A budget supplies actual
positive relative deficit at every nonempty prefix, independently of history. -/
theorem positive_after_manyS (f : Nat → Bool) (m B : Nat) (x : List Bool)
    (hword : seg f 0 (m+x.length)=List.replicate m false++x)
    (hbudget : ones x≤(B : Int)) (hm : B+1≤m) :
    ∀ k, 0<k → k≤m+x.length →
      cN (EndN f 0) 0 k+1≤cN (fun i => f i=false) 0 k := by
  intro k hk hkB
  have hE : cN (EndN f 0) 0 k≤cN (fun i => f i=true) 0 k := by
    apply cN_mono
    intro i _ _ he
    exact he.1
  by_cases hkm : k≤m
  · have hA := true_count_zero_of_S f 0 k (prefix_S_word f 0 m x hword k hkm)
    have hc := (cN_walk f 0 k).2
    omega
  · have hAm := true_count_zero_of_S f 0 m (prefix_S_word f 0 m x hword m (Nat.le_refl _))
    have hSm := (cN_walk f 0 m).2
    have hmono := count_prefix_le (fun i => f i=false) 0 m k (by omega)
    have hAtotal := ones_seg_eq_count f 0 (m+x.length)
    rw [hword,ones_append,ones_replicate_S] at hAtotal
    have hAmono := count_prefix_le (fun i => f i=true) 0 k (m+x.length) hkB
    omega

private theorem suffix_segment (f : Nat → Bool) (n : Nat) (u v : List Bool)
    (hword : seg f n (u.length+v.length)=u++v) : seg f (n+u.length) v.length=v := by
  have hd := seg_drop f n (u.length+v.length) u.length (by omega)
  rw [hword,List.drop_append,List.drop_length,Nat.sub_self,List.drop_zero,List.nil_append] at hd
  simpa only [Nat.add_sub_cancel_left] using hd.symm

/-- This full count transport explicitly covers the initial S signs too;
only the proved reset, never a silent rebasing, identifies the free counts. -/
theorem free_count_reset_shift (f : Nat → Bool) (n a m B : Nat) (u x : List Bool)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n=w++List.replicate a true)
    (hword : seg f n (u.length+m+x.length)=u++(List.replicate m false++x))
    (hB : 1≤B) (hbudget : ones u+ones x≤(B : Int)) (hm : 2*(B : Int)-1≤(m : Int)) :
    cN (fun i => f i=true ∧ ¬EndN f 0 i) (n+u.length) (m+x.length)=
      cN (fun i => f (n+u.length+i)=true ∧
        ¬EndN (fun t => f (n+u.length+t)) 0 i) 0 (m+x.length) := by
  let q := n+u.length
  have hv : seg f q (m+x.length)=List.replicate m false++x := by
    simpa only [List.length_append,List.length_replicate,q] using
      suffix_segment f n u (List.replicate m false++x)
        (by simpa only [List.length_append,List.length_replicate,Nat.add_assoc] using hword)
  have hg : seg (fun i => f (q+i)) 0 (m+x.length)=List.replicate m false++x := by
    rw [seg_nat_shift,Nat.add_zero]
    exact hv
  have hA := true_count_zero_of_S f q m (prefix_S_word f q m x hv m (Nat.le_refl _))
  have hgA := true_count_zero_of_S (fun i => f (q+i)) 0 m
    (prefix_S_word (fun i => f (q+i)) 0 m x hg m (Nat.le_refl _))
  have hF : cN (fun i => f i=true ∧ ¬EndN f 0 i) q m=0 := by
    have hmono : cN (fun i => f i=true ∧ ¬EndN f 0 i) q m≤cN (fun i => f i=true) q m := by
      apply cN_mono
      intro i _ _ he
      exact he.1
    omega
  have hgF : cN (fun i => f (q+i)=true ∧ ¬EndN (fun t => f (q+t)) 0 i) 0 m=0 := by
    have hmono : cN (fun i => f (q+i)=true ∧ ¬EndN (fun t => f (q+t)) 0 i) 0 m≤
        cN (fun i => f (q+i)=true) 0 m := by
      apply cN_mono
      intro i _ _ he
      exact he.1
    omega
  have hr := (separator_future_count_eq f n a m B u x hw hpre hword hB hbudget hm).2
  have hs := free_count_nat_shift f q m x.length
  have hc := cN_add (fun i => f i=true ∧ ¬EndN f 0 i) q m x.length
  have hcg := cN_add (fun i => f (q+i)=true ∧ ¬EndN (fun t => f (q+t)) 0 i) 0 m x.length
  simp only [Nat.zero_add] at hcg
  change cN (fun i => f i=true ∧ ¬EndN f 0 i) q (m+x.length)=
    cN (fun i => f (q+i)=true ∧ ¬EndN (fun t => f (q+t)) 0 i) 0 (m+x.length)
  change cN (fun i => f i=true ∧ ¬EndN f 0 i) (q+m) x.length=_ at hr
  dsimp only [q] at *
  simp only [Nat.add_assoc] at *
  omega


private theorem segment_middle (f : Nat → Bool) (n : Nat) (u v z : List Bool)
    (hword : seg f n (u.length+v.length+z.length)=u++v++z) : seg f (n+u.length) v.length=v := by
  have hs := suffix_segment f n u (v++z)
    (by simpa only [List.length_append,List.append_assoc,Nat.add_assoc] using hword)
  have ht := seg_take f (n+u.length) (v.length+z.length) v.length (by omega)
  rw [show v.length+z.length=(v++z).length by simp only [List.length_append],hs,List.take_left] at ht
  exact ht.symm

private theorem sign_of_replicate_segment (f : Nat → Bool) (n K : Nat) (b : Bool)
    (hseg : seg f n K=List.replicate K b) (i : Nat) (hi : i<K) : f (n+i)=b := by
  have h := seg_get f n K i hi
  rw [hseg,List.getElem?_replicate,if_pos hi] at h
  exact Option.some.inj h.symm

/-- A long separator resets an arbitrary past and leaves a genuine
positive-deficit two-run problem. All free counts in the conclusion retain
base0, and the fixed A budget stays explicit. -/
theorem long_separator_two_run_free_gap (f : Nat → Bool) (n a m B L s T j : Nat) (u : List Bool)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n=w++List.replicate a true)
    (hword : seg f n (u.length+m+L+s+T)=
      u++(List.replicate m false++List.replicate L true++List.replicate s false++List.replicate T true))
    (hB : 2≤B) (hbudget : ones u+(L : Int)+(T : Int)≤(B : Int))
    (hm : 2*(B : Int)-1≤(m : Int))
    (hgap : ∀ i, n+u.length+m+L+s+T≤i → i<n+u.length+m+L+s+T+j → f i=false)
    (he : EndN f 0 (n+u.length+m+L+s+T+j)) :
    j+1≤cN (fun i => f i=true ∧ ¬EndN f 0 i) (n+u.length) (m+L+s+T) := by
  let x := List.replicate L true++List.replicate s false++List.replicate T true
  let q := n+u.length
  let g := fun i => f (q+i)
  have hxlen : x.length=L+s+T := by simp only [x,List.length_append,List.length_replicate]
  have hxo : ones x=(L : Int)+(T : Int) := by
    simp only [x,ones_append,ones_replicate_A,ones_replicate_S]
    omega
  have hwordx : seg f n (u.length+m+x.length)=u++(List.replicate m false++x) := by
    simpa only [x,List.length_append,List.length_replicate,Nat.add_assoc,List.append_assoc] using hword
  have hgword : seg g 0 (m+x.length)=List.replicate m false++x := by
    rw [seg_nat_shift,Nat.add_zero]
    simpa only [q,List.length_append,List.length_replicate] using
      suffix_segment f n u (List.replicate m false++x)
        (by simpa only [List.length_append,List.length_replicate,Nat.add_assoc] using hwordx)
  have hpos := positive_after_manyS g m B x hgword
    (by rw [hxo]; have hu := ones_bounds u; omega) (by omega)
  have hSm : seg g 0 m=List.replicate m false := prefix_S_word g 0 m x hgword m (Nat.le_refl _)
  have hAL : seg g m L=List.replicate L true := by
    have h := segment_middle g 0 (List.replicate m false) (List.replicate L true)
      (List.replicate s false++List.replicate T true)
      (by simpa only [x,List.length_append,List.length_replicate,List.append_assoc,Nat.add_assoc] using hgword)
    simpa only [Nat.zero_add,List.length_replicate] using h
  have hSs : seg g (m+L) s=List.replicate s false := by
    have h := segment_middle g 0 (List.replicate m false++List.replicate L true)
      (List.replicate s false) (List.replicate T true)
      (by simpa only [x,List.length_append,List.length_replicate,List.append_assoc,Nat.add_assoc] using hgword)
    simpa only [Nat.zero_add,List.length_append,List.length_replicate] using h
  have hAT : seg g (m+L+s) T=List.replicate T true := by
    have h := suffix_segment g 0
      (List.replicate m false++List.replicate L true++List.replicate s false) (List.replicate T true)
      (by simpa only [x,List.length_append,List.length_replicate,List.append_assoc,Nat.add_assoc] using hgword)
    simpa only [Nat.zero_add,List.length_append,List.length_replicate] using h
  have hwordj : seg f n (u.length+m+x.length+j)=
      u++(List.replicate m false++(x++List.replicate j false)) := by
    rw [seg_add,show n+(u.length+m+x.length)=n+u.length+m+L+s+T by rw [hxlen]; omega,
      seg_false f (n+u.length+m+L+s+T) j hgap,hwordx]
    simp only [List.append_assoc]
  have hreset := endable_budget_separator_iff f n a m B u (x++List.replicate j false) hw hpre
    (by simpa only [List.length_append,List.length_replicate,Nat.add_assoc] using hwordj)
    (by omega) (by simp only [ones_append,ones_replicate_S,Int.add_zero]; rw [hxo]; omega) hm
  have hendq : EndN f q (q+(m+L+s+T+j)) := by
    have hreset' : EndN f 0 (q+(m+L+s+T+j)) ↔ EndN f q (q+(m+L+s+T+j)) := by
      simpa only [q,hxlen,List.length_append,List.length_replicate,Nat.add_assoc] using hreset
    exact hreset'.mp (by simpa only [q,Nat.add_assoc] using he)
  have hendg : EndN g 0 (m+L+s+T+j) := by
    have h := (endN_nat_shift f q 0 (m+L+s+T+j)).mp (by simpa only [Nat.add_zero] using hendq)
    exact h
  have hgapg : ∀ i, m+L+s+T≤i → i<m+L+s+T+j → g i=false := by
    intro i hi hij
    exact hgap (q+i) (by dsimp [q]; omega) (by dsimp [q]; omega)
  have hbound := two_A_run_free_gap g 0 m L s T j [] BlockWord.nil (by rfl)
    (by intro i _ hi; simpa only [Nat.zero_add] using sign_of_replicate_segment g 0 m false hSm i (by omega))
    (by intro i hi; simpa only [Nat.zero_add] using sign_of_replicate_segment g m L true hAL i hi)
    (by intro i hi hil; have h := sign_of_replicate_segment g (m+L) s false hSs (i-(m+L)) (by omega); simpa only [show m+L+(i-(m+L))=i by omega] using h)
    (by intro i hi; simpa only [Nat.zero_add] using sign_of_replicate_segment g (m+L+s) T true hAT i hi)
    (by omega) (by simpa only [hxlen,Nat.zero_add,Nat.add_assoc] using hpos)
    (by simpa only [Nat.zero_add] using hgapg) (by simpa only [Nat.zero_add] using hendg)
  have hc := free_count_reset_shift f n a m B u x hw hpre hwordx (by omega)
    (by rw [hxo]; omega) hm
  have hc' : cN (fun i => g i=true ∧ ¬EndN g 0 i) 0 (m+L+s+T)=
      cN (fun i => f i=true ∧ ¬EndN f 0 i) q (m+L+s+T) := by
    simpa only [q,g,hxlen,Nat.add_assoc] using hc.symm
  rw [hc'] at hbound
  exact hbound


/-- A genuine three-run counterexample cannot have a middle S run>=39.
The required A20 bound is derived from E416, not supplied as an input. -/
theorem three_run_counterexample_middle_S_bound (f : Nat → Bool) (n h M m L s T j : Nat) (w : List Bool)
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
    (hbad : cN (fun x => f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+T)<j+1) : m<39 := by
  have hr := three_run_free_gap_residual f n h M m L s T j w hw hpre hS hA hS2 hA2 hS3 hA3
    hB hpos hgap he hbad
  have hshape := three_run_word f n h M m L s T hS hA hS2 hA2 hS3 hA3
  have hones := ones_seg_eq_count f n (h+M+m+L+s+T)
  rw [hshape,ones_append,ones_append,ones_append,ones_append,ones_append,
    ones_replicate_S,ones_replicate_S,ones_replicate_S,ones_replicate_A,
    ones_replicate_A,ones_replicate_A] at hones
  let u := List.replicate h false++List.replicate M true
  have hul : u.length=h+M := by simp only [u,List.length_append,List.length_replicate]
  have huo : ones u=(M : Int) := by simp only [u,ones_append,ones_replicate_S,ones_replicate_A]; omega
  have hword : seg f n (u.length+m+L+s+T)=u++
      (List.replicate m false++List.replicate L true++List.replicate s false++List.replicate T true) := by
    simpa only [u,List.length_append,List.length_replicate,List.append_assoc,Nat.add_assoc] using hshape
  have hp0 : seg f 0 n=w++List.replicate 0 true := by simpa using hpre
  by_cases hm : 39≤m
  · have hf := long_separator_two_run_free_gap f n 0 m 20 L s T j u hw hp0 hword (by omega)
      (by rw [huo]; omega) (by omega)
      (by simpa only [hul,Nat.add_assoc] using hgap) (by simpa only [hul,Nat.add_assoc] using he)
    have hc := cN_add (fun x => f x=true ∧ ¬EndN f 0 x) n (h+M) (m+L+s+T)
    simp only [hul,Nat.add_assoc] at hf hc hbad
    omega
  · omega

/-- The two internal S runs of any three-run counterexample are now
bounded by proved actual-history pruning; the initial S run is still free. -/
theorem three_run_counterexample_internal_S_bounds (f : Nat → Bool) (n h M m L s T j : Nat) (w : List Bool)
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
    (hbad : cN (fun x => f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+T)<j+1) : m<39 ∧ s<39 := by
  exact ⟨three_run_counterexample_middle_S_bound f n h M m L s T j w hw hpre hS hA hS2 hA2 hS3 hA3 hB hpos hgap he hbad,
    three_run_counterexample_last_S_bound f n h M m L s T j w hw hpre hS hA hS2 hA2 hS3 hA3 hB hpos hgap he hbad⟩

open Classical in
theorem long_separator_two_run_free_gap_int (e : Int → Bool) (p : Int) (n a m B L s T j : Nat)
    (u : List Bool) {w : List Bool} (hw : BlockWord w)
    (hpre : segment e p n=w++List.replicate a true)
    (hword : segment e (p+(n : Int)) (u.length+m+L+s+T)=
      u++(List.replicate m false++List.replicate L true++List.replicate s false++List.replicate T true))
    (hB : 2≤B) (hbudget : ones u+(L : Int)+(T : Int)≤(B : Int)) (hm : 2*(B : Int)-1≤(m : Int))
    (hgap : ∀ i, n+u.length+m+L+s+T≤i → i<n+u.length+m+L+s+T+j → e (p+(i : Int))=false)
    (he : Endable e p (p+((n+u.length+m+L+s+T+j : Nat) : Int))) :
    j+1≤countP (fun x => e x=true ∧ ¬Endable e p x) (p+((n+u.length : Nat) : Int)) (m+L+s+T) := by
  rw [segment_seg e p p 0 (by simp)] at hpre
  rw [segment_seg e p (p+(n : Int)) n rfl] at hword
  rw [nonsupplied_count_shift]
  apply long_separator_two_run_free_gap (fun i => e (p+(i : Int))) n a m B L s T j u hw hpre hword hB hbudget hm hgap
  exact (endable_iff e p p _ 0 (n+u.length+m+L+s+T+j) (by simp) rfl).mp he

end Recaman.SeparatorTailFreeGap
