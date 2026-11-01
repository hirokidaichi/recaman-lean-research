import Recaman.SeparatorTailFreeGap

namespace Recaman.InitialSeparatorTrim

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.BlockOldRay Recaman.ThreeRunSupplyBudget
open Recaman.SeparatorSupplyReset Recaman.SeparatorTailFreeGap
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- Only the initial S prefix is changed. The complete actual future is
copied, with its positions shifted by the explicit prefix length. -/
def trimSSequence (f : Nat → Bool) (start C : Nat) (i : Nat) : Bool :=
  if i<C then false else f (start+(i-C))

theorem trimS_tail_sign (f : Nat → Bool) (start C i : Nat) :
    trimSSequence f start C (C+i)=f (start+i) := by
  unfold trimSSequence
  rw [if_neg (by omega),Nat.add_sub_cancel_left]

theorem trimS_prefix (f : Nat → Bool) (start C K : Nat) :
    seg (trimSSequence f start C) 0 (C+K)=List.replicate C false++seg f start K := by
  rw [seg_add,Nat.zero_add]
  have hs : seg (trimSSequence f start C) 0 C=List.replicate C false := by
    apply seg_false
    intro i _ hi
    exact if_pos (by omega)
  rw [hs]
  congr 1
  change (List.range K).map (fun i => trimSSequence f start C (C+i))=
    (List.range K).map (fun i => f (start+i))
  have hf : (fun i => trimSSequence f start C (C+i))=(fun i => f (start+i)) := by
    funext i
    exact trimS_tail_sign f start C i
  rw [hf]

/-- With a fixed future A budget the excess initial S signs cannot start
any P2 window. All future S counts and word lengths are unbounded. -/
theorem initial_S_local_trim (x : List Bool) (h B C : Nat) (hx : ones x≤(B : Int))
    (hBC : B≤C) (hC : C≤h) :
    Recaman.ThreeNonsuppliedData.localSupply (List.replicate h false++x)=
      Recaman.ThreeNonsuppliedData.localSupply (List.replicate C false++x) := by
  have hm := mass_eq x
  have hb := ones_bounds x
  have he := localSupply_erase_prefix (List.replicate (h-C) false) (List.replicate C false++x)
    (by simp only [mass_append,mass_rep_false,ones_replicate_S]; omega)
  rw [←List.append_assoc,List.replicate_append_replicate,show h-C+C=h by omega] at he
  exact he

private theorem suffix_segment (f : Nat → Bool) (n : Nat) (u v : List Bool)
    (hword : seg f n (u.length+v.length)=u++v) : seg f (n+u.length) v.length=v := by
  have hd := seg_drop f n (u.length+v.length) u.length (by omega)
  rw [hword,List.drop_append,List.drop_length,Nat.sub_self,List.drop_zero,List.nil_append] at hd
  simpa only [Nat.add_sub_cancel_left] using hd.symm

/-- The old prefix is erased by the actual reset theorem before trimming.
The endpoint sign is preserved too, so the result is an EndN equivalence. -/
theorem initial_S_endable_trim (f : Nat → Bool) (n a h B C : Nat) (x : List Bool)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n=w++List.replicate a true)
    (hword : seg f n (h+x.length)=List.replicate h false++x)
    (hB : 1≤B) (hx : ones x≤(B : Int)) (hC : C≤h) (hBC : 2*(B : Int)-1≤(C : Int)) :
    EndN f 0 (n+h+x.length) ↔
      EndN (trimSSequence f (n+h) C) 0 (C+x.length) := by
  have hsuffix : seg f (n+h) x.length=x := by
    simpa only [List.length_replicate] using suffix_segment f n (List.replicate h false) x
      (by simpa only [List.length_replicate] using hword)
  have hgword : seg (trimSSequence f (n+h) C) 0 (C+x.length)=List.replicate C false++x := by
    rw [trimS_prefix,hsuffix]
  by_cases hA : f (n+h+x.length)=true
  · have he := endable_budget_separator_iff f n a h B [] x hw hpre
      (by simpa only [List.length_nil,List.nil_append,Nat.zero_add] using hword)
      hB (by simpa only [ones,Int.zero_add] using hx) (by omega)
    have hl := localSupply_seg_iff f n (n+h+x.length) (by omega) hA
    rw [show n+h+x.length-n=h+x.length by omega,hword] at hl
    have hAg : trimSSequence f (n+h) C (C+x.length)=true := by rw [trimS_tail_sign]; exact hA
    have hgl := localSupply_seg_iff (trimSSequence f (n+h) C) 0 (C+x.length) (by omega) hAg
    rw [Nat.sub_zero,hgword] at hgl
    have htrim := initial_S_local_trim x h B C hx (by omega) hC
    have he' : EndN f 0 (n+h+x.length) ↔ EndN f n (n+h+x.length) := by
      simpa only [List.length_nil,Nat.zero_add,Nat.add_zero,Nat.add_assoc] using he
    have ht : Recaman.ThreeNonsuppliedData.localSupply (List.replicate h false++x)=true ↔
        Recaman.ThreeNonsuppliedData.localSupply (List.replicate C false++x)=true := by rw [htrim]
    exact he'.trans (hl.symm.trans (ht.trans hgl))
  · have hAg : ¬trimSSequence f (n+h) C (C+x.length)=true := by rw [trimS_tail_sign]; exact hA
    constructor
    · intro he
      exact False.elim (hA he.1)
    · intro he
      exact False.elim (hAg he.1)

private theorem ones_take_bound (x : List Bool) (k : Nat) : ones (x.take k)≤ones x := by
  have h := ones_append (x.take k) (x.drop k)
  rw [List.take_append_drop] at h
  have hd := ones_bounds (x.drop k)
  omega

theorem initial_S_prefix_endable_trim (f : Nat → Bool) (n a h B C : Nat) (x : List Bool)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n=w++List.replicate a true)
    (hword : seg f n (h+x.length)=List.replicate h false++x)
    (hB : 1≤B) (hx : ones x≤(B : Int)) (hC : C≤h) (hBC : 2*(B : Int)-1≤(C : Int))
    (k : Nat) (hk : k≤x.length) :
    EndN f 0 (n+h+k) ↔ EndN (trimSSequence f (n+h) C) 0 (C+k) := by
  have hp : seg f n (h+k)=List.replicate h false++x.take k := by
    have hh := seg_take f n (h+x.length) (h+k) (by omega)
    rw [hword,List.take_append,List.take_of_length_le (by simp only [List.length_replicate]; omega),
      show h+k-(List.replicate h false).length=k by simp only [List.length_replicate]; omega] at hh
    exact hh.symm
  have h := initial_S_endable_trim f n a h B C (x.take k) hw hpre
    (by simpa only [List.length_take,Nat.min_eq_left hk] using hp) hB
    (by have ho := ones_take_bound x k; omega) hC hBC
  simpa only [List.length_take,Nat.min_eq_left hk] using h

theorem initial_S_future_free_count (f : Nat → Bool) (n a h B C : Nat) (x : List Bool)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n=w++List.replicate a true)
    (hword : seg f n (h+x.length)=List.replicate h false++x)
    (hB : 1≤B) (hx : ones x≤(B : Int)) (hC : C≤h) (hBC : 2*(B : Int)-1≤(C : Int)) :
    cN (fun i => f i=true ∧ ¬EndN f 0 i) (n+h) x.length=
      cN (fun i => trimSSequence f (n+h) C i=true ∧
        ¬EndN (trimSSequence f (n+h) C) 0 i) C x.length := by
  have hc1 := count_nat_shift (fun i => f i=true ∧ ¬EndN f 0 i) (n+h) 0 x.length
  have hc2 := count_nat_shift (fun i => trimSSequence f (n+h) C i=true ∧
    ¬EndN (trimSSequence f (n+h) C) 0 i) C 0 x.length
  simp only [Nat.add_zero] at hc1 hc2
  rw [←hc1,←hc2]
  apply cN_congr
  intro i _ hi
  have he := initial_S_prefix_endable_trim f n a h B C x hw hpre hword hB hx hC hBC i (by omega)
  rw [trimS_tail_sign]
  exact and_congr_right (fun _ => not_congr he)

private theorem free_zero_S (f : Nat → Bool) (s K : Nat)
    (hword : seg f s K=List.replicate K false) :
    cN (fun i => f i=true ∧ ¬EndN f 0 i) s K=0 := by
  have h := ones_seg_eq_count f s K
  rw [hword,ones_replicate_S] at h
  have hm : cN (fun i => f i=true ∧ ¬EndN f 0 i) s K≤cN (fun i => f i=true) s K := by
    apply cN_mono
    intro i _ _ he
    exact he.1
  omega

theorem initial_S_full_free_count (f : Nat → Bool) (n a h B C : Nat) (x : List Bool)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n=w++List.replicate a true)
    (hword : seg f n (h+x.length)=List.replicate h false++x)
    (hB : 1≤B) (hx : ones x≤(B : Int)) (hC : C≤h) (hBC : 2*(B : Int)-1≤(C : Int)) :
    cN (fun i => f i=true ∧ ¬EndN f 0 i) n (h+x.length)=
      cN (fun i => trimSSequence f (n+h) C i=true ∧
        ¬EndN (trimSSequence f (n+h) C) 0 i) 0 (C+x.length) := by
  have hs : seg f n h=List.replicate h false := by
    have hh := seg_take f n (h+x.length) h (by omega)
    have hleft : (List.replicate h false++x).take h=List.replicate h false := by
      simpa only [List.length_replicate] using
        (List.take_left (l₁:=List.replicate h false) (l₂:=x))
    rw [hword,hleft] at hh
    exact hh.symm
  have hgs : seg (trimSSequence f (n+h) C) 0 C=List.replicate C false := by
    simpa only [Nat.add_zero,seg,List.range_zero,List.map_nil,List.append_nil] using trimS_prefix f (n+h) C 0
  have hz := free_zero_S f n h hs
  have hgz := free_zero_S (trimSSequence f (n+h) C) 0 C hgs
  have he := initial_S_future_free_count f n a h B C x hw hpre hword hB hx hC hBC
  have hc := cN_add (fun i => f i=true ∧ ¬EndN f 0 i) n h x.length
  have hcg := cN_add (fun i => trimSSequence f (n+h) C i=true ∧
    ¬EndN (trimSSequence f (n+h) C) 0 i) 0 C x.length
  simp only [Nat.zero_add] at hcg
  omega


/-- A long-head counterexample is transported to a new actual sign history
with an empty old prefix and the fixed head length C. The target, all free
counts and positive deficit are supplied, not assumed for the new history. -/
theorem initial_S_counterexample_transfer (f : Nat → Bool) (n a h B C j : Nat) (x : List Bool)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n=w++List.replicate a true)
    (hword : seg f n (h+x.length)=List.replicate h false++x)
    (hB : 2≤B) (hx : ones x≤(B : Int)) (hC : C≤h) (hBC : 2*(B : Int)-1≤(C : Int))
    (hgap : ∀ i, n+h+x.length≤i → i<n+h+x.length+j → f i=false)
    (he : EndN f 0 (n+h+x.length+j))
    (hbad : cN (fun i => f i=true ∧ ¬EndN f 0 i) n (h+x.length)<j+1) :
    cN (fun i => trimSSequence f (n+h) C i=true ∧
      ¬EndN (trimSSequence f (n+h) C) 0 i) 0 (C+x.length)<j+1 ∧
    EndN (trimSSequence f (n+h) C) 0 (C+x.length+j) ∧
    (∀ k, 0<k → k≤C+x.length+j →
      cN (EndN (trimSSequence f (n+h) C) 0) 0 k+1≤
        cN (fun i => trimSSequence f (n+h) C i=false) 0 k) ∧
    seg (trimSSequence f (n+h) C) 0 (C+x.length)=List.replicate C false++x := by
  have hcount := initial_S_full_free_count f n a h B C x hw hpre hword (by omega) hx hC hBC
  have hwj : seg f n (h+(x++List.replicate j false).length)=
      List.replicate h false++(x++List.replicate j false) := by
    simp only [List.length_append,List.length_replicate]
    rw [show h+(x.length+j)=h+x.length+j by omega,seg_add,
      show n+(h+x.length)=n+h+x.length by omega,seg_false f (n+h+x.length) j hgap,hword]
    simp only [List.append_assoc]
  have hxj : ones (x++List.replicate j false)≤(B : Int) := by
    simpa only [ones_append,ones_replicate_S,Int.add_zero] using hx
  have heq := initial_S_endable_trim f n a h B C (x++List.replicate j false) hw hpre hwj
    (by omega) hxj hC hBC
  have htarget : EndN (trimSSequence f (n+h) C) 0 (C+x.length+j) := by
    have hpoint : EndN f 0 (n+h+x.length+j) ↔
        EndN (trimSSequence f (n+h) C) 0 (C+x.length+j) := by
      simpa only [List.length_append,List.length_replicate,Nat.add_assoc] using heq
    exact hpoint.mp he
  have hxsuffix : seg f (n+h) x.length=x := by
    simpa only [List.length_replicate] using suffix_segment f n (List.replicate h false) x
      (by simpa only [List.length_replicate] using hword)
  have hxjsuffix : seg f (n+h) (x++List.replicate j false).length=x++List.replicate j false := by
    simpa only [List.length_replicate] using suffix_segment f n (List.replicate h false)
      (x++List.replicate j false) (by simpa only [List.length_replicate] using hwj)
  have hgj : seg (trimSSequence f (n+h) C) 0 (C+(x++List.replicate j false).length)=
      List.replicate C false++(x++List.replicate j false) := by rw [trimS_prefix,hxjsuffix]
  have hpos := positive_after_manyS (trimSSequence f (n+h) C) C B (x++List.replicate j false)
    hgj hxj (by omega)
  refine ⟨?_,htarget,?_,?_⟩
  · omega
  · simpa only [List.length_append,List.length_replicate,Nat.add_assoc] using hpos
  · rw [trimS_prefix,hxsuffix]

open Classical in
theorem initial_S_endable_trim_int (e : Int → Bool) (p : Int) (n a h B C : Nat) (x : List Bool)
    {w : List Bool} (hw : BlockWord w) (hpre : segment e p n=w++List.replicate a true)
    (hword : segment e (p+(n : Int)) (h+x.length)=List.replicate h false++x)
    (hB : 1≤B) (hx : ones x≤(B : Int)) (hC : C≤h) (hBC : 2*(B : Int)-1≤(C : Int)) :
    Endable e p (p+((n+h+x.length : Nat) : Int)) ↔
      EndN (trimSSequence (fun i => e (p+(i : Int))) (n+h) C) 0 (C+x.length) := by
  rw [segment_seg e p p 0 (by simp)] at hpre
  rw [segment_seg e p (p+(n : Int)) n rfl] at hword
  rw [endable_iff e p p _ 0 (n+h+x.length) (by simp) rfl]
  exact initial_S_endable_trim (fun i => e (p+(i : Int))) n a h B C x hw hpre hword hB hx hC hBC

open Classical in
theorem initial_S_full_free_count_int (e : Int → Bool) (p : Int) (n a h B C : Nat) (x : List Bool)
    {w : List Bool} (hw : BlockWord w) (hpre : segment e p n=w++List.replicate a true)
    (hword : segment e (p+(n : Int)) (h+x.length)=List.replicate h false++x)
    (hB : 1≤B) (hx : ones x≤(B : Int)) (hC : C≤h) (hBC : 2*(B : Int)-1≤(C : Int)) :
    countP (fun i => e i=true ∧ ¬Endable e p i) (p+(n : Int)) (h+x.length)=
      cN (fun i => trimSSequence (fun k => e (p+(k : Int))) (n+h) C i=true ∧
        ¬EndN (trimSSequence (fun k => e (p+(k : Int))) (n+h) C) 0 i) 0 (C+x.length) := by
  rw [segment_seg e p p 0 (by simp)] at hpre
  rw [segment_seg e p (p+(n : Int)) n rfl] at hword
  rw [nonsupplied_count_shift]
  exact initial_S_full_free_count (fun i => e (p+(i : Int))) n a h B C x hw hpre hword hB hx hC hBC

end Recaman.InitialSeparatorTrim
