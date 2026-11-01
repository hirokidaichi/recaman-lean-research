import Recaman.BlockSuffixPositivity

namespace Recaman.PrefixMassBarrier

open Recaman.LeadingRunSupply
open Recaman.BlockSuffixPositivity
open Recaman.CapacityEqualityInduction
open Recaman.SingleWindowEquality
open Recaman.LineCapacityPeriodic

/-- A sufficiently negative tail mass excludes every local window that
starts in the discarded prefix. No restriction on either word's length. -/
theorem localSupply_erase_prefix (u v : List Bool)
    (hbarrier : mass v + ones u ≤ 0) :
    Recaman.ThreeNonsuppliedData.localSupply (u++v) =
      Recaman.ThreeNonsuppliedData.localSupply v := by
  apply Bool.eq_iff_iff.mpr
  rw [localSupply_iff,localSupply_iff]
  constructor
  · rintro ⟨t,ht,hm,ha⟩
    by_cases htu : t<u.length
    · have hd : (u++v).drop t=u.drop t++v := by
        rw [List.drop_append,show t-u.length=0 by omega,List.drop_zero]
      rw [hd,mass_append] at hm
      have hones := ones_drop_le u t
      have hb := ones_bounds (u.drop t)
      have he := mass_eq (u.drop t)
      omega
    · have hd : (u++v).drop t=v.drop (t-u.length) := by
        rw [List.drop_append,List.drop_eq_nil_of_le (by omega),List.nil_append]
      refine ⟨t-u.length,?_,?_,?_⟩
      · simp only [List.length_append] at ht
        omega
      · simpa only [hd] using hm
      · simpa only [hd] using ha
  · rintro ⟨t,ht,hm,ha⟩
    have hd : (u++v).drop (u.length+t)=v.drop t := by
      rw [List.drop_append,List.drop_eq_nil_of_le (by omega),List.nil_append,
        show u.length+t-u.length=t by omega]
    refine ⟨u.length+t,by simpa only [List.length_append] using Nat.add_lt_add_left ht u.length,?_,?_⟩
    · simpa only [hd] using hm
    · simpa only [hd] using ha

/-- A long S separator makes the next actual A's supply independent of an
arbitrary earlier tail u. The original block prefix and endpoint A remain. -/
theorem endable_after_prefix_manyS_A_iff (f : Nat → Bool)
    (n a m r j : Nat) (u : List Bool)
    {β : List Bool} (hβ : BlockWord β)
    (hseg : seg f 0 n=β++List.replicate a true) (hr : 1≤r)
    (hm : 2*ones u+2*(r : Int)-1≤(m : Int))
    (hw : seg f n (u.length+m+r+j)=
      u++(List.replicate m false++List.replicate r true++List.replicate j false))
    (hA : f (n+(u.length+m+r+j))=true) :
    EndN f 0 (n+(u.length+m+r+j)) ↔ r=2*(j+1) := by
  let v := List.replicate m false++List.replicate r true++List.replicate j false
  have hu := ones_bounds u
  have hbarrier : mass v+ones u≤0 := by
    simp only [v,mass_append,mass_rep_false,mass_replicate_A]
    omega
  have herase := localSupply_erase_prefix u v hbarrier
  have hl : Recaman.ThreeNonsuppliedData.localSupply (u++v)=true ↔ r=2*(j+1) := by
    rw [herase,localSupply_three_runs_iff]
    constructor
    · exact And.left
    · intro he
      exact ⟨he,by omega⟩
  constructor
  · intro he
    obtain ⟨_,t,l,ht0,htl,hwin⟩ := he
    by_cases htn : n≤t
    · apply hl.mp
      have hlocal := (localSupply_seg_iff f n (n+(u.length+m+r+j)) (by omega) hA).mpr
        ⟨hA,t,l,htn,htl,hwin⟩
      simpa only [Nat.add_sub_cancel_left,hw,v] using hlocal
    · have hwin' : Win f t (n+(u.length+m+r+j)-t) := by
        have heq : n+(u.length+m+r+j)-t=l := by omega
        simpa only [heq] using hwin
      have hc := old_window_count_barrier f n a t (n+(u.length+m+r+j)) hβ hseg
        (by omega) (by omega) hwin'
      rw [Nat.add_sub_cancel_left,hw] at hc
      simp only [ones_append,ones_replicate_S,ones_replicate_A] at hc
      omega
  · intro he
    apply end_mono f 0 n _ (Nat.zero_le _)
    apply (localSupply_seg_iff f n (n+(u.length+m+r+j)) (by omega) hA).mp
    rw [Nat.add_sub_cancel_left,hw]
    exact hl.mpr he

theorem no_endable_prefix_even_followup (f : Nat → Bool)
    (n a m k j : Nat) (u : List Bool)
    {β : List Bool} (hβ : BlockWord β)
    (hseg : seg f 0 n=β++List.replicate a true) (hk : 1≤k)
    (hm : 2*ones u+4*(k : Int)+1≤(m : Int))
    (hw : seg f n (u.length+(m+2*k+(k-1)+1+j))=
      u++evenFollowWord m k j) :
    ¬EndN f 0 (n+(u.length+(m+2*k+(k-1)+1+j))) := by
  have hu := ones_bounds u
  have hbarrier : mass (evenFollowWord m k j)+ones u≤0 := by
    simp only [evenFollowWord,mass_append,mass_rep_false,mass_replicate_A]
    omega
  have herase := localSupply_erase_prefix u (evenFollowWord m k j) hbarrier
  rw [localSupply_even_followup m k j hk] at herase
  intro he
  obtain ⟨hA,t,l,ht0,htl,hwin⟩ := he
  by_cases htn : n≤t
  · have hlocal := (localSupply_seg_iff f n _ (by omega) hA).mpr ⟨hA,t,l,htn,htl,hwin⟩
    rw [Nat.add_sub_cancel_left,hw,herase] at hlocal
    contradiction
  · have hwin' : Win f t (n+(u.length+(m+2*k+(k-1)+1+j))-t) := by
      have heq : n+(u.length+(m+2*k+(k-1)+1+j))-t=l := by omega
      simpa only [heq] using hwin
    have hc := old_window_count_barrier f n a t _ hβ hseg (by omega) (by omega) hwin'
    rw [Nat.add_sub_cancel_left,hw] at hc
    simp only [evenFollowWord,ones_append,ones_replicate_S,ones_replicate_A] at hc
    omega

theorem no_additions_prefix_even_followup (f : Nat → Bool)
    (n a m k K : Nat) (u : List Bool)
    {β : List Bool} (hβ : BlockWord β)
    (hseg : seg f 0 n=β++List.replicate a true) (hk : 1≤k)
    (hm : 2*ones u+4*(k : Int)+1≤(m : Int))
    (hw : seg f n (u.length+(m+2*k+(k-1)+1))=u++evenFollowWord m k 0)
    (hfree : cN (fun x => f x=true ∧ ¬EndN f 0 x)
      (n+(u.length+(m+2*k+(k-1)+1))) K=0) :
    cN (fun x => f x=true) (n+(u.length+(m+2*k+(k-1)+1))) K=0 := by
  let b := n+(u.length+(m+2*k+(k-1)+1))
  have hall : ∀ j, j<K → f (b+j)=false := by
    intro j
    induction j using Nat.strongRecOn with
    | ind j ih =>
      intro hjK
      cases hA : f (b+j)
      · rfl
      · have hnot := not_of_cN_zero (fun x => f x=true ∧ ¬EndN f 0 x) b K hfree
          (b+j) (by omega) (by omega)
        have he : EndN f 0 (b+j) := by
          apply Classical.byContradiction
          intro hn
          exact hnot ⟨hA,hn⟩
        have hgap : ∀ x, b≤x → x<b+j → f x=false := by
          intro x hbx hxj
          have h := ih (x-b) (by omega) (by omega)
          simpa only [Nat.add_sub_cancel' hbx] using h
        have hwj : seg f n (u.length+(m+2*k+(k-1)+1+j))=u++evenFollowWord m k j := by
          rw [show u.length+(m+2*k+(k-1)+1+j)=(u.length+(m+2*k+(k-1)+1))+j by omega,
            seg_add,hw,seg_false f b j hgap]
          simp only [evenFollowWord,List.replicate_zero,List.append_nil,List.append_assoc]
        have hn := no_endable_prefix_even_followup f n a m k j u hβ hseg hk hm hwj
        exact False.elim (hn (by simpa only [b,Nat.add_assoc] using he))
  apply cN_zero_of
  intro x hbx hxend
  have hf := hall (x-b) (by omega)
  rw [Nat.add_sub_cancel' hbx] at hf
  simp [hf]

/-- Arbitrary earlier tails are allowed. A sufficiently long separating S
run followed by an even A run permits at most one further A if no new
nonsupplied A is available, for every future length K. -/
theorem one_addition_after_prefix_manyS_evenA (f : Nat → Bool)
    (n a m k K : Nat) (u : List Bool)
    {β : List Bool} (hβ : BlockWord β)
    (hseg : seg f 0 n=β++List.replicate a true) (hk : 1≤k)
    (hm : 2*ones u+4*(k : Int)+1≤(m : Int))
    (hw : seg f n (u.length+m+2*k)=
      u++(List.replicate m false++List.replicate (2*k) true))
    (hfree : cN (fun x => f x=true ∧ ¬EndN f 0 x) (n+(u.length+m+2*k)) K=0) :
    cN (fun x => f x=true) (n+(u.length+m+2*k)) K≤1 := by
  let b := n+(u.length+m+2*k)
  change cN (fun x => f x=true ∧ ¬EndN f 0 x) b K=0 at hfree
  change cN (fun x => f x=true) b K≤1
  by_cases hex : ∃ j, j<K ∧ f (b+j)=true
  · obtain ⟨j,hjK,⟨hj,hA⟩,hfirst⟩ := first_mark
      (fun x => x<K ∧ f (b+x)=true) K
      (by obtain ⟨j,hj,ha⟩ := hex; exact ⟨j,by omega,hj,ha⟩)
    have hS : ∀ x, b≤x → x<b+j → f x=false := by
      intro x hbx hxj
      have hn := hfirst (x-b) (by omega)
      have hnot : f x≠true := by
        intro htrue
        apply hn
        exact ⟨by omega,by simpa only [Nat.add_sub_cancel' hbx] using htrue⟩
      cases hf : f x
      · rfl
      · exact False.elim (hnot hf)
    have hnot := not_of_cN_zero (fun x => f x=true ∧ ¬EndN f 0 x) b K hfree
      (b+j) (by omega) (by omega)
    have he : EndN f 0 (b+j) := by
      apply Classical.byContradiction
      intro hn
      exact hnot ⟨hA,hn⟩
    have hwj : seg f n (u.length+m+2*k+j)=
        u++(List.replicate m false++List.replicate (2*k) true++List.replicate j false) := by
      rw [seg_add,hw,seg_false f b j hS]
      simp only [List.append_assoc]
    have hu := ones_bounds u
    have heq := (endable_after_prefix_manyS_A_iff f n a m (2*k) j u hβ hseg
      (by omega) (by omega) hwj (by simpa only [b,Nat.add_assoc] using hA)).mp
      (by simpa only [b,Nat.add_assoc] using he)
    have hjk : j=k-1 := by omega
    have hbase : seg f n (u.length+(m+2*k+(k-1)+1))=u++evenFollowWord m k 0 := by
      rw [show u.length+(m+2*k+(k-1)+1)=(u.length+m+2*k+j)+1 by omega,
        seg_succ,hwj]
      have hA' : f (n+(u.length+m+2*k+j))=true := by simpa only [b,Nat.add_assoc] using hA
      rw [hA',hjk]
      simp only [evenFollowWord,List.replicate_zero,List.append_nil,List.replicate_one,List.append_assoc]
    have hA0 : cN (fun x => f x=true) b j=0 := by
      apply cN_zero_of
      intro x hbx hxj
      simp [hS x hbx hxj]
    have hA1 := cN_succ_pos (fun x => f x=true) b j hA
    have hsplit := cN_add (fun x => f x=true) b (j+1) (K-(j+1))
    have hfreeSplit := cN_add (fun x => f x=true ∧ ¬EndN f 0 x) b (j+1) (K-(j+1))
    have htime : b+(j+1)=n+(u.length+(m+2*k+(k-1)+1)) := by dsimp [b]; omega
    have hfreeTail : cN (fun x => f x=true ∧ ¬EndN f 0 x)
        (n+(u.length+(m+2*k+(k-1)+1))) (K-(j+1))=0 := by
      rw [Nat.add_sub_cancel' (by omega),htime] at hfreeSplit
      omega
    have hzero := no_additions_prefix_even_followup f n a m k (K-(j+1)) u hβ hseg hk hm hbase hfreeTail
    rw [Nat.add_sub_cancel' (by omega),htime] at hsplit
    omega
  · have hzero : cN (fun x => f x=true) b K=0 := by
      apply cN_zero_of
      intro x hbx hxK ha
      apply hex
      refine ⟨x-b,by omega,?_⟩
      simpa only [Nat.add_sub_cancel' hbx] using ha
    omega

/-- Maximum mass among all suffixes, including the empty suffix. -/
def suffixCeiling : List Bool → Int
  | [] => 0
  | c::w => max (mass (c::w)) (suffixCeiling w)

theorem suffixCeiling_nonnegative (w : List Bool) : 0≤suffixCeiling w := by
  induction w with
  | nil => decide
  | cons c w ih => simp only [suffixCeiling]; omega

theorem mass_drop_le_suffixCeiling (w : List Bool) (t : Nat) :
    mass (w.drop t)≤suffixCeiling w := by
  induction w generalizing t with
  | nil => simp [suffixCeiling]
  | cons c w ih =>
    cases t with
    | zero => simp only [List.drop_zero,suffixCeiling]; omega
    | succ t =>
      have h := ih t
      simp only [List.drop_succ_cons,suffixCeiling]
      omega

theorem localSupply_erase_prefix_ceiling (u v : List Bool)
    (hbarrier : mass v+suffixCeiling u≤0) :
    Recaman.ThreeNonsuppliedData.localSupply (u++v)=
      Recaman.ThreeNonsuppliedData.localSupply v := by
  apply Bool.eq_iff_iff.mpr
  rw [localSupply_iff,localSupply_iff]
  constructor
  · rintro ⟨t,ht,hm,ha⟩
    by_cases htu : t<u.length
    · have hd : (u++v).drop t=u.drop t++v := by
        rw [List.drop_append,show t-u.length=0 by omega,List.drop_zero]
      rw [hd,mass_append] at hm
      have hb := mass_drop_le_suffixCeiling u t
      omega
    · have hd : (u++v).drop t=v.drop (t-u.length) := by
        rw [List.drop_append,List.drop_eq_nil_of_le (by omega),List.nil_append]
      refine ⟨t-u.length,?_,?_,?_⟩
      · simp only [List.length_append] at ht
        omega
      · simpa only [hd] using hm
      · simpa only [hd] using ha
  · rintro ⟨t,ht,hm,ha⟩
    have hd : (u++v).drop (u.length+t)=v.drop t := by
      rw [List.drop_append,List.drop_eq_nil_of_le (by omega),List.nil_append,
        show u.length+t-u.length=t by omega]
    refine ⟨u.length+t,by simpa only [List.length_append] using Nat.add_lt_add_left ht u.length,?_,?_⟩
    · simpa only [hd] using hm
    · simpa only [hd] using ha

/-- The same discarded prefix is safe for every future word within the
remaining A budget, rather than just for the current endpoint. -/
theorem bounded_future_context_erasure (u v x : List Bool) (B : Nat)
    (hbarrier : mass v+suffixCeiling u+(B : Int)≤0)
    (hx : ones x≤(B : Int)) :
    Recaman.ThreeNonsuppliedData.localSupply ((u++v)++x)=
      Recaman.ThreeNonsuppliedData.localSupply (v++x) := by
  have hm := mass_eq x
  have hb := ones_bounds x
  have hmass : mass (v++x)+suffixCeiling u≤0 := by rw [mass_append]; omega
  simpa only [List.append_assoc] using localSupply_erase_prefix_ceiling u (v++x) hmass

def contextTrimAux (B : Nat) (w : List Bool) : Nat → List Bool
  | 0 => w
  | t+1 => if mass (w.drop (t+1))+suffixCeiling (w.take (t+1))+(B : Int)≤0
      then w.drop (t+1) else contextTrimAux B w t

def contextTrim (B : Nat) (w : List Bool) : List Bool := contextTrimAux B w w.length

theorem contextTrimAux_future (B : Nat) (w x : List Bool) (fuel : Nat)
    (hx : ones x≤(B : Int)) :
    Recaman.ThreeNonsuppliedData.localSupply (contextTrimAux B w fuel++x)=
      Recaman.ThreeNonsuppliedData.localSupply (w++x) := by
  induction fuel with
  | zero => rfl
  | succ t ih =>
    simp only [contextTrimAux]
    split
    · rename_i hb
      have h := bounded_future_context_erasure (w.take (t+1)) (w.drop (t+1)) x B hb hx
      rw [List.take_append_drop] at h
      exact h.symm
    · exact ih

theorem contextTrim_future (B : Nat) (w x : List Bool) (hx : ones x≤(B : Int)) :
    Recaman.ThreeNonsuppliedData.localSupply (contextTrim B w++x)=
      Recaman.ThreeNonsuppliedData.localSupply (w++x) := by
  exact contextTrimAux_future B w x w.length hx

/-- Every fixed negative buffer can lose a future supply if the remaining
A budget is discarded. This is a word counterfamily, not an orbit example. -/
theorem context_buffer_counterfamily (m : Nat) :
    mass (List.replicate m false)+suffixCeiling [false]= -(m : Int) ∧
    Recaman.ThreeNonsuppliedData.localSupply
      (([false]++List.replicate m false)++
        (List.replicate (2*(m+1)) true++List.replicate m false))=true ∧
    Recaman.ThreeNonsuppliedData.localSupply
      (List.replicate m false++
        (List.replicate (2*(m+1)) true++List.replicate m false))=false := by
  have hceil : suffixCeiling [false]=0 := by decide
  refine ⟨by rw [hceil,mass_rep_false]; omega,?_,?_⟩
  · have h := (localSupply_three_runs_iff (m+1) (2*(m+1)) m).mpr ⟨rfl,by omega⟩
    simpa only [List.replicate_succ,List.singleton_append,List.append_assoc] using h
  · cases h : Recaman.ThreeNonsuppliedData.localSupply
        (List.replicate m false++(List.replicate (2*(m+1)) true++List.replicate m false))
    · rfl
    · have h' := (localSupply_three_runs_iff m (2*(m+1)) m).mp
        (by simpa only [List.append_assoc] using h)
      omega

theorem no_unbounded_future_context_threshold :
    ¬∃ C : Nat, ∀ u v : List Bool, mass v+suffixCeiling u≤ -(C : Int) →
      ∀ x : List Bool, Recaman.ThreeNonsuppliedData.localSupply ((u++v)++x)=
        Recaman.ThreeNonsuppliedData.localSupply (v++x) := by
  rintro ⟨C,hC⟩
  obtain ⟨hm,hbefore,hafter⟩ := context_buffer_counterfamily C
  have h := hC [false] (List.replicate C false) (by omega)
    (List.replicate (2*(C+1)) true++List.replicate C false)
  rw [hbefore,hafter] at h
  contradiction

-- The threshold0 in the unrestricted word erasure cannot be relaxed to1.
theorem unit_barrier_counterexample :
    let u := [true]
    let v := [true,false,false,false,true,false,false,true,true,true]
    mass v+suffixCeiling u=1 ∧
      Recaman.ThreeNonsuppliedData.localSupply (u++v)=true ∧
      Recaman.ThreeNonsuppliedData.localSupply v=false := by decide

/-- Separate the local suffix-height obstruction from the total-S old-window
obstruction. Earlier S signs can contribute to the latter. -/
theorem endable_after_separated_run_iff (f : Nat → Bool)
    (n a m r j : Nat) (u : List Bool)
    {β : List Bool} (hβ : BlockWord β)
    (hseg : seg f 0 n=β++List.replicate a true) (hr : 1≤r)
    (hcut : suffixCeiling u+(r : Int)≤(m : Int))
    (hold : (u.length : Int)-ones u+(m : Int)≥2*(ones u+(r : Int))-1)
    (hw : seg f n (u.length+m+r+j)=
      u++(List.replicate m false++List.replicate r true++List.replicate j false))
    (hA : f (n+(u.length+m+r+j))=true) :
    EndN f 0 (n+(u.length+m+r+j)) ↔ r=2*(j+1) := by
  let v := List.replicate m false++List.replicate r true++List.replicate j false
  have hu := suffixCeiling_nonnegative u
  have hbarrier : mass v+suffixCeiling u≤0 := by
    simp only [v,mass_append,mass_rep_false,mass_replicate_A]
    omega
  have herase := localSupply_erase_prefix_ceiling u v hbarrier
  have hl : Recaman.ThreeNonsuppliedData.localSupply (u++v)=true ↔ r=2*(j+1) := by
    rw [herase,localSupply_three_runs_iff]
    exact ⟨And.left,fun he => ⟨he,by omega⟩⟩
  constructor
  · intro he
    obtain ⟨_,t,l,ht0,htl,hwin⟩ := he
    by_cases htn : n≤t
    · apply hl.mp
      have hlocal := (localSupply_seg_iff f n (n+(u.length+m+r+j)) (by omega) hA).mpr
        ⟨hA,t,l,htn,htl,hwin⟩
      simpa only [Nat.add_sub_cancel_left,hw,v] using hlocal
    · have hwin' : Win f t (n+(u.length+m+r+j)-t) := by
        have heq : n+(u.length+m+r+j)-t=l := by omega
        simpa only [heq] using hwin
      have hc := old_window_count_barrier f n a t (n+(u.length+m+r+j)) hβ hseg
        (by omega) (by omega) hwin'
      rw [Nat.add_sub_cancel_left,hw] at hc
      simp only [ones_append,ones_replicate_S,ones_replicate_A] at hc
      omega
  · intro he
    apply end_mono f 0 n _ (Nat.zero_le _)
    apply (localSupply_seg_iff f n (n+(u.length+m+r+j)) (by omega) hA).mp
    rw [Nat.add_sub_cancel_left,hw]
    exact hl.mpr he

theorem no_endable_separated_even_followup (f : Nat → Bool)
    (n a m k j : Nat) (u : List Bool)
    {β : List Bool} (hβ : BlockWord β)
    (hseg : seg f 0 n=β++List.replicate a true) (hk : 1≤k)
    (hcut : suffixCeiling u+(k : Int)+2≤(m : Int))
    (hold : (u.length : Int)-ones u+(m : Int)+((k-1 : Nat) : Int)≥
      2*(ones u+2*(k : Int)+1)-1)
    (hw : seg f n (u.length+(m+2*k+(k-1)+1+j))=u++evenFollowWord m k j) :
    ¬EndN f 0 (n+(u.length+(m+2*k+(k-1)+1+j))) := by
  have hbarrier : mass (evenFollowWord m k j)+suffixCeiling u≤0 := by
    simp only [evenFollowWord,mass_append,mass_rep_false,mass_replicate_A]
    omega
  have herase := localSupply_erase_prefix_ceiling u (evenFollowWord m k j) hbarrier
  rw [localSupply_even_followup m k j hk] at herase
  intro he
  obtain ⟨hA,t,l,ht0,htl,hwin⟩ := he
  by_cases htn : n≤t
  · have hlocal := (localSupply_seg_iff f n _ (by omega) hA).mpr ⟨hA,t,l,htn,htl,hwin⟩
    rw [Nat.add_sub_cancel_left,hw,herase] at hlocal
    contradiction
  · have hwin' : Win f t (n+(u.length+(m+2*k+(k-1)+1+j))-t) := by
      have heq : n+(u.length+(m+2*k+(k-1)+1+j))-t=l := by omega
      simpa only [heq] using hwin
    have hc := old_window_count_barrier f n a t _ hβ hseg (by omega) (by omega) hwin'
    rw [Nat.add_sub_cancel_left,hw] at hc
    simp only [evenFollowWord,ones_append,ones_replicate_S,ones_replicate_A] at hc
    omega


theorem no_additions_separated_even_followup (f : Nat → Bool)
    (n a m k K : Nat) (u : List Bool)
    {β : List Bool} (hβ : BlockWord β)
    (hseg : seg f 0 n=β++List.replicate a true) (hk : 1≤k)
    (hcut : suffixCeiling u+(k : Int)+2≤(m : Int))
    (hold : (u.length : Int)-ones u+(m : Int)+((k-1 : Nat) : Int)≥
      2*(ones u+2*(k : Int)+1)-1)
    (hw : seg f n (u.length+(m+2*k+(k-1)+1))=u++evenFollowWord m k 0)
    (hfree : cN (fun x => f x=true ∧ ¬EndN f 0 x)
      (n+(u.length+(m+2*k+(k-1)+1))) K=0) :
    cN (fun x => f x=true) (n+(u.length+(m+2*k+(k-1)+1))) K=0 := by
  let b := n+(u.length+(m+2*k+(k-1)+1))
  have hall : ∀ j, j<K → f (b+j)=false := by
    intro j
    induction j using Nat.strongRecOn with
    | ind j ih =>
      intro hjK
      cases hA : f (b+j)
      · rfl
      · have hnot := not_of_cN_zero (fun x => f x=true ∧ ¬EndN f 0 x) b K hfree
          (b+j) (by omega) (by omega)
        have he : EndN f 0 (b+j) := by
          apply Classical.byContradiction
          intro hn
          exact hnot ⟨hA,hn⟩
        have hgap : ∀ x, b≤x → x<b+j → f x=false := by
          intro x hbx hxj
          have h := ih (x-b) (by omega) (by omega)
          simpa only [Nat.add_sub_cancel' hbx] using h
        have hwj : seg f n (u.length+(m+2*k+(k-1)+1+j))=u++evenFollowWord m k j := by
          rw [show u.length+(m+2*k+(k-1)+1+j)=(u.length+(m+2*k+(k-1)+1))+j by omega,
            seg_add,hw,seg_false f b j hgap]
          simp only [evenFollowWord,List.replicate_zero,List.append_nil,List.append_assoc]
        have hn := no_endable_separated_even_followup f n a m k j u hβ hseg hk hcut hold hwj
        exact False.elim (hn (by simpa only [b,Nat.add_assoc] using he))
  apply cN_zero_of
  intro x hbx hxend
  have hf := hall (x-b) (by omega)
  rw [Nat.add_sub_cancel' hbx] at hf
  simp [hf]

theorem one_addition_after_separated_evenA (f : Nat → Bool)
    (n a m k K : Nat) (u : List Bool)
    {β : List Bool} (hβ : BlockWord β)
    (hseg : seg f 0 n=β++List.replicate a true) (hk : 1≤k)
    (hcut0 : suffixCeiling u+2*(k : Int)≤(m : Int))
    (hcut1 : suffixCeiling u+(k : Int)+2≤(m : Int))
    (hold0 : (u.length : Int)-ones u+(m : Int)≥2*(ones u+2*(k : Int))-1)
    (hold1 : (u.length : Int)-ones u+(m : Int)+((k-1 : Nat) : Int)≥
      2*(ones u+2*(k : Int)+1)-1)
    (hw : seg f n (u.length+m+2*k)=
      u++(List.replicate m false++List.replicate (2*k) true))
    (hfree : cN (fun x => f x=true ∧ ¬EndN f 0 x) (n+(u.length+m+2*k)) K=0) :
    cN (fun x => f x=true) (n+(u.length+m+2*k)) K≤1 := by
  let b := n+(u.length+m+2*k)
  change cN (fun x => f x=true ∧ ¬EndN f 0 x) b K=0 at hfree
  change cN (fun x => f x=true) b K≤1
  by_cases hex : ∃ j, j<K ∧ f (b+j)=true
  · obtain ⟨j,hjK,⟨hj,hA⟩,hfirst⟩ := first_mark
      (fun x => x<K ∧ f (b+x)=true) K
      (by obtain ⟨j,hj,ha⟩ := hex; exact ⟨j,by omega,hj,ha⟩)
    have hS : ∀ x, b≤x → x<b+j → f x=false := by
      intro x hbx hxj
      have hn := hfirst (x-b) (by omega)
      have hnot : f x≠true := by
        intro htrue
        apply hn
        exact ⟨by omega,by simpa only [Nat.add_sub_cancel' hbx] using htrue⟩
      cases hf : f x
      · rfl
      · exact False.elim (hnot hf)
    have hnot := not_of_cN_zero (fun x => f x=true ∧ ¬EndN f 0 x) b K hfree
      (b+j) (by omega) (by omega)
    have he : EndN f 0 (b+j) := by
      apply Classical.byContradiction
      intro hn
      exact hnot ⟨hA,hn⟩
    have hwj : seg f n (u.length+m+2*k+j)=
        u++(List.replicate m false++List.replicate (2*k) true++List.replicate j false) := by
      rw [seg_add,hw,seg_false f b j hS]
      simp only [List.append_assoc]
    have hu := ones_bounds u
    have heq := (endable_after_separated_run_iff f n a m (2*k) j u hβ hseg
      (by omega) (by omega) (by omega) hwj (by simpa only [b,Nat.add_assoc] using hA)).mp
      (by simpa only [b,Nat.add_assoc] using he)
    have hjk : j=k-1 := by omega
    have hbase : seg f n (u.length+(m+2*k+(k-1)+1))=u++evenFollowWord m k 0 := by
      rw [show u.length+(m+2*k+(k-1)+1)=(u.length+m+2*k+j)+1 by omega,
        seg_succ,hwj]
      have hA' : f (n+(u.length+m+2*k+j))=true := by simpa only [b,Nat.add_assoc] using hA
      rw [hA',hjk]
      simp only [evenFollowWord,List.replicate_zero,List.append_nil,List.replicate_one,List.append_assoc]
    have hA0 : cN (fun x => f x=true) b j=0 := by
      apply cN_zero_of
      intro x hbx hxj
      simp [hS x hbx hxj]
    have hA1 := cN_succ_pos (fun x => f x=true) b j hA
    have hsplit := cN_add (fun x => f x=true) b (j+1) (K-(j+1))
    have hfreeSplit := cN_add (fun x => f x=true ∧ ¬EndN f 0 x) b (j+1) (K-(j+1))
    have htime : b+(j+1)=n+(u.length+(m+2*k+(k-1)+1)) := by dsimp [b]; omega
    have hfreeTail : cN (fun x => f x=true ∧ ¬EndN f 0 x)
        (n+(u.length+(m+2*k+(k-1)+1))) (K-(j+1))=0 := by
      rw [Nat.add_sub_cancel' (by omega),htime] at hfreeSplit
      omega
    have hzero := no_additions_separated_even_followup f n a m k (K-(j+1)) u hβ hseg hk hcut1 hold1 hbase hfreeTail
    rw [Nat.add_sub_cancel' (by omega),htime] at hsplit
    omega
  · have hzero : cN (fun x => f x=true) b K=0 := by
      apply cN_zero_of
      intro x hbx hxK ha
      apply hex
      refine ⟨x-b,by omega,?_⟩
      simpa only [Nat.add_sub_cancel' hbx] using ha
    omega

theorem suffixCeiling_prepend_S (w : List Bool) :
    suffixCeiling (false::w)=suffixCeiling w := by
  have h := mass_drop_le_suffixCeiling w 0
  simp only [List.drop_zero] at h
  change max (-1+mass w) (suffixCeiling w)=suffixCeiling w
  omega

theorem suffixCeiling_S_prefix (m : Nat) (w : List Bool) :
    suffixCeiling (List.replicate m false++w)=suffixCeiling w := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.replicate_succ,List.cons_append,suffixCeiling_prepend_S,ih]

theorem suffixCeiling_A_run (m : Nat) : suffixCeiling (List.replicate m true)=(m : Int) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.replicate_succ]
    change max (mass (true::List.replicate m true)) (suffixCeiling (List.replicate m true))=_
    rw [mass_cons,mass_replicate_A,ih]
    change max (1+(m : Int)) (m : Int)=((m+1 : Nat) : Int)
    omega

/-- A two-A-run family with unbounded earlier run and arbitrary old block
prefix. The separating S run need only be M+3, rather than2M+5. -/
theorem one_addition_after_two_A_runs (f : Nat → Bool) (n a h M m K : Nat)
    {β : List Bool} (hβ : BlockWord β)
    (hseg : seg f 0 n=β++List.replicate a true) (hh : M+2≤h) (hm : M+3≤m)
    (hw : seg f n (h+M+m+2)=List.replicate h false++List.replicate M true++
      List.replicate m false++List.replicate 2 true)
    (hfree : cN (fun x => f x=true ∧ ¬EndN f 0 x) (n+(h+M+m+2)) K=0) :
    cN (fun x => f x=true) (n+(h+M+m+2)) K≤1 := by
  let u := List.replicate h false++List.replicate M true
  have hceil : suffixCeiling u=(M : Int) := by
    exact (suffixCeiling_S_prefix h _).trans (suffixCeiling_A_run M)
  have hw' : seg f n (u.length+m+2*1)=
      u++(List.replicate m false++List.replicate (2*1) true) := by
    simpa only [u,List.length_append,List.length_replicate,List.append_assoc] using hw
  have hfree' : cN (fun x => f x=true ∧ ¬EndN f 0 x) (n+(u.length+m+2*1)) K=0 := by
    simpa only [u,List.length_append,List.length_replicate] using hfree
  have hres := one_addition_after_separated_evenA f n a m 1 K u hβ hseg (by decide)
    (by rw [hceil]; omega) (by rw [hceil]; omega)
    (by simp only [u,List.length_append,List.length_replicate,ones_append,ones_replicate_S,ones_replicate_A]; omega)
    (by simp only [u,List.length_append,List.length_replicate,ones_append,ones_replicate_S,ones_replicate_A]; omega)
    hw' hfree'
  simpa only [u,List.length_append,List.length_replicate] using hres

def supplyGapKey (w : List Bool) : Int := 2*areaW w+mass w*(mass w-1)

theorem supplyGapKey_append_S (w : List Bool) (j : Nat) :
    supplyGapKey (w++List.replicate j false)=supplyGapKey w := by
  have h := twice_area_replicate_S j
  simp only [supplyGapKey,areaW_append,mass_append,mass_rep_false,List.length_replicate]
  grind

theorem localSupply_gap_key_iff (w : List Bool) (j : Nat) :
    Recaman.ThreeNonsuppliedData.localSupply (w++List.replicate j false)=true ↔
      ∃ t, t<w.length ∧ mass (w.drop t)=(j : Int)+1 ∧ supplyGapKey (w.drop t)=0 := by
  rw [localSupply_iff]
  constructor
  · rintro ⟨t,ht,hm,ha⟩
    rw [checked_wordArea_eq] at ha
    by_cases htu : t<w.length
    · have hd : (w++List.replicate j false).drop t=w.drop t++List.replicate j false := by
        rw [List.drop_append,show t-w.length=0 by omega,List.drop_zero]
      rw [hd] at hm ha
      have hm' := hm
      rw [mass_append,mass_rep_false] at hm'
      have hz : supplyGapKey (w.drop t++List.replicate j false)=0 := by
        rw [supplyGapKey,hm,ha]
        decide
      rw [supplyGapKey_append_S] at hz
      exact ⟨t,htu,by omega,hz⟩
    · have hd : (w++List.replicate j false).drop t=List.replicate (j-(t-w.length)) false := by
        rw [List.drop_append,List.drop_eq_nil_of_le (by omega),List.nil_append,List.drop_replicate]
      rw [hd,mass_rep_false] at hm
      omega
  · rintro ⟨t,ht,hm,hk⟩
    have hd : (w++List.replicate j false).drop t=w.drop t++List.replicate j false := by
      rw [List.drop_append,show t-w.length=0 by omega,List.drop_zero]
    have hm' : mass (w.drop t++List.replicate j false)=1 := by
      rw [mass_append,mass_rep_false,hm]
      omega
    have hz : supplyGapKey (w.drop t++List.replicate j false)=0 := by
      rw [supplyGapKey_append_S,hk]
    have ha : areaW (w.drop t++List.replicate j false)=0 := by
      unfold supplyGapKey at hz
      rw [hm'] at hz
      omega
    refine ⟨t,by simp only [List.length_append,List.length_replicate]; omega,?_,?_⟩
    · simpa only [hd] using hm'
    · rw [checked_wordArea_eq,hd]
      exact ha

theorem positive_zero_gap_key_count (w : List Bool) (hm : 0<mass w)
    (hk : supplyGapKey w=0) : 2*mass w≤ones w := by
  have hb := ones_bounds w
  have he := mass_eq w
  have hl := areaW_count_lower w
  have hp : 0<ones w := by omega
  have hpoly : 0≤ones w*(ones w-2*mass w) := by
    have hs : (w.length : Int)-ones w=ones w-mass w := by omega
    rw [hs] at hl
    have hc : ones w*(ones w+1)-(ones w-mass w)*(ones w-mass w+1)-
        2*ones w*(ones w-mass w)=
        -(mass w*(mass w-1))-2*(ones w*(ones w-2*mass w)) := by grind
    rw [hc] at hl
    unfold supplyGapKey at hk
    omega
  by_cases hle : 2*mass w≤ones w
  · exact hle
  · have hn := Int.mul_neg_of_pos_of_neg hp (show ones w-2*mass w<0 by omega)
    omega

theorem localSupply_gap_half_bound (w : List Bool) (j : Nat)
    (h : Recaman.ThreeNonsuppliedData.localSupply (w++List.replicate j false)=true) :
    2*(j : Int)+2≤ones w := by
  obtain ⟨t,ht,hm,hk⟩ := (localSupply_gap_key_iff w j).mp h
  have hb := positive_zero_gap_key_count (w.drop t) (by omega) hk
  have hc := ones_drop_le w t
  omega

theorem oldSignature_gap_half_bound (w : List Bool) (j : Nat)
    (h : Recaman.ThreeNonsuppliedData.oldSignature (w++List.replicate j false)=true) :
    2*(j : Int)+2≤ones w := by
  let A := ones w
  let N := (w.length : Int)-A+(j : Int)
  let V := w++List.replicate j false
  let lowerW := A*(A+1)-((w.length : Int)-A)*((w.length : Int)-A+1)-
    2*A*((w.length : Int)-A)
  have hb := ones_bounds w
  have hN : 0≤N := by dsimp [N,A]; omega
  have hmass : mass V=A-N := by
    change mass (w++List.replicate j false)=A-N
    rw [mass_append,mass_rep_false,mass_eq w]
    dsimp [A,N]
    omega
  have hlen : (V.length : Int)=A+N := by
    simp only [V,List.length_append,List.length_replicate,Int.natCast_add]
    dsimp [N]
    omega
  simp only [Recaman.ThreeNonsuppliedData.oldSignature,decide_eq_true_eq,
    checked_wordArea_eq] at h
  change 1≤1-mass V ∧ 1≤ -areaW V-(V.length : Int)*(1-mass V) ∧
    (1-mass V)*(1-mass V+1)≤2*(-areaW V-(V.length : Int)*(1-mass V))+2 ∧ _ at h
  rw [hmass,hlen] at h
  have hR : A≤N := by omega
  have hB : 1≤ -areaW V-(A+N)*(1-A+N) := by
    have he : 1-(A-N)=1-A+N := by omega
    simpa only [he] using h.2.1
  have hlo : (1-A+N)*(1-A+N+1)+2*areaW V+2*((A+N)*(1-A+N))-2≤0 := by
    have he : 1-(A-N)=1-A+N := by omega
    have ht := h.2.2.1
    rw [he] at ht
    omega
  have hlower : lowerW≤2*areaW w := areaW_count_lower w
  have hid : (1-A+N)*(1-A+N+1)+2*areaW V+2*((A+N)*(1-A+N))-2=
      2*(N*(N-2*A+2)+2*A*(j : Int))+(2*areaW w-lowerW) := by
    have har : areaW V=areaW w+(j : Int)*mass w+areaW (List.replicate j false) := by
      simp only [V,areaW_append,List.length_replicate]
    have hs := twice_area_replicate_S j
    have hm := mass_eq w
    rw [har]
    dsimp [A,N,lowerW]
    grind
  have hquad : N*(N-2*A+2)+2*A*(j : Int)≤0 := by rw [hid] at hlo; omega
  have hA : 2≤A := by
    by_cases ha0 : A=0
    · have hc : N*(N-2*A+2)+2*A*(j : Int)=N*N+2*N := by rw [ha0]; grind
      rw [hc] at hquad
      have hs : 0≤N*N := Int.mul_nonneg hN hN
      have hn0 : N=0 := by omega
      have hv0 : V=[] := List.length_eq_zero_iff.mp (by omega)
      have har0 : areaW V=0 := by rw [hv0]; rfl
      rw [har0,ha0,hn0] at hB
      omega
    · by_cases ha1 : A=1
      · have hc : N*(N-2*A+2)+2*A*(j : Int)=N*N+2*(j : Int) := by rw [ha1]; grind
        rw [hc] at hquad
        have hs : 0<N*N := Int.mul_pos (by omega) (by omega)
        omega
      · dsimp [A] at *
        omega
  have hmax : 2*A*(j : Int)≤(A-1)*(A-1) := by
    have hs : 0≤(N-(A-1))*(N-(A-1)) := by
      by_cases hz : 0≤N-(A-1)
      · exact Int.mul_nonneg hz hz
      · have hz' : 0≤ -(N-(A-1)) := by omega
        have hp := Int.mul_nonneg hz' hz'
        have he : (-(N-(A-1)))*(-(N-(A-1)))=(N-(A-1))*(N-(A-1)) := by grind
        rwa [he] at hp
    have hc : (N-(A-1))*(N-(A-1))=N*(N-2*A+2)+(A-1)*(A-1) := by grind
    rw [hc] at hs
    omega
  change 2*(j : Int)+2≤A
  by_cases hle : 2*(j : Int)+2≤A
  · exact hle
  · have hp := Int.mul_nonneg (show 0≤A by omega) (show 0≤2*(j : Int)+1-A by omega)
    have he : A*(2*(j : Int)+1-A)=2*A*(j : Int)-A*(A-1) := by grind
    rw [he] at hp
    have hsq : (A-1)*(A-1)=A*(A-1)-A+1 := by grind
    rw [hsq] at hmax
    omega

theorem wordSupply_gap_half_bound (w : List Bool) (j : Nat)
    (h : (Recaman.ThreeNonsuppliedData.localSupply (w++List.replicate j false) ||
      Recaman.ThreeNonsuppliedData.oldSignature (w++List.replicate j false))=true) :
    2*(j : Int)+2≤ones w := by
  rw [Bool.or_eq_true] at h
  rcases h with hl|ho
  · exact localSupply_gap_half_bound w j hl
  · exact oldSignature_gap_half_bound w j ho

/-- Every actually supplied A after an S-only gap obeys the sharp half-count
bound. The count is all earlier A signs, not just nonsupplied ones. -/
theorem supplied_after_S_gap_half_bound (f : Nat → Bool) (n a b j : Nat)
    {β : List Bool} (hβ : BlockWord β)
    (hseg : seg f 0 n=β++List.replicate a true) (hnb : n<b)
    (hS : ∀ x, b≤x → x<b+j → f x=false) (he : EndN f 0 (b+j)) :
    2*(j : Int)+2≤ones (seg f n (b-n)) := by
  have hword : seg f n (b+j-n)=seg f n (b-n)++List.replicate j false := by
    have h := seg_add f n (b-n) j
    rw [show n+(b-n)=b by omega,seg_false f b j hS] at h
    simpa only [show b-n+j=b+j-n by omega] using h
  have hadmit := wordSupply_admitted f n a (b+j) hβ hseg (by omega) he.1 true he
  change (Recaman.ThreeNonsuppliedData.localSupply (seg f n (b+j-n)) ||
    Recaman.ThreeNonsuppliedData.oldSignature (seg f n (b+j-n)))=true at hadmit
  rw [hword] at hadmit
  exact wordSupply_gap_half_bound _ j hadmit

theorem sharp_half_gap_family (j : Nat) :
    let w := List.replicate (j+1) false++List.replicate (2*(j+1)) true
    ones w=2*(j : Int)+2 ∧
      Recaman.ThreeNonsuppliedData.localSupply (w++List.replicate j false)=true := by
  dsimp only
  constructor
  · simp only [ones_append,ones_replicate_S,ones_replicate_A]
    omega
  · exact (localSupply_three_runs_iff (j+1) (2*(j+1)) j).mpr ⟨rfl,Nat.le_refl _⟩

end Recaman.PrefixMassBarrier
