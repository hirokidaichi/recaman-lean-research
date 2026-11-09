import Recaman.TripleRunClockResidue
import Recaman.RunSupplyBudget

namespace Recaman.TripleRunLocalClockCut

open Recaman.TripleRunClockResidue Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity
open Recaman.RunSupplyKeys Recaman.BlockOldRay Recaman.SingleWindowEquality Recaman.RunSupplyBudget

private theorem triple_drop_profile (hs : List Nat) (h t : Nat) :
    ∃ r hs' h', (tripleRuns hs++List.replicate h false).drop t=
      (List.replicate r true++tripleRuns hs')++List.replicate h' false := by
  induction hs generalizing t with
  | nil =>
    exact ⟨0,[],h-t,by simp [tripleRuns]⟩
  | cons s hs ih =>
    change ∃ r hs' h', (((List.replicate s false++List.replicate 3 true)++
      tripleRuns hs)++List.replicate h false).drop t=_
    rw [List.append_assoc,List.append_assoc]
    by_cases hS : t≤s
    · refine ⟨0,(s-t)::hs,h,?_⟩
      rw [List.drop_append_of_le_length (by simpa only [List.length_replicate] using hS),
        List.drop_replicate]
      simp only [tripleRuns,List.replicate_zero,List.nil_append,List.append_assoc]
    · rw [List.drop_append,List.drop_eq_nil_of_le (by simp; omega),List.nil_append,
        List.length_replicate]
      by_cases hA : t-s≤3
      · refine ⟨3-(t-s),hs,h,?_⟩
        rw [List.drop_append_of_le_length (by simpa only [List.length_replicate] using hA),
          List.drop_replicate,List.append_assoc]
      · rw [List.drop_append,List.drop_eq_nil_of_le (by simp; omega),List.nil_append,
          List.length_replicate]
        exact ih (t-s-3)

theorem triple_local_residue_one_excluded (hs : List Nat) (h i : Nat) (hi : i%3=1) :
    Recaman.ThreeNonsuppliedData.localSupply
      ((tripleRuns hs++List.replicate h false)++List.replicate i true)=false := by
  let u:=tripleRuns hs++List.replicate h false
  change Recaman.ThreeNonsuppliedData.localSupply (u++List.replicate i true)=false
  cases he : Recaman.ThreeNonsuppliedData.localSupply (u++List.replicate i true) with
  | false => rfl
  | true =>
    have he' : Recaman.ThreeNonsuppliedData.localSupply
        (u++List.replicate i true++List.replicate 0 false)=true := by
      simpa only [List.replicate_zero,List.append_nil] using he
    obtain ⟨t,_,hm,hk⟩:=(localSupply_A_S_iff u i 0).mp he'
    obtain ⟨r,hs',h',hd⟩:=triple_drop_profile hs h t
    change u.drop t=(List.replicate r true++tripleRuns hs')++List.replicate h' false at hd
    rw [hd] at hm hk
    exact (triple_run_residue_one_excluded hs' r h' i hi (by omega) (by omega)).elim

/-- All original EndN at these clocks have a source before the
three-A-run tail. Old sources remain unrestricted. -/
theorem actual_triple_run_residue_only_old (f : Nat → Bool) (B i : Nat) (w : List Bool)
    (hs : List Nat) (h : Nat) (hi : i%3=1)
    (hpre : seg f 0 B=w++(tripleRuns hs++List.replicate h false))
    (hA : ∀ k, k<i → f (B+k)=true) (he : EndN f 0 (B+i)) :
    tailOldRay w (tripleRuns hs++List.replicate h false) i := by
  have ha : seg f B i=List.replicate i true := by
    apply seg_A
    intro t ht hti
    have h:=hA (t-B) (by omega)
    rwa [Nat.add_sub_cancel' ht] at h
  have hseg:=seg_add f 0 B i
  rw [Nat.zero_add,hpre,ha] at hseg
  have hloc:=(localSupply_seg_iff f 0 (B+i) (Nat.zero_le _) he.1).mpr he
  rw [Nat.sub_zero,hseg] at hloc
  rcases (ray_supply_append_iff w (tripleRuns hs++List.replicate h false) i).mp hloc with h|h
  · exact h
  · rw [triple_local_residue_one_excluded hs _ i hi] at h
    cases h

end Recaman.TripleRunLocalClockCut
