import Recaman.OldSourceNegativeThreshold
import Recaman.AdditionRankSlack

namespace Recaman.ThresholdPrefixFreeCount

open Recaman.AdditionRankSlack Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity
open Recaman.RunSupplyKeys Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality
open Recaman.LineCapacityPeriodic

/-- This position is an addition with neither a local source nor a key
negative enough for an old BlockWord source. -/
def certifiedFreeAt (x : List Bool) (t : Nat) : Bool :=
  decide (x[t]?=some true ∧ -4*(cntF (x.take t) : Int)≤runKey (x.take t) ∧
    Recaman.ThreeNonsuppliedData.localSupply (x.take t)=false)

theorem count_range (g : Nat → Bool) (n K : Nat) :
    cN (fun x=>g (x-n)=true) n K=(List.range K).countP g := by
  induction K with
  | zero => rfl
  | succ K ih =>
    rw [List.range_succ,List.countP_append]
    cases hg : g K with
    | false =>
      have h : ¬g (n+K-n)=true := by rw [Nat.add_sub_cancel_left,hg]; decide
      rw [cN_succ_neg _ n K h,ih]
      simp [hg]
    | true =>
      have h : g (n+K-n)=true := by rw [Nat.add_sub_cancel_left,hg]
      rw [cN_succ_pos _ n K h,ih]
      simp [hg]

/-- Each certified position contributes one distinct original free addition. -/
theorem certified_prefix_free_count (f : Nat → Bool) (n K : Nat) (w x : List Bool)
    (hw : BlockWord w) (hpre : seg f 0 n=w) (hseg : seg f n K=x) :
    (List.range K).countP (certifiedFreeAt x)≤free f n K := by
  rw [← count_range (certifiedFreeAt x) n K]
  unfold free
  apply cN_mono
  intro t hnt htk hc
  obtain ⟨hA,hK,hL⟩:=of_decide_eq_true hc
  have hclock : n+(t-n)=t := Nat.add_sub_cancel' hnt
  have hget := seg_get f n K (t-n) (by omega)
  rw [hseg,hclock,hA] at hget
  have ha : f t=true := (Option.some.inj hget).symm
  have ht := seg_take f n K (t-n) (by omega)
  rw [hseg] at ht
  have he := Recaman.OldSourceNegativeThreshold.actual_free_above_old_threshold
    f n (t-n) w (x.take (t-n)) hw hpre ht.symm
      (by rw [hclock]; exact ha) hK hL
  rw [hclock] at he
  exact ⟨ha,he⟩

/-- These three early words each force at least four original free
additions, even with an unbounded old BlockWord. -/
theorem four_free_short_prefixes (f : Nat → Bool) (n K : Nat) (w : List Bool)
    (hw : BlockWord w) (hpre : seg f 0 n=w)
    (hshape : (K=6 ∧ seg f n K=[false,true,true,false,true,true]) ∨
      (K=8 ∧ seg f n K=[false,true,false,true,true,true,false,true]) ∨
      (K=7 ∧ seg f n K=[false,true,true,false,true,false,true])) :
    4≤free f n K := by
  rcases hshape with ⟨rfl,h⟩|⟨rfl,h⟩|⟨rfl,h⟩
  · exact Nat.le_trans (by decide) (certified_prefix_free_count f n 6 w _ hw hpre h)
  · exact Nat.le_trans (by decide) (certified_prefix_free_count f n 8 w _ hw hpre h)
  · exact Nat.le_trans (by decide) (certified_prefix_free_count f n 7 w _ hw hpre h)

end Recaman.ThresholdPrefixFreeCount
