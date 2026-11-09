import Recaman.DeficitRecordPredecessor
import Recaman.InitialSPaddingPositive

namespace Recaman.DeficitRecordControl

open Recaman.DeficitRecordSourceCharge Recaman.SourceDeficitBand Recaman.ShortSourceTriples
open Recaman.AdditionRankSlack Recaman.SingleWindowEquality Recaman.BlockSuffixPositivity
open Recaman.InitialSPaddingPositive

private def old1 : List Bool := [false,false,true,true,true,true]
private def neutral : List Bool := [true,false,false,false,true,true]
private def old2 : List Bool := neutral++old1
private def old3 : List Bool := [false]++List.replicate 5 true++List.replicate 5 false++old2
private def old4 : List Bool := neutral++old3

def recordSign : Nat → Bool :=
  finiteSign (old4++[false,true,false,true,true,false,true])

private theorem supplied_literal (t : Nat)
    (ht : t=30 ∨ t=32 ∨ t=33 ∨ t=35 ∨ t=36) : EndN recordSign 0 t := by
  rcases ht with rfl|rfl|rfl|rfl|rfl
  · exact (localSupply_seg_iff recordSign 0 30 (by decide) (by decide)).mp (by decide)
  · exact (localSupply_seg_iff recordSign 0 32 (by decide) (by decide)).mp (by decide)
  · exact (localSupply_seg_iff recordSign 0 33 (by decide) (by decide)).mp (by decide)
  · exact (localSupply_seg_iff recordSign 0 35 (by decide) (by decide)).mp (by decide)
  · exact (localSupply_seg_iff recordSign 0 36 (by decide) (by decide)).mp (by decide)

/-- A nonshort local supply really can set a strict new deficit minimum
on an interior interval. The exact high witness is an original S. -/
theorem actual_nonshort_record_control :
    localRecord recordSign 29 36 ∧ recordSubtraction recordSign 29 34 ∧
      free recordSign 29 8=0 := by
  have hz : free recordSign 29 8=0 := by
    unfold free
    apply cN_zero_of
    intro t hnt ht he
    have h : t=29 ∨ t=30 ∨ t=31 ∨ t=32 ∨ t=33 ∨ t=34 ∨ t=35 ∨ t=36 := by omega
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact (by decide : recordSign 29≠true) he.1
    · exact he.2 (supplied_literal 30 (by decide))
    · exact (by decide : recordSign 31≠true) he.1
    · exact he.2 (supplied_literal 32 (by decide))
    · exact he.2 (supplied_literal 33 (by decide))
    · exact (by decide : recordSign 34≠true) he.1
    · exact he.2 (supplied_literal 35 (by decide))
    · exact he.2 (supplied_literal 36 (by decide))
  have hF (t : Nat) (hnt : 29≤t) (ht : t≤37) : free recordSign 0 t=free recordSign 0 29 := by
    have h0:=free_prefix_mono recordSign 29 (t-29) 8 (by omega)
    have h:=cN_add (fun x=>recordSign x=true ∧ ¬EndN recordSign 0 x) 0 29 (t-29)
    rw [Nat.zero_add,Nat.add_sub_cancel' hnt] at h
    change free recordSign 0 t=free recordSign 0 29+free recordSign 29 (t-29) at h
    omega
  have hD (t : Nat) (hnt : 29≤t) (ht : t≤36) :
      deficit recordSign 37<deficit recordSign t := by
    have hFw : Fw recordSign t<Fw recordSign 37 := by
      have he : t=29 ∨ t=30 ∨ t=31 ∨ t=32 ∨ t=33 ∨ t=34 ∨ t=35 ∨ t=36 := by omega
      rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    have h1:=walk_eq_free_sub_deficit recordSign t
    have h2:=walk_eq_free_sub_deficit recordSign 37
    rw [hF t hnt (by omega)] at h1
    rw [hF 37 (by decide) (by decide)] at h2
    omega
  have hWin : Win recordSign 29 (36-29) := by unfold Win; decide
  have hR : localRecord recordSign 29 36 :=
    ⟨supplied_literal 36 (by decide),
      fun hs=> (by decide : recordSign 33≠false) hs.2.1,
      hD,29,by decide,by decide,hWin⟩
  exact ⟨hR,⟨by decide,36,29,by decide,hR,by decide,by decide,hWin,by decide⟩,hz⟩

/-- Both positions charged to the record occur in the next short triple. -/
theorem record_pair_overlaps_short_triple :
    localRecord recordSign 29 36 ∧ EndN recordSign 0 35 ∧
      shortEndpoint recordSign 29 37 ∧
      37-2=35 ∧ 37-1=36 := by
  have hr:=actual_nonshort_record_control.1
  have hp:=(Recaman.DeficitRecordPredecessor.local_record_supplied_predecessor recordSign 29 36 hr).2.1
  have hs : shortEndpoint recordSign 29 37 := by unfold shortEndpoint; decide
  exact ⟨hr,hp,hs,by decide,by decide⟩

end Recaman.DeficitRecordControl
