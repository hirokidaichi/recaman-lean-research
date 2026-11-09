import Recaman.DeficitRecordSourceCharge

namespace Recaman.DeficitRecordPredecessor

open Recaman.DeficitRecordSourceCharge Recaman.OtherSupplyHeightBudget
open Recaman.SourceDeficitBand Recaman.ShortSourceTriples
open Recaman.AdditionRankSlack Recaman.SingleWindowEquality

private theorem deficit_step_at_S (f : Nat → Bool) (t : Nat) (hs : f t=false) :
    deficit f (t+1)=deficit f t+1 := by
  have he : cN (EndN f 0) 0 (t+1)=cN (EndN f 0) 0 t :=
    cN_succ_neg _ 0 t (by intro h; have hh:=h.1; rw [Nat.zero_add,hs] at hh; cases hh)
  have hS : subtractions f 0 (t+1)=subtractions f 0 t+1 :=
    cN_succ_pos _ 0 t (by simpa only [Nat.zero_add] using hs)
  unfold deficit
  rw [he,hS]
  omega

/-- A local nonshort supply at a strict new deficit minimum has a
supplied predecessor that does not itself set a strict new minimum. -/
theorem local_record_supplied_predecessor (f : Nat → Bool) (n t : Nat)
    (hr : localRecord f n t) : n<t ∧ EndN f 0 (t-1) ∧ ¬localRecord f n (t-1) := by
  obtain ⟨s,hs,hst,hWin⟩:=hr.2.2.2
  obtain ⟨c,hsc,hct,hS,hHigh⟩:=
    local_nonshort_has_high_S f n s t hs hst hr.1.1 hWin hr.2.1
  have htc : t-1+1=t := by omega
  have hA : f (t-1)=true := by
    cases h : f (t-1) with
    | true => rfl
    | false =>
      have hd:=deficit_step_at_S f (t-1) h
      rw [htc] at hd
      have hEnd:=deficit_step_at_supply f t hr.1
      have hdrop:=hr.2.2.1 (t-1) (by omega) (by omega)
      omega
  have hGap : c<t-1 := by
    by_cases h : c<t-1
    · exact h
    · have he : c=t-1 := by omega
      rw [he,hA] at hS
      cases hS
  obtain ⟨hD,hFree,_⟩:=record_high_witness_exact f n c t (by omega) hct hr hHigh
  have hNo := not_of_cN_zero (P := fun x=>f x=true ∧ ¬EndN f 0 x)
    (s := c) (t-c) hFree (t-1) (by omega) (by omega)
  have hEnd : EndN f 0 (t-1) := by
    by_cases h : EndN f 0 (t-1)
    · exact h
    · exact (hNo ⟨hA,h⟩).elim
  refine ⟨by omega,hEnd,?_⟩
  intro hPrev
  have hdrop:=hPrev.2.2.1 c (by omega) (by omega)
  rw [htc,hD] at hdrop
  omega

theorem local_records_pair_into_original_supplies (f : Nat → Bool) (n K : Nat) :
    2*cN (localRecord f n) n K≤cN (EndN f 0) n K := by
  let P:=localRecord f n
  let Q:=EndN f 0
  change 2*cN P n K≤cN Q n K
  induction K using Nat.strongRecOn with
  | ind K ih =>
    cases K with
    | zero => simp [cN]
    | succ k =>
      by_cases h : P (n+k)
      · obtain ⟨hlt,he,hn⟩:=local_record_supplied_predecessor f n (n+k) h
        rw [show n+k-1=n+(k-1) by omega] at he hn
        have hp:=cN_succ_neg P n (k-1) hn
        have hq:=cN_succ_pos Q n (k-1) he
        rw [show k-1+1=k by omega] at hp hq
        have hq' : Q (n+k) := h.1
        have hb:=ih (k-1) (by omega)
        rw [cN_succ_pos P n k h,cN_succ_pos Q n k hq',hp,hq]
        omega
      · have hb:=ih k (by omega)
        have hq:=cN_add Q n k 1
        rw [cN_succ_neg P n k h]
        omega

end Recaman.DeficitRecordPredecessor
