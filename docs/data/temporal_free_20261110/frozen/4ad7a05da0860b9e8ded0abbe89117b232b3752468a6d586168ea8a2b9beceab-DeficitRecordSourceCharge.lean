import Recaman.OtherSupplyHeightBudget
import Recaman.SourceDeficitBand

namespace Recaman.DeficitRecordSourceCharge

open Recaman.OtherSupplyHeightBudget Recaman.SourceDeficitBand Recaman.ShortSourceTriples
open Recaman.AdditionRankSlack Recaman.SingleWindowEquality

/-- A local nonshort supply that creates a strict new deficit minimum
within the chosen interval. -/
def localRecord (f : Nat → Bool) (n t : Nat) : Prop :=
  EndN f 0 t ∧ ¬shortEndpoint f n t ∧
  (∀ q, n≤q → q≤t → deficit f (t+1)<deficit f q) ∧
  ∃ s, n≤s ∧ s≤t ∧ Win f s (t-s)

def recordSubtraction (f : Nat → Bool) (n c : Nat) : Prop :=
  f c=false ∧ ∃ t s, c<t ∧ localRecord f n t ∧
    n≤s ∧ s≤c ∧ Win f s (t-s) ∧ Fw f t≤Fw f c

theorem deficit_step_at_supply (f : Nat → Bool) (t : Nat) (h : EndN f 0 t) :
    deficit f (t+1)=deficit f t-1 := by
  have he : cN (EndN f 0) 0 (t+1)=cN (EndN f 0) 0 t+1 :=
    cN_succ_pos _ 0 t (by simpa only [Nat.zero_add] using h)
  have hs : subtractions f 0 (t+1)=subtractions f 0 t :=
    cN_succ_neg _ 0 t (by simp [h.1])
  unfold deficit
  rw [he,hs]
  omega

theorem high_S_deficit_le (f : Nat → Bool) (c t : Nat)
    (hct : c≤t) (hHigh : Fw f t≤Fw f c) : deficit f c≤deficit f t := by
  have hc:=walk_eq_free_sub_deficit f c
  have ht:=walk_eq_free_sub_deficit f t
  have hm:=free_prefix_mono f 0 c t hct
  omega

/-- A high witness of the later record cannot precede any earlier
record of the same original deficit, even with intermediate free A. -/
theorem record_witness_after_earlier (f : Nat → Bool) (n a b c : Nat)
    (hna : n≤a) (hnc : n≤c) (hab : a<b) (hcb : c<b)
    (ha : localRecord f n a) (hb : localRecord f n b)
    (hHigh : Fw f b≤Fw f c) : a<c := by
  have hda:=deficit_step_at_supply f a ha.1
  have hdb:=deficit_step_at_supply f b hb.1
  have hDrop:=hb.2.2.1 (a+1) (by omega) (by omega)
  have hLe:=high_S_deficit_le f c b (by omega) hHigh
  by_cases h : a<c
  · exact h
  · have hFloor:=ha.2.2.1 c hnc (by omega)
    omega

/-- Distinct local nonshort records can charge distinct original high
subtractions. Neither all suppliers nor all deficit drops are asserted
to have this record property. -/
theorem original_record_high_subtraction_count (f : Nat → Bool) (n K : Nat) :
    cN (localRecord f n) n K≤cN (recordSubtraction f n) n K := by
  let P:=localRecord f n
  let Q:=recordSubtraction f n
  change cN P n K≤cN Q n K
  induction K using Nat.strongRecOn with
  | ind K ih =>
    cases K with
    | zero => simp [cN]
    | succ k =>
      by_cases hb : P (n+k)
      · have hBase:=hb
        obtain ⟨hE,hShort,hRec,s,hs,hst,hWin⟩:=hb
        obtain ⟨c,hsc,hcb,hS,hHigh⟩:=
          local_nonshort_has_high_S f n s (n+k) hs hst hE.1 hWin hShort
        let d:=c-n
        have hdc : n+d=c := by dsimp [d]; omega
        have hd : d<k := by omega
        have hQc : Q c := ⟨hS,n+k,s,hcb,hBase,hs,hsc,hWin,hHigh⟩
        have hz : cN P c (n+k-c)=0 := by
          apply cN_zero_of
          intro a hca hab ha
          have hlt:=record_witness_after_earlier f n a (n+k) c
            (by omega) (by omega) (by omega) hcb ha hBase hHigh
          omega
        have hp:=cN_add P n d (n+k-c)
        rw [show d+(n+k-c)=k by omega,hdc,hz,Nat.add_zero] at hp
        have hq:=cN_succ_pos Q n d (by rwa [hdc])
        have hMono:=cN_add Q n (d+1) (k+1-(d+1))
        rw [show d+1+(k+1-(d+1))=k+1 by omega] at hMono
        have hprev:=ih d (by omega)
        rw [cN_succ_pos P n k hBase,hp]
        omega
      · have hprev:=ih k (by omega)
        have hq:=cN_add Q n k 1
        rw [cN_succ_neg P n k hb]
        omega

end Recaman.DeficitRecordSourceCharge
