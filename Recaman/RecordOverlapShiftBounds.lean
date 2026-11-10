import Recaman.DeficitRecordPredecessor
import Recaman.ShortRecordOverlapBudget

namespace Recaman.RecordOverlapShiftBounds

open Recaman.DeficitRecordPredecessor Recaman.DeficitRecordSourceCharge
open Recaman.ShortSourceTriples Recaman.AdditionRankSlack Recaman.SingleWindowEquality
open Recaman.BlockSuffixPositivity
open Classical

/-! The correction terms of the E644 overlap budget count records whose
predecessor or successor position is a short endpoint. The maps `t ↦ t-1`
and `t ↦ t+1` are injective and their images lie inside the window, so each
correction term is bounded by the short endpoint count. -/

private theorem cN_step (P : Nat → Prop) (s m : Nat) :
    cN P s (m+1) = cN P s m + (if P (s+m) then 1 else 0) := rfl

private theorem ite_le {P Q : Prop} (h : P → Q) :
    (if P then 1 else 0) ≤ (if Q then 1 else 0) := by
  rcases Classical.em P with hp | hp
  · have hq : Q := h hp
    rw [if_pos hp, if_pos hq]
    exact Nat.le_refl 1
  · rw [if_neg hp]
    exact Nat.zero_le _

/-- Shifted counting bound to the left: if each `P` position sends `t-1` to a
`Q` position, the count of `P` over `[n+1, n+1+K)` is at most the count of
`Q` over `[n, n+K)`. -/
theorem cN_shift_pred (P Q : Nat → Prop) (n K : Nat)
    (h : ∀ t, P t → Q (t-1)) :
    cN P (n+1) K ≤ cN Q n K := by
  induction K with
  | zero => exact Nat.zero_le _
  | succ m ih =>
    rw [cN_step P (n+1) m, cN_step Q n m]
    refine Nat.add_le_add ih ?_
    have hstep : (n+1+m)-1 = n+m := by omega
    rw [← hstep]
    exact ite_le (h (n+1+m))

/-- Shifted counting bound to the right: if each `P` position sends `t+1` to
a `Q` position, the count of `P` over `[n, n+K)` is at most the count of
`Q` over `[n+1, n+1+K)`. -/
theorem cN_shift_succ (P Q : Nat → Prop) (n K : Nat)
    (h : ∀ t, P t → Q (t+1)) :
    cN P n K ≤ cN Q (n+1) K := by
  induction K with
  | zero => exact Nat.zero_le _
  | succ m ih =>
    rw [cN_step P n m, cN_step Q (n+1) m]
    refine Nat.add_le_add ih ?_
    have hstep : (n+1)+m = n+m+1 := by omega
    rw [hstep]
    exact ite_le (h (n+m))

/-- A record whose predecessor position is a short endpoint: the predecessor
positions are distinct and inside the window, so the count is at most the
short endpoint count. -/
theorem records_with_preceding_short (f : Nat → Bool) (n K : Nat) :
    cN (fun t => localRecord f n t ∧ shortEndpoint f n (t-1)) n K ≤
      cN (shortEndpoint f n) n K := by
  let P := fun t => localRecord f n t ∧ shortEndpoint f n (t-1)
  have hpn : ¬ P n := by
    intro hp
    obtain ⟨hge,_,_,_,_⟩ := hp.2
    omega
  rcases Nat.eq_zero_or_pos K with hK | hK
  · subst hK
    have hl : cN P n 0 = 0 := rfl
    rw [hl]
    exact Nat.zero_le _
  · have hadd : cN P n K = cN P (n+1) (K-1) := by
      have h1 : K = 1 + (K-1) := by omega
      conv => lhs; rw [h1, cN_add P n 1 (K-1)]
      have hz : cN P n 1 = 0 := by
        rw [show (1:Nat) = 0+1 from rfl, cN_succ_neg P n 0 hpn, cN]
      rw [hz]
      omega
    have hshift := cN_shift_pred P (shortEndpoint f n) n (K-1) (fun _ hp => hp.2)
    have hle := count_prefix_le (shortEndpoint f n) n (K-1) K (by omega)
    calc
      cN P n K = cN P (n+1) (K-1) := hadd
      _ ≤ cN (shortEndpoint f n) n (K-1) := hshift
      _ ≤ cN (shortEndpoint f n) n K := hle

/-- A record whose successor position is a short endpoint: the successor
positions are distinct and inside the window, so the count is at most the
short endpoint count. -/
theorem records_with_following_short (f : Nat → Bool) (n K : Nat) :
    cN (fun t => localRecord f n t ∧ t+1 < n+K ∧ shortEndpoint f n (t+1)) n K ≤
      cN (shortEndpoint f n) n K := by
  let P := fun t => localRecord f n t ∧ t+1 < n+K ∧ shortEndpoint f n (t+1)
  rcases Nat.eq_zero_or_pos K with hK | hK
  · subst hK
    have hl : cN P n 0 = 0 := rfl
    rw [hl]
    exact Nat.zero_le _
  · have hpos : 0 < K := hK
    have hlast : ¬ P (n+(K-1)) := by
      intro hp
      omega
    have hstep0 : cN P n K = cN P n (K-1) := by
      have h1 : K = (K-1)+1 := by omega
      conv => lhs; rw [h1]
      rw [cN_succ_neg P n (K-1) hlast]
    have hshift := cN_shift_succ P (shortEndpoint f n) n (K-1)
      (fun _ hp => hp.2.2)
    have hmon : cN (shortEndpoint f n) (n+1) (K-1) ≤ cN (shortEndpoint f n) n K := by
      have h2 : K = 1 + (K-1) := by omega
      have hadd : cN (shortEndpoint f n) n K =
          cN (shortEndpoint f n) n 1 + cN (shortEndpoint f n) (n+1) (K-1) := by
        conv => lhs; rw [h2]
        rw [cN_add (shortEndpoint f n) n 1 (K-1)]
      have hle : cN (shortEndpoint f n) (n+1) (K-1) ≤
          cN (shortEndpoint f n) n 1 + cN (shortEndpoint f n) (n+1) (K-1) :=
        Nat.le_add_left _ _
      omega
    calc
      cN P n K = cN P n (K-1) := hstep0
      _ ≤ cN (shortEndpoint f n) (n+1) (K-1) := hshift
      _ ≤ cN (shortEndpoint f n) n K := hmon

/-- The two correction terms of the E644 budget are individually bounded by
the short endpoint count, hence their weighted sum is at most three times
that count. -/
theorem overlap_corrections_bounded (f : Nat → Bool) (n K : Nat) :
    cN (fun t => localRecord f n t ∧ shortEndpoint f n (t-1)) n K +
      2*cN (fun t => localRecord f n t ∧ t+1 < n+K ∧ shortEndpoint f n (t+1)) n K ≤
      3*cN (shortEndpoint f n) n K := by
  have h1 := records_with_preceding_short f n K
  have h2 := records_with_following_short f n K
  omega

/-- Sanity corollary: combining the E644 budget with the correction bounds
recovers the two-addition lower bound for strict records alone. -/
theorem records_need_two_additions (f : Nat → Bool) (n K : Nat) :
    2*cN (localRecord f n) n K ≤ additions f n K := by
  have h := Recaman.ShortRecordOverlapBudget.short_record_overlap_budget f n K
  have h1 := records_with_preceding_short f n K
  have h2 := records_with_following_short f n K
  omega

end Recaman.RecordOverlapShiftBounds
