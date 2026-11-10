import Recaman.RecordOverlapShiftBounds

namespace Recaman.ShortRecordJointCorrection

open Recaman.RecordOverlapShiftBounds Recaman.DeficitRecordSourceCharge
open Recaman.OtherSupplyHeightBudget Recaman.ShortSourceTriples
open Recaman.SingleWindowEquality Recaman.BlockSuffixPositivity

/-- A short endpoint cannot have strict local deficit records on both sides.
A high subtraction for the later record would have to lie between the records,
where the short endpoint is an addition. -/
theorem short_endpoint_excludes_two_records (f : Nat → Bool) (n t : Nat)
    (hs : shortEndpoint f n t) (hl : localRecord f n (t-1))
    (hr : localRecord f n (t+1)) : False := by
  have hLater := hr
  obtain ⟨he, hshort, _, s, hns, hst, hwin⟩ := hr
  obtain ⟨c, hsc, hct, hcS, hhigh⟩ :=
    local_nonshort_has_high_S f n s (t+1) hns hst he.1 hwin hshort
  have hnt := hs.1
  have hlt := record_witness_after_earlier f n (t-1) (t+1) c
    (by omega) (by omega) (by omega) hct hl hLater hhigh
  have hEq : c = t := by omega
  rw [hEq, hs.2.2.2.2] at hcS
  cases hcS

/-- The two correction types use disjoint short endpoints in the original
interval. This bounds their sum, including both interval boundaries. -/
theorem joint_corrections_le_short (f : Nat → Bool) (n K : Nat) :
    cN (fun t => localRecord f n t ∧ shortEndpoint f n (t-1)) n K +
      cN (fun t => localRecord f n t ∧ t+1 < n+K ∧ shortEndpoint f n (t+1)) n K ≤
      cN (shortEndpoint f n) n K := by
  let B := fun t => localRecord f n t ∧ shortEndpoint f n (t-1)
  let C := fun t => localRecord f n t ∧ t+1 < n+K ∧ shortEndpoint f n (t+1)
  let P := fun t => shortEndpoint f n t ∧ localRecord f n (t+1)
  let Q := fun t => shortEndpoint f n t ∧ localRecord f n (t-1)
  change cN B n K + cN C n K ≤ _
  cases K with
  | zero => simp [cN]
  | succ k =>
    have hnB : ¬ B n := by
      intro h
      have hh := h.2.1
      omega
    have hb0 : cN B n 1 = 0 := cN_succ_neg B n 0 (by simpa only [Nat.add_zero] using hnB)
    have hbSplit := cN_add B n 1 k
    rw [Nat.add_comm 1 k, hb0, Nat.zero_add] at hbSplit
    have hbShift := cN_shift_pred B P n k (fun t h => by
      have ht := h.2.1
      exact ⟨h.2, by rw [show t-1+1=t by omega]; exact h.1⟩)
    have hb := count_prefix_le P n k (k+1) (by omega)
    have hlast : ¬ C (n+k) := by
      intro h
      have hh := h.2.1
      omega
    have hc0 := cN_succ_neg C n k hlast
    have hcShift := cN_shift_succ C Q n k (fun t h => ⟨h.2.2, by
      rw [Nat.add_sub_cancel]
      exact h.1⟩)
    have hcSplit := cN_add Q n 1 k
    rw [Nat.add_comm 1 k] at hcSplit
    have hpart := cN_split (shortEndpoint f n) (fun t => localRecord f n (t+1)) n (k+1)
    have hq := cN_mono Q (fun t => shortEndpoint f n t ∧ ¬localRecord f n (t+1)) n (k+1)
      (fun t _ _ h => ⟨h.1, fun hr => short_endpoint_excludes_two_records f n t h.1 h.2 hr⟩)
    change cN (shortEndpoint f n) n (k+1) = cN P n (k+1) + _ at hpart
    omega

end Recaman.ShortRecordJointCorrection
