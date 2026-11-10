import Recaman.DeficitRecordPredecessor
import Recaman.ShortRecordOverlapBudget

namespace Recaman.SupplyTrichotomyBudget

open Recaman.DeficitRecordPredecessor Recaman.DeficitRecordSourceCharge
open Recaman.ShortSourceTriples Recaman.AdditionRankSlack Recaman.SingleWindowEquality
open Classical

/-! Every internal addition of an original interval is either free (no
supporting window starts from the past), supplied by a short SAA triple, a
strict local record, or neither. The exact partition transports the E644
overlap budget to the reduced form `2L + R ≤ free + O + B + 2C`. -/

/-- A positions of the interval that carry no original support window. -/
noncomputable def freePositions (f : Nat → Bool) (n K : Nat) : Nat :=
  cN (fun t => f t = true ∧ ¬ EndN f 0 t) n K

/-- Actual supplies that are neither a short endpoint nor a strict record. -/
noncomputable def otherSupplied (f : Nat → Bool) (n K : Nat) : Nat :=
  cN (fun t => EndN f 0 t ∧ ¬ shortEndpoint f n t ∧ ¬ localRecord f n t) n K

/-- The supplied additions split exactly into short endpoints, records, and
the remaining class. -/
theorem supplied_trichotomy (f : Nat → Bool) (n K : Nat) :
    cN (EndN f 0) n K =
      cN (shortEndpoint f n) n K + cN (localRecord f n) n K +
      otherSupplied f n K := by
  have h1 := cN_split (P := EndN f 0) (Q := shortEndpoint f n) (s := n) K
  have hshort : cN (fun t => EndN f 0 t ∧ shortEndpoint f n t) n K =
      cN (shortEndpoint f n) n K := by
    exact cN_congr (P := fun t => EndN f 0 t ∧ shortEndpoint f n t)
      (Q := shortEndpoint f n) n K
      (fun i _ _ => ⟨fun hp => hp.2, fun hp => ⟨short_endpoint_supplied f n i hp, hp⟩⟩)
  have h2 := cN_split (P := fun t => EndN f 0 t ∧ ¬ shortEndpoint f n t)
    (Q := localRecord f n) (s := n) K
  have hrec : cN (fun t => (EndN f 0 t ∧ ¬ shortEndpoint f n t) ∧ localRecord f n t) n K =
      cN (localRecord f n) n K := by
    exact cN_congr (P := fun t => (EndN f 0 t ∧ ¬ shortEndpoint f n t) ∧ localRecord f n t)
      (Q := localRecord f n) n K
      (fun i _ _ => ⟨fun hp => hp.2, fun hp => ⟨⟨hp.1, hp.2.1⟩, hp⟩⟩)
  have hoth : cN (fun t => (EndN f 0 t ∧ ¬ shortEndpoint f n t) ∧ ¬ localRecord f n t) n K =
      otherSupplied f n K := by
    exact cN_congr (P := fun t => (EndN f 0 t ∧ ¬ shortEndpoint f n t) ∧ ¬ localRecord f n t)
      (Q := fun t => EndN f 0 t ∧ ¬ shortEndpoint f n t ∧ ¬ localRecord f n t) n K
      (fun i _ _ => ⟨fun hp => ⟨hp.1.1, hp.1.2, hp.2⟩, fun hp => ⟨⟨hp.1, hp.2.1⟩, hp.2.2⟩⟩)
  rw [h1, hshort, h2, hrec, hoth]
  omega

/-- The interval additions split into free positions and the three supplied
classes. -/
theorem additions_trichotomy (f : Nat → Bool) (n K : Nat) :
    additions f n K =
      freePositions f n K + cN (EndN f 0) n K := by
  show cN (fun t => f t = true) n K = freePositions f n K + cN (EndN f 0) n K
  have hsplit := cN_split (P := fun t => f t = true) (Q := EndN f 0) (s := n) K
  have hsup : cN (fun t => f t = true ∧ EndN f 0 t) n K = cN (EndN f 0) n K := by
    exact cN_congr (P := fun t => f t = true ∧ EndN f 0 t)
      (Q := EndN f 0) n K
      (fun i _ _ => ⟨fun hp => hp.2, fun he => ⟨he.1, he⟩⟩)
  have hfree : cN (fun t => f t = true ∧ ¬ EndN f 0 t) n K = freePositions f n K := rfl
  rw [hsplit, hsup, hfree]
  omega

/-- Reduced overlap budget: charging each short endpoint twice, each record
once, every unit on the left is paid by a free position, a remaining
supply, or one of the two overlap corrections. -/
theorem trichotomy_budget (f : Nat → Bool) (n K : Nat) :
    2*cN (shortEndpoint f n) n K + cN (localRecord f n) n K ≤
      freePositions f n K + otherSupplied f n K +
      cN (fun t => localRecord f n t ∧ shortEndpoint f n (t-1)) n K +
      2*cN (fun t => localRecord f n t ∧ t+1 < n+K ∧ shortEndpoint f n (t+1)) n K := by
  have hB := Recaman.ShortRecordOverlapBudget.short_record_overlap_budget f n K
  have hpart := additions_trichotomy f n K
  have htri := supplied_trichotomy f n K
  rw [hpart, htri] at hB
  omega

/-- If an interval has neither a remaining supply nor an overlap, then twice
the short endpoints plus the records are bounded by the free positions
alone. -/
theorem zero_other_zero_overlap (f : Nat → Bool) (n K : Nat)
    (hO : otherSupplied f n K = 0)
    (hB : cN (fun t => localRecord f n t ∧ shortEndpoint f n (t-1)) n K = 0)
    (hC : cN (fun t => localRecord f n t ∧ t+1 < n+K ∧ shortEndpoint f n (t+1)) n K = 0) :
    2*cN (shortEndpoint f n) n K + cN (localRecord f n) n K ≤
      freePositions f n K := by
  have h := trichotomy_budget f n K
  rw [hB, hC] at h
  omega

end Recaman.SupplyTrichotomyBudget
