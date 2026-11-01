import Recaman.LagSevenDonorCoverage

/-!
# TrueOldestGateT6: Gate T6 for `p ≤ 10` with the true oldest subtraction of the donor

Convention: `past e u d = [e (u-1), ..., e (u-d)]` (newest first), `true` = A, `false` = S.
A donor is an addition `u0` whose length-11 past window is one of the seven minimal SS=2 P2
words `d1, ..., d7` of `Recaman/LagSevenDonorCoverage.lean` (E-348).

## The defect being repaired (E-347)

The Gate T6 theorems for `p ≤ 10` (E-230/E-231, `TenGateT6Resolution`) delete the phase
`oldestSubtractionPhase p u0 (lag u0) = endpointPhase p u0 11`, i.e. the bit at offset 11 of the
donor window. For the four donors `d1, d2, d3, d6` that bit is an A, so the deleted phase is not
a subtraction at all and the deletion is a no-op: the conclusion degenerates to the Hall
hypothesis. The true oldest subtraction of the donor window sits at offset
`oldestOffset (past e u0 11)`, which is 10 for `d1, d2, d3, d6` and 11 for `d4, d5, d7`.

## What is proved

* `trueOldestPhase e p u0 d := endpointPhase p u0 (oldestOffset (past e u0 d))`, the phase of the
  true oldest subtraction of the length-`d` window at `u0`.
* `trueOldestPhase_eq_of_offset_eleven`: for `d4, d5, d7` it coincides with the phase deleted by
  E-230 (`oldestSubtractionPhase p u0 11`); `trueOldestPhase_eq_of_offset_ten`: for
  `d1, d2, d3, d6` it is `endpointPhase p u0 10`, and `offset_eleven_is_A_of_offset_ten` records
  that offset 11 is an A there (the E-347 no-op).
* `trueOldest_bit_is_S` / `trueOldest_is_subtraction`: on every donor the true oldest phase is a
  genuine S bit of the window and lies in `subPhases e 0 p` (periodicity, `0 < p`).
* `aas_endpoint_ne_trueOldest`: in a periodic word, the endpoint phase of a lag-3 AAS window
  never equals the true oldest phase of a donor. Congruence of the two phases transports the
  window's two A bits onto donor offsets `off - 2`, `off - 1`, and the Boolean check `aasClash`
  (decided on the seven words) shows no donor carries `A A` there.
* `p10_gate_t6_true_oldest`: for `p ≤ 10`, positive `signSum`, slack `|U| < |D|`, Hall on all
  sublists of `U`, and a donor `u0 ∈ U` (`past e u0 11 ∈ donors`, `lag u0 = 11`), deleting
  `trueOldestPhase e p u0 11` preserves Hall on every sublist of `U`. The case split is the one
  of E-230: sublists containing `u0` survive by slack compensation (`p ≤ 11`), tight sublists
  avoiding `u0` consist of lag-3 AAS windows (E-230's `tight_avoiding_all_lag_three_p10`) whose
  endpoints avoid the true oldest phase by the new disjointness lemma, and slack sublists survive
  trivially. `p10_gate_t6_true_oldest_lag` restates it with `trueOldestPhase e p u0 (lag u0)`.
* `p10_gate_t6_true_oldest_of_minimal`: the same with the donor given semantically (P2 at lag 11,
  no proper P2 prefix, `ssCount = 2`) via `minimal_ss2_eleven_mem_donors`.

## What is not proved

Nothing here concerns `p > 10`: the lag-3 rigidity of tight avoiding sublists is imported from
E-230 and is specific to `p ≤ 10` (`|D| ≤ 4`). Tight avoiding sublists with lag-7 members, donors
of lag 15 or more, donors with `ssCount ≥ 3`, and the capacity inequality E-070 are untouched.
No orbit hypothesis is used; `e` is an arbitrary periodic sign word.
-/

namespace Recaman.TrueOldestGateT6

open Recaman.LeadingRunSupply (past P2 past_p2_iff)
open Recaman.OneSSMultiplicity (ssCount)
open Recaman.LowSSPeriodicSupply (endpointPhase)
open Recaman.TwoSSLocalDonation (oldestSubtractionPhase oldest_is_subtraction)
open Recaman.TwoSSTightDisjoint (neighborhood deletedNeighborhood)
open Recaman.SharpPeriodicSupply (phase_eq_mod lift_equal_mod)
open Recaman.TwoSSLeadingSibling (past_length)
open Recaman.LagSevenDonorCoverage (d1 d2 d3 d4 d5 d6 d7 donors mem_donors_iff oldestOffset
  oldestOffset_donors oldestOffset_is_oldest_S past_getD minimal_ss2_eleven_mem_donors)

/-- The phase of the true oldest subtraction of the length-`d` window at `u0`: the endpoint
phase at offset `oldestOffset (past e u0 d)` instead of the fixed offset `d`. -/
def trueOldestPhase (e : Int → Bool) (p : Nat) (u0 : Nat) (d : Nat) : Nat :=
  endpointPhase p (u0 : Int) (oldestOffset (past e (u0 : Int) d))

/-- On a donor window the oldest offset is 10 (`d1, d2, d3, d6`) or 11 (`d4, d5, d7`). -/
theorem donor_oldestOffset (e : Int → Bool) (u0 : Int) (hdon : past e u0 11 ∈ donors) :
    ((past e u0 11 = d1 ∨ past e u0 11 = d2 ∨ past e u0 11 = d3 ∨ past e u0 11 = d6) ∧
        oldestOffset (past e u0 11) = 10) ∨
      ((past e u0 11 = d4 ∨ past e u0 11 = d5 ∨ past e u0 11 = d7) ∧
        oldestOffset (past e u0 11) = 11) := by
  rw [mem_donors_iff] at hdon
  rcases hdon with h | h | h | h | h | h | h <;> rw [h] <;> decide

/-- For `d4, d5, d7` the true oldest phase is the phase deleted by E-230. -/
theorem trueOldestPhase_eq_of_offset_eleven (e : Int → Bool) (p : Nat) (u0 : Nat)
    (hdon : past e (u0 : Int) 11 = d4 ∨ past e (u0 : Int) 11 = d5 ∨ past e (u0 : Int) 11 = d7) :
    trueOldestPhase e p u0 11 = oldestSubtractionPhase p u0 11 := by
  unfold trueOldestPhase oldestSubtractionPhase
  have hoff : oldestOffset (past e (u0 : Int) 11) = 11 := by
    rcases hdon with h | h | h <;> rw [h] <;> decide
  rw [hoff]

/-- For `d1, d2, d3, d6` the true oldest phase is the endpoint phase at offset 10. -/
theorem trueOldestPhase_eq_of_offset_ten (e : Int → Bool) (p : Nat) (u0 : Nat)
    (hdon : past e (u0 : Int) 11 = d1 ∨ past e (u0 : Int) 11 = d2 ∨
      past e (u0 : Int) 11 = d3 ∨ past e (u0 : Int) 11 = d6) :
    trueOldestPhase e p u0 11 = endpointPhase p (u0 : Int) 10 := by
  unfold trueOldestPhase
  have hoff : oldestOffset (past e (u0 : Int) 11) = 10 := by
    rcases hdon with h | h | h | h <;> rw [h] <;> decide
  rw [hoff]

/-- The E-347 defect in Lean: for `d1, d2, d3, d6` the bit at offset 11 is an A, so the phase
deleted by E-230 (`endpointPhase p u0 11`) is not a subtraction of the donor window. -/
theorem offset_eleven_is_A_of_offset_ten (e : Int → Bool) (u0 : Int)
    (hdon : past e u0 11 = d1 ∨ past e u0 11 = d2 ∨ past e u0 11 = d3 ∨ past e u0 11 = d6) :
    e (u0 - 11) = true := by
  have hbit : (past e u0 11).getD 10 true = true := by
    rcases hdon with h | h | h | h <;> rw [h] <;> decide
  rw [past_getD e u0 11 10 (by omega) true] at hbit
  have hx : u0 - 11 = u0 - 1 - ((10 : Nat) : Int) := by omega
  rw [hx]
  exact hbit

/-- On a donor window, the bit at the oldest offset is an S. -/
theorem trueOldest_bit_is_S (e : Int → Bool) (u0 : Int) (hdon : past e u0 11 ∈ donors) :
    e (u0 - (oldestOffset (past e u0 11) : Int)) = false := by
  have hS := (oldestOffset_is_oldest_S _ hdon).1
  have hbounds : 1 ≤ oldestOffset (past e u0 11) ∧ oldestOffset (past e u0 11) ≤ 11 := by
    rcases donor_oldestOffset e u0 hdon with ⟨_, hoff⟩ | ⟨_, hoff⟩ <;> omega
  rw [past_getD e u0 11 (oldestOffset (past e u0 11) - 1) (by omega) true] at hS
  have hx : u0 - (oldestOffset (past e u0 11) : Int) =
      u0 - 1 - ((oldestOffset (past e u0 11) - 1 : Nat) : Int) := by omega
  rw [hx]
  exact hS

/-- The true oldest phase of a donor is a subtraction phase of the periodic word. -/
theorem trueOldest_is_subtraction (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x) (u0 : Nat)
    (hdon : past e (u0 : Int) 11 ∈ donors) :
    trueOldestPhase e p u0 11 ∈ LagElevenPeriodic.subPhases e 0 p :=
  oldest_is_subtraction e p hp hper u0 (oldestOffset (past e (u0 : Int) 11))
    (trueOldest_bit_is_S e (u0 : Int) hdon)

/-- Boolean check on a word `w` with oldest offset `off`: are the bits at 0-based indices
`off - 3` and `off - 2` (offsets `off - 2`, `off - 1`) both A? A lag-3 AAS window whose endpoint
phase equals the phase of offset `off` places its two A bits exactly there. -/
def aasClash (w : List Bool) : Bool :=
  w.getD (oldestOffset w - 3) true && w.getD (oldestOffset w - 2) true

/-- No donor carries `A A` just above its oldest subtraction. -/
theorem aasClash_donors : ∀ w ∈ donors, aasClash w = false := by
  decide

/-- In a periodic word the endpoint phase of a lag-3 AAS window at `u` is never the true oldest
phase of a donor at `u0`: equality of phases lifts to `u - 3 = u0 - off + k p`, periodicity moves
the A bits `e (u-1)`, `e (u-2)` to donor offsets `off - 2`, `off - 1`, and `aasClash_donors`
rejects every donor. -/
theorem aas_endpoint_ne_trueOldest (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x) (u0 u : Nat)
    (hdon : past e (u0 : Int) 11 ∈ donors)
    (_huA : e (u : Int) = true)
    (haas : e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false) :
    endpointPhase p (u : Int) 3 ≠ trueOldestPhase e p u0 11 := by
  intro heq
  have hbounds : 10 ≤ oldestOffset (past e (u0 : Int) 11) ∧
      oldestOffset (past e (u0 : Int) 11) ≤ 11 := by
    rcases donor_oldestOffset e (u0 : Int) hdon with ⟨_, hoff⟩ | ⟨_, hoff⟩ <;> omega
  have hfalse := aasClash_donors _ hdon
  unfold aasClash at hfalse
  unfold trueOldestPhase endpointPhase at heq
  have hmod := phase_eq_mod p hp _ _ heq
  obtain ⟨k, hk⟩ := lift_equal_mod p _ _ hmod
  obtain ⟨off, hoff⟩ : ∃ off, oldestOffset (past e (u0 : Int) 11) = off := ⟨_, rfl⟩
  rw [hoff] at hbounds hfalse hk
  have h1 : e ((u0 : Int) - 1 - ((off - 3 : Nat) : Int)) = true := by
    have hx : (u : Int) - 1 = ((u0 : Int) - 1 - ((off - 3 : Nat) : Int)) + k * (p : Int) := by
      omega
    have hb := haas.1
    rw [hx, LagElevenPeriodic.e_shift e p hper] at hb
    exact hb
  have h2 : e ((u0 : Int) - 1 - ((off - 2 : Nat) : Int)) = true := by
    have hx : (u : Int) - 2 = ((u0 : Int) - 1 - ((off - 2 : Nat) : Int)) + k * (p : Int) := by
      omega
    have hb := haas.2.1
    rw [hx, LagElevenPeriodic.e_shift e p hper] at hb
    exact hb
  rw [past_getD e (u0 : Int) 11 (off - 3) (by omega) true,
    past_getD e (u0 : Int) 11 (off - 2) (by omega) true, h1, h2] at hfalse
  exact absurd hfalse (by decide)

/-- Gate T6 for `p ≤ 10` with the true oldest subtraction: deleting `trueOldestPhase e p u0 11`
of a donor `u0` preserves Hall's condition on every sublist of `U`. Hypotheses are those of
E-230's `p10_universal_gate_t6_deletability_unconditional` plus the donor membership and
`lag u0 = 11`. -/
theorem p10_gate_t6_true_oldest (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hp10 : p ≤ 10) (hpos : 0 < ShortPeriodicSupply.signSum e 0 p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U : List Nat) (lag : Nat → Nat)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (u0 : Nat) (hu0 : u0 ∈ U)
    (_hd_lt : lag u0 < 15)
    (_hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (hhall_orig : ∀ A : List Nat, List.Sublist A U → A.length ≤ (neighborhood e p A lag).length)
    (hU_pos : ∀ u ∈ U, 0 < lag u)
    (hU_P2 : ∀ u ∈ U, ShortPeriodicSupply.P2 e (u : Int) (lag u))
    (hU_A : ∀ u ∈ U, e (u : Int) = true)
    (hdon : past e (u0 : Int) 11 ∈ donors)
    (_hlag11 : lag u0 = 11) :
    ∀ A : List Nat, List.Sublist A U →
      A.length ≤ (deletedNeighborhood e p A lag (trueOldestPhase e p u0 11)).length := by
  intro A hsub
  by_cases hmem : u0 ∈ A
  · have hP2_past : P2 (past e (u0 : Int) (lag u0)) :=
      (past_p2_iff e (u0 : Int) (lag u0)).mpr hP0
    exact CapacitySlackCompensation.high_ss_containing_subsets_survive_deletion_p11 e p hp
      (by omega) hper U A lag hsub.length_le hslack u0 hmem hP2_past (by omega) _
  · by_cases htight : (neighborhood e p A lag).length = A.length
    · have hlag3 := TenGateT6Resolution.tight_avoiding_all_lag_three_p10 e p hp hp10 hpos hper
        U A lag u0 hu0 hmem hsub hslack htight hU_P2 hU_pos
      have haas := TenGateT6Resolution.tight_avoiding_all_aas_p10 e p hp hp10 hpos hper
        U A lag u0 hu0 hmem hsub hslack htight hU_P2 hU_pos
      have hdisj : ∀ u ∈ A, trueOldestPhase e p u0 11 ≠ endpointPhase p (u : Int) 3 := by
        intro u hu
        exact (aas_endpoint_ne_trueOldest e p hp hper u0 u hdon (hU_A u (hsub.subset hu))
          (haas u hu)).symm
      have hnot := TwoSSSmallCapacityClosure.tight_avoids_of_all_lag_three e p hp A lag hlag3
        haas _ hdisj
      exact TwoSSAvoidTight.deleted_hall_of_not_mem e p A lag _ hnot (hhall_orig A hsub)
    · have hhallA := hhall_orig A hsub
      exact TwoSSAvoidTight.deleted_hall_of_slack e p A lag _ (by omega)

/-- The same statement with the deleted phase written through the donor's own lag. -/
theorem p10_gate_t6_true_oldest_lag (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hp10 : p ≤ 10) (hpos : 0 < ShortPeriodicSupply.signSum e 0 p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U : List Nat) (lag : Nat → Nat)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (u0 : Nat) (hu0 : u0 ∈ U)
    (hd_lt : lag u0 < 15)
    (hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (hhall_orig : ∀ A : List Nat, List.Sublist A U → A.length ≤ (neighborhood e p A lag).length)
    (hU_pos : ∀ u ∈ U, 0 < lag u)
    (hU_P2 : ∀ u ∈ U, ShortPeriodicSupply.P2 e (u : Int) (lag u))
    (hU_A : ∀ u ∈ U, e (u : Int) = true)
    (hdon : past e (u0 : Int) 11 ∈ donors)
    (hlag11 : lag u0 = 11) :
    ∀ A : List Nat, List.Sublist A U →
      A.length ≤ (deletedNeighborhood e p A lag (trueOldestPhase e p u0 (lag u0))).length := by
  rw [hlag11]
  exact p10_gate_t6_true_oldest e p hp hp10 hpos hper U lag hslack u0 hu0 hd_lt hu0A hP0 hss0
    hhall_orig hU_pos hU_P2 hU_A hdon hlag11

/-- Gate T6 for `p ≤ 10` with the donor given semantically: `u0` has a P2 window of lag 11 with
no proper P2 prefix and `ssCount = 2`. -/
theorem p10_gate_t6_true_oldest_of_minimal (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hp10 : p ≤ 10) (hpos : 0 < ShortPeriodicSupply.signSum e 0 p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U : List Nat) (lag : Nat → Nat)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (u0 : Nat) (hu0 : u0 ∈ U)
    (hd_lt : lag u0 < 15)
    (hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (hhall_orig : ∀ A : List Nat, List.Sublist A U → A.length ≤ (neighborhood e p A lag).length)
    (hU_pos : ∀ u ∈ U, 0 < lag u)
    (hU_P2 : ∀ u ∈ U, ShortPeriodicSupply.P2 e (u : Int) (lag u))
    (hU_A : ∀ u ∈ U, e (u : Int) = true)
    (hlag11 : lag u0 = 11)
    (hmin : ∀ d, d < 11 → 0 < d → ¬ P2 ((past e (u0 : Int) 11).take d)) :
    ∀ A : List Nat, List.Sublist A U →
      A.length ≤ (deletedNeighborhood e p A lag (trueOldestPhase e p u0 11)).length := by
  have hP11 := hP0
  rw [hlag11] at hP11
  have hss11 := hss0
  rw [hlag11] at hss11
  have hdon : past e (u0 : Int) 11 ∈ donors :=
    minimal_ss2_eleven_mem_donors (past e (u0 : Int) 11) (past_length e (u0 : Int) 11)
      ((past_p2_iff e (u0 : Int) 11).mpr hP11) (by rw [past_length]; exact hmin) hss11
  exact p10_gate_t6_true_oldest e p hp hp10 hpos hper U lag hslack u0 hu0 hd_lt hu0A hP0 hss0
    hhall_orig hU_pos hU_P2 hU_A hdon hlag11

end Recaman.TrueOldestGateT6
