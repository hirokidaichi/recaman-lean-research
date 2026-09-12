import Recaman.TwoSSTightDisjoint
import Recaman.TwoSSLocalDonation

/-!
# TightAvoidingLagCertificate

`TenGateT6Resolution.tight_avoiding_all_lag_three_p10` forces every member of a tight
avoiding subset to lag 3, under the hypothesis `p ≤ 10`. The hypothesis is not an artefact
of the proof: this module certifies that the conclusion itself is false once the period is
large enough, so no extension of that statement to general `p` can exist.

The witness is the period 18 word `AAAASSAAAASAAASASS`, with

* `A = [2, 8, 11, 13]` and the lag assignment `11 ↦ 7`, everything else `↦ 3`;
* `N(A) = [4, 5, 10, 17]`, so `|N(A)| = 4 = |A|` and `A` is **tight**;
* the donor `u₀ = 7` carrying an S-ended `ssCount = 2` window of lag `11 < 15`, with
  `u₀ ∉ A`, so `A` is **avoiding**;
* `U = A ∪ {u₀}` of size 5 against `|D| = 6`, so the word has **positive slack**;
* yet phase `11` carries lag `7 ≠ 3`.

The same certificate also records that Gate T6's own conclusion survives here: the donated
subtraction `s*(u₀) = 14` is *not* covered by `N(A)`, so Hall's condition is preserved.
The lag 3 forcing dies at `p = 18` while deletability does not, which is why a replacement
theorem has to quantify over `lag ∈ {3, 7}` rather than over `lag = 3`.

Exhaustive search over all periodic words, all P2 lag assignments and all tight avoiding
subsets (probe `experiments/issue73_20260912/tight_avoiding_growth`) puts the first failure
exactly at `p = 18`: lag 3 forcing holds for every `p ≤ 17`.
-/

namespace Recaman.TightAvoidingLagCertificate

open TwoSSTightDisjoint TwoSSLocalDonation LeadingRunSupply OneSSMultiplicity
open ShortPeriodicSupply LowSSPeriodicSupply

/-- The period 18 sign word `AAAASSAAAASAAASASS` (`true` = addition). -/
def w18 : List Bool :=
  [true, true, true, true, false, false, true, true, true, true,
   false, true, true, true, false, true, false, false]

/-- The periodic extension of `w18` to all of `Int`. -/
def e18 : Int → Bool := fun x => w18.getD ((x % 18).toNat) false

/-- Phase 11 carries the lag 7 window; every other member of `A` carries lag 3. -/
def lag18 : Nat → Nat := fun u => if u = 11 then 7 else 3

/-- The tight avoiding subset. -/
def A18 : List Nat := [2, 8, 11, 13]

/-- The supply list: `A18` together with the donor `u₀ = 7`. -/
def U18 : List Nat := [2, 7, 8, 11, 13]

theorem e18_periodic (x : Int) : e18 (x + 18) = e18 x := by
  unfold e18
  congr 1
  omega

/-- Every member of `A18` really carries a P2 window at its assigned lag. -/
theorem A18_windows : ∀ u ∈ A18, ShortPeriodicSupply.P2 e18 (u : Int) (lag18 u) := by
  unfold A18 lag18 ShortPeriodicSupply.P2 e18 w18
  decide

/-- `A18` is tight: its subtraction neighborhood has exactly `|A18|` elements. -/
theorem A18_tight : (neighborhood e18 18 A18 lag18).length = A18.length := by
  unfold neighborhood A18 lag18 e18 w18 isCoveredBySubset isCoveredByWindow
    LagElevenPeriodic.subPhases
  decide

/-- The donor window at phase 7 is S-ended with `ssCount = 2` and lag `11 < 15`. -/
theorem donor_valid :
    ShortPeriodicSupply.P2 e18 7 11 ∧ ssCount (past e18 7 11) = 2 ∧ 11 < 15 ∧ e18 (7 - 11) = false := by
  unfold ShortPeriodicSupply.P2 past ssCount e18 w18
  decide

/-- The donor is avoided by `A18`, and `U18` has positive slack against `D`. -/
theorem avoiding_and_slack :
    (7 : Nat) ∉ A18 ∧ U18.length < (LagElevenPeriodic.subPhases e18 0 18).length := by
  unfold A18 U18 LagElevenPeriodic.subPhases e18 w18
  decide

/-- Gate T6's conclusion survives at this witness: the donated subtraction is uncovered. -/
theorem donated_subtraction_uncovered :
    oldestSubtractionPhase 18 7 11 = 14 ∧
    oldestSubtractionPhase 18 7 11 ∉ neighborhood e18 18 A18 lag18 := by
  unfold oldestSubtractionPhase endpointPhase SharpPeriodicSupply.phase
    neighborhood A18 lag18 e18 w18 isCoveredBySubset isCoveredByWindow
    LagElevenPeriodic.subPhases
  decide

/-- Some member of the tight avoiding subset carries a lag other than 3. -/
theorem lag_not_forced_to_three : ∃ u ∈ A18, lag18 u ≠ 3 := by
  unfold A18 lag18
  decide

/-- **Lag 3 forcing fails at period 18.**

Every hypothesis of `tight_avoiding_all_lag_three_p10` except `p ≤ 10` is met — positive
sign sum, periodicity, a tight avoiding subset, positive slack, P2 windows at every
assigned lag — and the conclusion `∀ u ∈ A, lag u = 3` is false. So that theorem admits no
extension to general `p`, and the period restriction in E-230/E-231 is necessary rather
than an artefact. -/
theorem lag_three_forcing_fails_at_period_18 :
    (∀ x : Int, e18 (x + 18) = e18 x) ∧
    0 < signSum e18 0 18 ∧
    (∀ u ∈ A18, ShortPeriodicSupply.P2 e18 (u : Int) (lag18 u)) ∧
    (neighborhood e18 18 A18 lag18).length = A18.length ∧
    U18.length < (LagElevenPeriodic.subPhases e18 0 18).length ∧
    (7 : Nat) ∈ U18 ∧ (7 : Nat) ∉ A18 ∧ List.Sublist A18 U18 ∧
    ShortPeriodicSupply.P2 e18 7 11 ∧ ssCount (past e18 7 11) = 2 ∧ e18 (7 - 11) = false ∧
    ¬ (∀ u ∈ A18, lag18 u = 3) := by
  refine ⟨e18_periodic, ?_, A18_windows, A18_tight, avoiding_and_slack.2, ?_, ?_, ?_,
    donor_valid.1, donor_valid.2.1, donor_valid.2.2.2, ?_⟩
  · unfold signSum e18 w18; decide
  · unfold U18; decide
  · exact avoiding_and_slack.1
  · unfold A18 U18; decide
  · intro h
    obtain ⟨u, hu, hne⟩ := lag_not_forced_to_three
    exact hne (h u hu)

end Recaman.TightAvoidingLagCertificate
