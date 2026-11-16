import Recaman.Basic
import Recaman.ShortPeriodicSupply
import Recaman.LagElevenPeriodic

/-!
# Pinned statements of the protected central claims (G6)

Human-owned, like `docs/PROTECTED_CLAIMS.tsv`: changes need `RECAMAN_HUMAN_APPROVED=1`.
Each `def` is the intended Lean statement of a central claim, written only with
library definitions. A registry row may carry the label `PROVED-LEAN` for a pinned
claim only if one of its audit symbols proves the pinned `Prop` (checked by
`scripts/harness_lean.py --check-pins`: unfold the pin, `intro` its binders,
`apply` the theorem and close every remaining goal by `assumption`, so stronger
theorems pass and extra hypotheses do not). The definitions these pins mention
are frozen by hash in `definitions.lock`.

Vocabulary is the one used by the proved partial results, so those results prove
restricted versions of the pins (regression fixtures in
`scripts/lean/PinFixtures.lean`):
* E-067 is `ShortPeriodicSupply.exists_phase_without_short_supply` (E-071) without
  the lag bound `d ≤ 7`;
* E-070 is `LowSSPeriodicSupply.periodic_lowSS_capacity` (E-128) without
  `ssCount (past e u d) ≤ 1`, with the positive period sum of E-067 added.

E-179 (Gate T6, COMPUTED) is not pinned; see `PINS.tsv`.
-/

namespace RecamanProtected

open Recaman

/-- E-001: the standard Recamán sequence takes every natural number. -/
def E001 : Prop :=
  ∀ m : Nat, ∃ t : Nat, a t = m

/-- E-067: every periodic sign word with positive period sum has an addition
phase with no P2 supplier at any lag. -/
def E067 : Prop :=
  ∀ (e : Int → Bool) (p : Nat), (∀ x : Int, e (x + p) = e x) → ∀ t : Int,
    0 < ShortPeriodicSupply.signSum e t p →
    ∃ i : Nat, i < p ∧ e (t + i) = true ∧
      ¬ ∃ d : Nat, 1 ≤ d ∧ ShortPeriodicSupply.P2 e (t + i) d

/-- E-070: in a periodic sign word with positive period sum, the addition phases
with a P2 supplier at any lag are at most the subtraction phases (|U| ≤ |D|). -/
def E070 : Prop :=
  ∀ (e : Int → Bool) (p : Nat), 0 < p → (∀ x : Int, e (x + p) = e x) →
    0 < ShortPeriodicSupply.signSum e 0 p →
    ∀ U : List Nat, U.Nodup → (∀ u, u ∈ U → u < p) →
    (∀ u, u ∈ U → e u = true ∧ ∃ d : Nat, ShortPeriodicSupply.P2 e u d) →
    U.length ≤ (LagElevenPeriodic.subPhases e 0 p).length

end RecamanProtected
