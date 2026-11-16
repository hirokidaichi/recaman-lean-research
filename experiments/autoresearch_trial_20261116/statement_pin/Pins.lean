import Recaman.LineCapacityPeriodic
import Recaman.CleanWindowCapacity

/-!
# Pinned statements (trial of the Comparator / SafeVerify mechanism, 2026-11-16)

A pinned statement is written once by a human from the prose claim, using only
library *definitions*.  A registry row may cite a theorem for a pinned claim only
if `check_pins.py` shows the theorem proves the pinned `Prop`:

* `exact`   : the theorem's type is definitionally the pinned `Prop` (Comparator mode);
* `implies` : `intro`s the pinned binders, `apply`s the theorem and closes every
  remaining hypothesis by `assumption` (accepts stronger theorems, rejects any
  extra hypothesis such as an unproved `LineCapacity e`).

This file is outside the `Recaman` library and is not imported by it.
-/

namespace RecamanPins

open Recaman.LeadingRunSupply
open Recaman.LineCapacityPeriodic
open Recaman.SuffixHallOwnerMap (clocks)
open Recaman.CleanWindowCapacity (Clean)

/-- E-070 (CONJECTURED, protected): on a periodic sign word with positive
period sum, the additions with a P2 supplier at any lag are at most the
subtractions in one period. -/
def E070 : Prop :=
  ∀ (e : Int → Bool) (p : Nat), 0 < p → (∀ x : Int, e (x + p) = e x) →
    0 < ((List.range p).map (fun i : Nat => if e (i : Int) then (1 : Int) else -1)).sum →
    ∀ t : Int, suppliedPhases e t p ≤ subtractionPhases e t p

/-- E-511 (PROVED-LEAN): clean windows give the interval capacity bound. -/
def E511 : Prop :=
  ∀ (e : Int → Bool) (q : Int) (n : Nat) (B : List Int), B.Nodup → ∀ (lag : Int → Nat),
    (∀ b ∈ B, q ≤ b - (lag b : Int) ∧ b < q + (n : Int) ∧ e b = true ∧
      P2 (past e b (lag b)) ∧ Clean e b (lag b)) →
    B.length ≤ ((clocks q n).filter (fun c => e c = false)).length

/-! ## Mutants used to test the checker (none of these is a research claim) -/

/-- Mutant 1 of E-511: the `Nodup` hypothesis is dropped (a stronger claim). -/
def E511_dropNodup : Prop :=
  ∀ (e : Int → Bool) (q : Int) (n : Nat) (B : List Int), ∀ (lag : Int → Nat),
    (∀ b ∈ B, q ≤ b - (lag b : Int) ∧ b < q + (n : Int) ∧ e b = true ∧
      P2 (past e b (lag b)) ∧ Clean e b (lag b)) →
    B.length ≤ ((clocks q n).filter (fun c => e c = false)).length

/-- Mutant 2 of E-511: `≤` strengthened to `<`. -/
def E511_strict : Prop :=
  ∀ (e : Int → Bool) (q : Int) (n : Nat) (B : List Int), B.Nodup → ∀ (lag : Int → Nat),
    (∀ b ∈ B, q ≤ b - (lag b : Int) ∧ b < q + (n : Int) ∧ e b = true ∧
      P2 (past e b (lag b)) ∧ Clean e b (lag b)) →
    B.length < ((clocks q n).filter (fun c => e c = false)).length

/-- Mutant 3 of E-511: an extra hypothesis `0 < n` (a weaker claim). -/
def E511_extraHyp : Prop :=
  ∀ (e : Int → Bool) (q : Int) (n : Nat), 0 < n → ∀ (B : List Int), B.Nodup → ∀ (lag : Int → Nat),
    (∀ b ∈ B, q ≤ b - (lag b : Int) ∧ b < q + (n : Int) ∧ e b = true ∧
      P2 (past e b (lag b)) ∧ Clean e b (lag b)) →
    B.length ≤ ((clocks q n).filter (fun c => e c = false)).length

/-- A deliberately vacuous "theorem" of the 2026-09-15 kind: the conclusion is a
hypothesis.  Lean accepts it; the pin check must not. -/
theorem vacuous_capacity (e : Int → Bool) (p : Nat) (t : Int)
    (h : suppliedPhases e t p ≤ subtractionPhases e t p) :
    suppliedPhases e t p ≤ subtractionPhases e t p := h

end RecamanPins
