# Statement audit draft for H-20260921-01

This is a pre-registration audit draft, not an E-number request.

## Verbatim target signature

```lean
theorem short_supply_donor_deletion (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U : List Nat) (lag : Nat → Nat) (hUn : U.Nodup)
    (hUp : ∀ u ∈ U, u < p)
    (hU_A : ∀ u ∈ U, e (u : Int) = true)
    (hU_lag : ∀ u ∈ U, lag u = 3 ∨ lag u = 7 ∨ lag u = 11)
    (hU_P2 : ∀ u ∈ U, P2 (past e (u : Int) (lag u)))
    (hU_min : ∀ u ∈ U, ∀ d, d < lag u → 0 < d → ¬ P2 ((past e (u : Int) (lag u)).take d))
    (u0 : Nat) (hPdon : P2 (past e (u0 : Int) 11))
    (hmindon : ∀ d, d < 11 → 0 < d → ¬ P2 ((past e (u0 : Int) 11).take d))
    (hss : Recaman.OneSSMultiplicity.ssCount (past e (u0 : Int) 11) = 2)
    (B : List Nat) (hBU : List.Sublist B U) :
    B.length ≤ (Recaman.TwoSSTightDisjoint.deletedNeighborhood e p B lag
      (Recaman.TrueOldestGateT6.trueOldestPhase e p u0 11)).length := by
```

`raw/target_signature.log` preserves this signature together with the proof body from the source
spelling verbatim.

## Definition expansion (normalized excerpts)

The following definition excerpts are normalized to ASCII for compact reading and are not claimed to
be verbatim source quotations. The target signature above and `raw/target_signature.log` are the
verbatim materials under audit.

```lean
def P2 (w : List Bool) : Prop := mass w = 1 /\ moment w = 0

def past (e : Int -> Bool) (t : Int) (d : Nat) : List Bool :=
  (List.range d).map fun i => e (t - ((i+1 : Nat) : Int))

def ssCount : List Bool -> Nat
  | [] => 0
  | b::w => (if b=false /\ w.head?=some false then 1 else 0)+ssCount w

def neighborhood (e : Int -> Bool) (p : Nat) (A : List Nat)
    (lag : Nat -> Nat) : List Nat :=
  (LagElevenPeriodic.subPhases e 0 p).filter
    (fun s => isCoveredBySubset e p A lag s)

def deletedNeighborhood (e : Int -> Bool) (p : Nat) (A : List Nat)
    (lag : Nat -> Nat) (s : Nat) : List Nat :=
  (neighborhood e p A lag).filter (fun y => decide (y != s))

def trueOldestPhase (e : Int -> Bool) (p : Nat) (u0 : Nat) (d : Nat) : Nat :=
  endpointPhase p (u0 : Int) (oldestOffset (past e (u0 : Int) d))
```

`P2` is a transparent arithmetic property of an explicit Boolean word, not an unproved research
hypothesis. The other definitions are concrete functions/testers. No conclusion is hidden in them.

## G5-style questions

- Do binders mention `e` and windows/phase lists? Yes: `e`, periodicity, `U`, `B`, `lag`, explicit
  `past` windows, `neighborhood`, and `trueOldestPhase` all occur.
- Is any hypothesis an unproved defined `Prop` or the conclusion itself? No. `P2` unfolds to two
  equalities. Minimality, membership, periodicity, nodup, range, current-A, and SS count are explicit.
- Is the proof a wrapper? Syntactically no under the heuristic, because it restricts hypotheses,
  proves Hall, performs a tight/slack case split, and invokes two deletion lemmas. Semantically its
  donor-specific mathematical content is entirely the already registered Q; it is a direct corollary
  and must not be counted as new mathematical input.

## Missing binders and consequences

There is no `u0 in U`, no assertion that U contains all supplied phases, no positive period mass, no
actual Recaman state/orbit, and no permission for lag 15 or larger in U. Consequently the statement
cannot establish general Gate T6, E-070, E-067, or an orbit claim.

## Preliminary judgment

Meaningful and nonvacuous in the all-short restricted class; not conclusion-assuming; direct
corollary rather than frontier-changing mathematics. Independent audit must decide the final card
label (`PROVED-LEAN` for the exact already checked corollary versus keeping the research claim pending)
without creating a new registry claim.
