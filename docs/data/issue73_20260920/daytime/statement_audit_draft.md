# Draft statement audit: proposed E-360

NOT REGISTERED. This file does not satisfy the weekly independent-review gate by itself.

- artifact: `Recaman/ShortTightDonorAvoidance.lean`
- reviewer: daytime proposer, separate same-session audit pass, 2026-09-20; independent Sol review pending
- For every theorem below, answer the three checks. A "no" on check 1 or a "yes" on check 2/3
  means the row must not be described as resolving anything unconditional.

## Recaman.ShortTightDonorAvoidance.shortOff_le_window

```lean
(e : Int → Bool) (p u d : Nat) (hu : u < p) (hA : e (u : Int) = true) (hd : d ≤ 11) (hP : P2 (past e (u : Int) d)) : 1 ≤ Recaman.ShortReservoirCapacity.shortOff e u ∧ Recaman.ShortReservoirCapacity.shortOff e u ≤ d
```

1. binders mention the sign word `e`, the orbit `a`/`stateAt`, windows or phase lists: yes — the actual sign word and past windows appear.
2. some hypothesis is an unproved defined Prop or is (equivalent to) the conclusion: no — concrete period, phase, P2, minimality and/or tightness conditions; no future-sign or donor-avoidance assumption. Intermediate Hall is an explicit hypothesis only where present.
3. the proof is a wrapper/omega/rfl over imported results: no — substantive proof work (scope and dependencies below).

## Recaman.ShortTightDonorAvoidance.short_window_hall

```lean
(e : Int → Bool) (p : Nat) (hp : 0 < p) (hper : ∀ x : Int, e (x + p) = e x) (A : List Nat) (lag : Nat → Nat) (hAn : A.Nodup) (hAp : ∀ u ∈ A, u < p) (hA : ∀ u ∈ A, e (u : Int) = true) (hlag : ∀ u ∈ A, lag u ≤ 11) (hP : ∀ u ∈ A, P2 (past e (u : Int) (lag u))) : A.length ≤ (neighborhood e p A lag).length
```

1. binders mention the sign word `e`, the orbit `a`/`stateAt`, windows or phase lists: yes — the actual sign word and past windows appear.
2. some hypothesis is an unproved defined Prop or is (equivalent to) the conclusion: no — concrete period, phase, P2, minimality and/or tightness conditions; no future-sign or donor-avoidance assumption. Intermediate Hall is an explicit hypothesis only where present.
3. the proof is a wrapper/omega/rfl over imported results: no — substantive proof work (scope and dependencies below).

## Recaman.ShortTightDonorAvoidance.w1_owns_oldest

```lean
(e : Int → Bool) (mem : Int → Prop) (own : Int → Int) (lag : Int → Nat) (hF : OwnerFamily e mem own lag) (t : Int) (ht : mem t) (hw : past e t (lag t) = w1) : own t = t - 7
```

1. binders mention the sign word `e`, the orbit `a`/`stateAt`, windows or phase lists: yes — the actual sign word and past windows appear.
2. some hypothesis is an unproved defined Prop or is (equivalent to) the conclusion: yes — hF is the explicit structural OwnerFamily premise. Its four fields are window language, current A, one owned S inside each window and surjectivity onto covered S. Neither the conclusion nor oldest ownership is a field. The periodic theorem CONSTRUCTS this family from actual tightness and the independently supplied short Hall theorem; the local theorem alone is conditional on hF.
3. the proof is a wrapper/omega/rfl over imported results: no — substantive proof work (scope and dependencies below).

## Recaman.ShortTightDonorAvoidance.w1_next_addition

```lean
(e : Int → Bool) (mem : Int → Prop) (own : Int → Int) (lag : Int → Nat) (hF : OwnerFamily e mem own lag) (t : Int) (ht : mem t) (hw : past e t (lag t) = w1) : e (t + 1) = true
```

1. binders mention the sign word `e`, the orbit `a`/`stateAt`, windows or phase lists: yes — the actual sign word and past windows appear.
2. some hypothesis is an unproved defined Prop or is (equivalent to) the conclusion: yes — hF is the explicit structural OwnerFamily premise. Its four fields are window language, current A, one owned S inside each window and surjectivity onto covered S. Neither the conclusion nor oldest ownership is a field. The periodic theorem CONSTRUCTS this family from actual tightness and the independently supplied short Hall theorem; the local theorem alone is conditional on hF.
3. the proof is a wrapper/omega/rfl over imported results: no — substantive proof work (scope and dependencies below).

## Recaman.ShortTightDonorAvoidance.short_tight_avoids_trueOldest

```lean
(e : Int → Bool) (p : Nat) (hp : 0 < p) (hper : ∀ x : Int, e (x + p) = e x) (U B : List Nat) (lag : Nat → Nat) (hU : U.Nodup) (hhall : ∀ A : List Nat, List.Sublist A U → A.length ≤ (neighborhood e p A lag).length) (hB : List.Sublist B U) (htight : (neighborhood e p B lag).length = B.length) (hBp : ∀ b ∈ B, b < p) (hB_A : ∀ b ∈ B, e (b : Int) = true) (hB_lag : ∀ b ∈ B, lag b = 3 ∨ lag b = 7 ∨ lag b = 11) (hB_P2 : ∀ b ∈ B, P2 (past e (b : Int) (lag b))) (hB_min : ∀ b ∈ B, ∀ d, d < lag b → 0 < d → ¬ P2 ((past e (b : Int) (lag b)).take d)) (u0 : Nat) (hdon : past e (u0 : Int) 11 ∈ donors) : Recaman.TrueOldestGateT6.trueOldestPhase e p u0 11 ∉ neighborhood e p B lag
```

1. binders mention the sign word `e`, the orbit `a`/`stateAt`, windows or phase lists: yes — the actual sign word and past windows appear.
2. some hypothesis is an unproved defined Prop or is (equivalent to) the conclusion: no — concrete period, phase, P2, minimality and/or tightness conditions; no future-sign or donor-avoidance assumption. Intermediate Hall is an explicit hypothesis only where present.
3. the proof is a wrapper/omega/rfl over imported results: no — substantive proof work (scope and dependencies below).

## Recaman.ShortTightDonorAvoidance.short_tight_avoids_ss2_donor

```lean
(e : Int → Bool) (p : Nat) (hp : 0 < p) (hper : ∀ x : Int, e (x + p) = e x) (B : List Nat) (lag : Nat → Nat) (hBn : B.Nodup) (htight : (neighborhood e p B lag).length = B.length) (hBp : ∀ b ∈ B, b < p) (hB_A : ∀ b ∈ B, e (b : Int) = true) (hB_lag : ∀ b ∈ B, lag b = 3 ∨ lag b = 7 ∨ lag b = 11) (hB_P2 : ∀ b ∈ B, P2 (past e (b : Int) (lag b))) (hB_min : ∀ b ∈ B, ∀ d, d < lag b → 0 < d → ¬ P2 ((past e (b : Int) (lag b)).take d)) (u0 : Nat) (hPdon : P2 (past e (u0 : Int) 11)) (hmindon : ∀ d, d < 11 → 0 < d → ¬ P2 ((past e (u0 : Int) 11).take d)) (hss : Recaman.OneSSMultiplicity.ssCount (past e (u0 : Int) 11) = 2) : Recaman.TrueOldestGateT6.trueOldestPhase e p u0 11 ∉ neighborhood e p B lag
```

1. binders mention the sign word `e`, the orbit `a`/`stateAt`, windows or phase lists: yes — the actual sign word and past windows appear.
2. some hypothesis is an unproved defined Prop or is (equivalent to) the conclusion: no — concrete period, phase, P2, minimality and/or tightness conditions; no future-sign or donor-avoidance assumption. Intermediate Hall is an explicit hypothesis only where present.
3. the proof is a wrapper/omega/rfl over imported results: no — substantive proof work (scope and dependencies below).

## Recaman.ShortTightDonorAvoidance.short_supply_donor_deletion

```lean
(e : Int → Bool) (p : Nat) (hp : 0 < p) (hper : ∀ x : Int, e (x + p) = e x) (U : List Nat) (lag : Nat → Nat) (hUn : U.Nodup) (hUp : ∀ u ∈ U, u < p) (hU_A : ∀ u ∈ U, e (u : Int) = true) (hU_lag : ∀ u ∈ U, lag u = 3 ∨ lag u = 7 ∨ lag u = 11) (hU_P2 : ∀ u ∈ U, P2 (past e (u : Int) (lag u))) (hU_min : ∀ u ∈ U, ∀ d, d < lag u → 0 < d → ¬ P2 ((past e (u : Int) (lag u)).take d)) (u0 : Nat) (hPdon : P2 (past e (u0 : Int) 11)) (hmindon : ∀ d, d < 11 → 0 < d → ¬ P2 ((past e (u0 : Int) 11).take d)) (hss : Recaman.OneSSMultiplicity.ssCount (past e (u0 : Int) 11) = 2) (B : List Nat) (hBU : List.Sublist B U) : B.length ≤ (Recaman.TwoSSTightDisjoint.deletedNeighborhood e p B lag (Recaman.TrueOldestGateT6.trueOldestPhase e p u0 11)).length
```

1. binders mention the sign word `e`, the orbit `a`/`stateAt`, windows or phase lists: yes — the actual sign word and past windows appear.
2. some hypothesis is an unproved defined Prop or is (equivalent to) the conclusion: no — concrete period, phase, P2, minimality and/or tightness conditions; no future-sign or donor-avoidance assumption. Intermediate Hall is an explicit hypothesis only where present.
3. the proof is a wrapper/omega/rfl over imported results: no — substantive proof work (scope and dependencies below).


## Same-session semantic audit (independent review still pending)

- **R / reachability:** no assertion about the canonical Recaman orbit. The object is an arbitrary periodic sign word.
- **W / windows:** past is newest-first. Covered offset i corresponds to clock u-1-i. The donor's true oldest S is offset 10 or 11, not always 11. All shifted clocks are integers; periodicity transfers them by equality of residues.
- **C / constraints:** short_window_hall proves the canonical short charge lies INSIDE the chosen P2 window before using injectivity. An injection into all S phases alone would not imply Hall. The final donor theorem requires minimal lag-11 SS=2; each B window is minimal and has lag 3/7/11. No full U, positive drift, period upper bound, future A, motif decomposition or generic capacity is assumed.
- **T / target:** the exact final conclusion is nonmembership of the true donor subtraction in N(B). The deletion corollary covers all sublists of a supply list whose ENTIRE membership has short minimal windows. It does not cover a sublist with a lag >=15 member.
- The local w1 proof uses E-357 to eliminate w2 and lag11. w2 is NOT ruled out by the root's bits alone; the saved v1 failure exposed precisely that dependency.
- The future-AAS theorem E-351 is not used to prove W. There is no circular use of the desired future sign.
- E-357/359 refactors only extract constructors already present in their proofs. Existing registered theorem signatures are unchanged. They are not claimed as new research results.
- Nonempty examples: finite owner family {-3,0,2}; periodic SSAAAASAAA with B={4,7,9}; period8 donor with a nonempty tight singleton; E-240 remains a permitted non-AAS tight example.
- Negative controls: removing tightness fails at period11; replacing SS=2 by SS=3 fails at period12; missing onto and nonfunctional ownership permit next S in the local model. Donor minimality was not refuted on periods1..12; it is RETAINED.
- The frozen p32/33 data were checked by two different algorithms (iterated sums + matching, and periodic closed formulas + all-subset Hall). This is algorithmic cross-checking in one session, not independent-agent approval.
- Main code has no forbidden proof escape. Full check reports 2561 audited declarations within the allowed axioms.
