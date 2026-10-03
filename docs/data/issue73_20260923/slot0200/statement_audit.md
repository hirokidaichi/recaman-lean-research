# H-20260920-03 statement and dependency audit (candidate)

Target: `Recaman/ShortTightDonorAvoidance.lean` at SHA-256
`bb12f35acc8e48c584cead52d675e36b034afda22f0f28ecfd245031f70fee85`.
The original card is frozen in `original_card_at_freeze.md` (SHA-256
`3ad887aff9cf89b84471de4a8f85b62cb8abe5d411455e3c085e8e0cb1771b16`).

## Original exact claim

For every `e : Int -> Bool`, positive period `p` with
`forall x, e (x+p)=e x`, and nodup `B : List Nat` of in-range current-A
phases, assign each `b in B` a P2 window of length `lag b <= 11`.
Let `m b` be its least positive P2 prefix. If
`(neighborhood e p B lag).length = B.length`, then
`neighborhood e p B m = neighborhood e p B lag`.
This claim requires full-window `P2 (past e b (lag b))` and leastness of
`m b`; it does not require a donor. The exact English is in the frozen card.

## Verbatim source signatures

From lines 531-534 (also frozen in `ShortTightDonorAvoidance.snapshot.lean`
and checked against `signature.stdout`):

```lean
theorem exists_minimal_p2_prefix (e : Int → Bool) (t : Int) (d : Nat)
    (hP : P2 (past e t d)) :
    ∃ m, m ≤ d ∧ P2 (past e t m) ∧
      ∀ k, k < m → 0 < k → ¬ P2 ((past e t m).take k) := by
```

From lines 548-550:

```lean
theorem neighborhood_prefix_sublist (e : Int → Bool) (p : Nat) (B : List Nat)
    (m lag : Nat → Nat) (hle : ∀ b ∈ B, m b ≤ lag b) :
    List.Sublist (neighborhood e p B m) (neighborhood e p B lag) := by
```

From lines 572-579:

```lean
theorem tight_neighborhood_eq_of_p2_prefix (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (B : List Nat) (m lag : Nat → Nat) (hBn : B.Nodup)
    (hBp : ∀ b ∈ B, b < p) (hBA : ∀ b ∈ B, e (b : Int) = true)
    (hle : ∀ b ∈ B, m b ≤ lag b) (hbound : ∀ b ∈ B, lag b ≤ 11)
    (hP : ∀ b ∈ B, P2 (past e (b : Int) (m b)))
    (htight : (neighborhood e p B lag).length = B.length) :
    neighborhood e p B m = neighborhood e p B lag := by
```

## Both directions

- Original card to source: use `exists_minimal_p2_prefix` at every full
  P2 window, choose `m`, then pass `m <= lag` and `P2(m)` to the source
  theorem. `take_past` identifies the minimality predicate with all shorter
  past windows. The source theorem returns the exact claimed equality.
- Source to original card: the source premise is strictly broader as a
  *domain of direct application*. It does not ask whether `P2(lag)` holds,
  nor whether `m` is least. Thus a source instance alone cannot certify an
  instance of the original strict-reduction subcase. `AAAS` at period 4,
  `B=[2]`, `m=3`, `lag=4` has P2 prefix `AAS`, full window `AASA` with
  `P2(lag)=false`, and both neighborhoods `[3]`. This is source-strict and
  tight, but outside the exact card.
- The exact card is not wholly empty: period 4 `AAAS`, `B=[2]`,
  `m=lag=3` has current A, P2 `AAS`, tight `N=[3]`. It exercises only
  identity reduction. The original p1..12/p15 experiment has zero tight
  nonminimal assignments, so it does not exercise strict `m<lag` under
  the card's full premises. This is a finite gap, not a universal
  impossibility proof.

## Proof dependencies and meaning

`exists_minimal_p2_prefix` uses strong induction and `take_past`; it has no
donor or H-02 premise. `neighborhood_prefix_sublist` uses only the definition
of coverage and `m <= lag`; it does not need P2. The equality theorem calls
`short_window_hall` on `m` to get `|B| <= |N_m|`. Inclusion gives
`N_m` as a sublist of `N_lag`; tightness gives `|N_lag|=|B|`.
Equal finite lengths force equality of the neighborhood lists. `neighborhood`
filters `subPhases e 0 p`, itself a filtered `List.range p`; the finite
checker compares the same phase sets rather than depending on list order.
This is a direct composition of the short Hall inequality, prefix inclusion,
and finite-list length equality. Its Lean proof is substantive in the harness
syntax test; that test alone does not establish a new independent mathematical
input for the original strict subcase.

The equality theorem calls neither `short_tight_avoids_ss2_window` nor H-02.
The later `short_p2_tight_avoids_ss2_window` uses `exists_minimal_p2_prefix`
and this equality to transport nonmembership from
`short_tight_avoids_ss2_window`. `short_p2_ss2_deletion` uses the transported
result in its tight branch and short Hall/slack in its other branch. The
H-02 premise is not established by the 01:30 procedural audit; neither
downstream theorem is promoted or treated as an established research
consequence in this packet. E-360's `w1_future_aas_member` is an existing W
dependency, not a new input here.

## Adversarial controls

- Without tightness: period 9 `ASAAASASS`, `B=[4]`, `m=3`, `lag=7` has
  full P2 `AASASSA`, prefix P2 `AAS`, `N_m=[1]`, `N_lag=[1,7,8]`.
- `B=[]` makes the equality immediate but is not the only exact-card case;
  the period-4 singleton above confirms nonempty premises.
- The old finite experiment enumerates every cycle p1..12 and p15 and all
  short-P2 assignments, including every sublist of current-A phases. Its
  `PASS` asserts only positive totals for nonminimal assignments,
  changed nontight neighborhoods, and donor checks. It does **not** assert
  `tight_nonminimal > 0`. The p15 line reports 8,115 nonminimal assignments,
  39,340 tight assignments, and zero in their intersection.
- E-240 refutes pure-AAS forcing; equality permits w1 and does not use that
  route. E-069 refutes global oldest-S injection; the proof uses the existing
  short selector on short P2 windows, not global oldest-S. E-345 is the
  SS>=3 donor deletion countercontrol, outside equality and the SS=2
  downstream claim. E-180 concerns collision-slack-linear and is unrelated.
  H-04's lag-15 counterexample is outside `lag<=11`; its true oldest phase
  must not be replaced by fixed offset 11.

## Scope and decision

The semantic conclusion is an equality for arbitrary periodic sign streams,
not an actual Recaman orbit. The source theorem is accepted by Lean and has
the stated dependencies; the original card's distinctive strict full-P2
tight case has no witness in the predeclared finite ranges. It remains an
explicit nonvacuity gap. No global impossibility, general lag, full-U
capacity, general Gate T6, or surjectivity follows. Procedural verdict is
reserved for the independent Sol auditor; until then H-03 stays
`CONJECTURED` with no registry/frontier promotion.
