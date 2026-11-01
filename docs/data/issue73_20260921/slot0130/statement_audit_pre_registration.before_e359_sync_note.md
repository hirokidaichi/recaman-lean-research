# Registration-prep statement audit: frozen short W/Q core

## Status and boundary

This is a pre-registration packet, not an official `docs/statement_audits/E-NNN.md`.
No evidence ID is reserved and no registry row is added. The harness command
`python3 scripts/harness_gate.py --audit-template E-999` rejected the request with
`E-999 not in docs/EVIDENCE_REGISTRY.tsv`; therefore creating `E-360.md` or another numbered
file before a registry decision would incorrectly claim a reservation. The eventual reviewer
must generate the official file only after the parent fixes the exact row and cited symbol list.
This packet addresses the G5 material's syntactic and semantic prerequisites (exact signatures,
binder/defined-Prop audit and claim correspondence). The machine check of an actual registry row
has not run because no row exists; that unperformed row-level check is not reported as passing.

Reviewed source identity:

- `Recaman/ShortTightDonorAvoidance.lean` through
  `short_tight_avoids_ss2_donor`: SHA-256
  `bb12f35acc8e48c584cead52d675e36b034afda22f0f28ecfd245031f70fee85`.
- `Recaman/OwnerFamilyLagEleven.lean`: SHA-256
  `0bc2293b5d67f7ef5865f7a3f67b2fbf10aeb76bfa92eac9a086cc893c5846f4`.
- `Recaman/PeriodicOwnerFamilyLagEleven.lean`: SHA-256
  `a90c8f2ac7e6b98dfda4a260434d2e44d3e35781c3212f6a04b7952e9ef6b4c0`.

The ten core declarations and the two constructors below are the entire audit boundary.
`short_supply_donor_deletion` and later declarations, `SS2OldestPattern`, and the p32/33
holdout certification are excluded. The original cards H-20260917-01 (Q) and H-20260920-01
(W) remain `CONJECTURED`; this packet does not itself authorize promotion.

## Definitions expanded

`past e t d` is the newest-first list of the preceding `d` signs:

```lean
def past (e : Int -> Bool) (t : Int) (d : Nat) : List Bool :=
  (List.range d).map fun i => e (t - ((i+1 : Nat) : Int))
```

The word-level P2 predicate occurring in the signatures is not an unproved research
hypothesis; it is the following conjunction:

```lean
def P2 (w : List Bool) : Prop := mass w = 1 ∧ moment w = 0
```

`phase p t := (t % p).toNat`. `neighborhood e p A lag` filters the period's subtraction
phases to those covered by a member window in `A`. `trueOldestPhase` uses the actual oldest
S offset, not the fixed endpoint 11:

```lean
def trueOldestPhase (e : Int -> Bool) (p : Nat) (u0 : Nat) (d : Nat) : Nat :=
  endpointPhase p (u0 : Int) (oldestOffset (past e (u0 : Int) d))
```

The only nonstandard defined `Prop` used as a theorem hypothesis is `OwnerFamily`. Its semantic
fields are shown below in an ASCII-normalized rendering; the punctuation-preserving source lines
are in `core_signatures_verbatim.txt`:

```lean
structure OwnerFamily (e : Int -> Bool) (mem : Int -> Prop)
    (own : Int -> Int) (lag : Int -> Nat) : Prop where
  window : ∀ b, mem b -> past e b (lag b) ∈ ownerWords
  addA : ∀ b, mem b -> e b = true
  own_mem : ∀ b, mem b ->
    ∃ k ∈ sOffsets (past e b (lag b)), own b = b - (k : Int)
  onto : ∀ b, mem b -> ∀ k ∈ sOffsets (past e b (lag b)),
    ∃ b', mem b' ∧ own b' = b - (k : Int)
```

Thus it says: every member has one of the twenty minimal P2 words of lengths 3/7/11 and is
an A clock; its single-valued owner map selects an S in its own window; every S in every member
window is selected by some member. It contains no future-A, donor-avoidance, oldest-owner,
periodicity, Hall, or conclusion field. The four local W-chain theorems below are nevertheless
conditional (`C`) when read alone; the periodic constructors discharge this structure from
concrete Hall/tightness hypotheses.

## R/W/C/T theorem-content classification

The classifications follow the statement-content distinctions in
`docs/AUDIT_GRAND_SYNTHESIS_2026-09-15.md`: R has concrete mathematical content, W is a
wrapper/constructor restatement, C assumes a key defined structural hypothesis, and T is a free
arithmetic tautology. Here R means that the declaration's body performs concrete semantic work;
it does not by itself assert historical novelty or authorize a separate evidence claim. Counts
over the twelve audited declarations are `R/W/C/T = 6/2/4/0`.

| declaration | class | reason |
|---|---:|---|
| `shortOff_le_window` | R | concrete sign word and actual P2 window; proves selector locality |
| `short_window_hall` | R | constructs an injection into the actual neighborhood |
| `member_window_aas_or_w1` | C | substantive case elimination, conditional on `OwnerFamily` |
| `w1_owns_oldest` | C | substantive paired-S argument, conditional on `OwnerFamily` |
| `w1_future_aas_member` | C | substantive offset exhaustion, conditional on `OwnerFamily` |
| `w1_next_addition` | C | derived future sign, still conditional on `OwnerFamily`; harness says substantive |
| `tight_w1_next_addition` | W | transports local W through `tight_owner_family` |
| `donor_cover_next_subtraction` | R | concrete donor/w1 overlap classification |
| `short_tight_avoids_trueOldest` | R | concrete periodic phase lift and A/S contradiction |
| `short_tight_avoids_ss2_donor` | R | discharges donor classification and Hall on each short sublist |
| `ownerFamily_of_minimal` | W | structure constructor from its fully expanded fields; not a research result alone |
| `tight_owner_family` | R | realizes `OwnerFamily` from concrete Hall, tightness, windows and periodicity; extracted from the existing E-359 proof, so not new research |

There is no T declaration. The C declarations are not advertised as unconditional results;
their realizability is supplied by the final constructor before the periodic W/Q statements.

## Semantic R/W/C/T

This second use of R/W/C/T follows the prior draft's semantic checklist and is kept distinct
from the theorem-content counts above.

- **R / reachability:** no theorem asserts reachability by the canonical Recaman orbit. The
  quantified object is an arbitrary periodic sign word. `tight_owner_family` proves realizability
  of the ownership structure from Hall/tightness, not realizability of the sign word as an orbit.
- **W / windows:** `past` is newest-first; offset `i+1` is clock `t-1-i`. The donor oldest offset
  is 10 for d1/d2/d3/d6 and 11 for d4/d5/d7. Phase equality is transported through periodicity
  before an absolute-clock equality is used. The short selector is proved to lie inside the
  supplied window, not merely somewhere in the period's subtraction list.
- **C / constraints:** B is nodup, tight, within phase bounds, current-A, and has minimal P2
  windows with lag in {3,7,11}. The donor is a minimal length-11 P2 word with SS count exactly 2.
  The final theorem has no assumed Hall because Hall is constructed for every short sublist.
  Full U, positive drift, future A, donor avoidance, and all-lag capacity are not premises.
- **T / target:** the exact target is
  `trueOldestPhase e p u0 11 ∉ neighborhood e p B lag`. It is not deletion survival, general
  Gate T6, E-070/E-067, actual-orbit nonperiodicity, or surjectivity.

## Statement renderings and G5 checks

The line-for-line, punctuation-preserving source excerpts for all ten core declarations,
`OwnerFamily`, and the two constructors are in `core_signatures_verbatim.txt` next to this file.
The multiline blocks below normalize `→`/`≤` to ASCII in a few places for annotation; they are
not substituted for that verbatim evidence.

### 1. `shortOff_le_window`

```lean
theorem shortOff_le_window (e : Int -> Bool) (p u d : Nat) (hu : u < p)
    (hA : e (u : Int) = true) (hd : d <= 11) (hP : P2 (past e (u : Int) d)) :
    1 <= Recaman.ShortReservoirCapacity.shortOff e u ∧
      Recaman.ShortReservoirCapacity.shortOff e u <= d
```

Binders: sign word `e`, period/range `p,u`, actual window length `d`, current A and P2
conditions. Japanese claim: 「既存 short selector の offset は実際の P2 窓の中にある」。
Formal-to-Japanese and Japanese-to-formal both match. G5: concrete `e`/window yes; no unproved
defined-Prop hypothesis; not a wrapper (`R`).

### 2. `short_window_hall`

```lean
theorem short_window_hall (e : Int -> Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x) (A : List Nat) (lag : Nat -> Nat)
    (hAn : A.Nodup) (hAp : ∀ u ∈ A, u < p) (hA : ∀ u ∈ A, e (u : Int) = true)
    (hlag : ∀ u ∈ A, lag u <= 11)
    (hP : ∀ u ∈ A, P2 (past e (u : Int) (lag u))) :
    A.length <= (neighborhood e p A lag).length
```

Binders explicitly give a positive period, periodic sign word, nodup phase list, phase bounds,
current A, lag at most 11 and actual P2 windows. Japanese: 「任意の短い供給窓 list は自分自身の
近傍に Hall を満たす」。No minimality or ambient U is asserted. G5: concrete yes; no
unproved defined Prop; non-wrapper injection/locality proof (`R`).

### 3. `member_window_aas_or_w1`

```lean
theorem member_window_aas_or_w1 (e : Int -> Bool) (mem : Int -> Prop)
    (own : Int -> Int) (lag : Int -> Nat) (hF : OwnerFamily e mem own lag)
    (t : Int) (ht : mem t) :
    past e t (lag t) = aas ∨ past e t (lag t) = w1
```

Binders are the stream, member predicate, functional owner, lag, expanded family above, and
one member. Japanese: 「lag 3/7/11 owner family のメンバーは E-357 の除外後 AAS または w1」。
G5: concrete yes; `OwnerFamily` is a defined structural premise (`C`); conclusion is not a
field of the structure and proof is not a wrapper.

### 4. `w1_owns_oldest`

```lean
theorem w1_owns_oldest (e : Int -> Bool) (mem : Int -> Prop) (own : Int -> Int)
    (lag : Int -> Nat) (hF : OwnerFamily e mem own lag) (t : Int) (ht : mem t)
    (hw : past e t (lag t) = w1) : own t = t - 7
```

Japanese: 「w1 メンバーはその真の最古 S（offset 7）を所有する」。This is not hidden in
`OwnerFamily`: `onto`, paired-S exclusion and functionality force it. G5: concrete yes; defined
premise yes (`C`); substantive, not wrapper.

### 5. `w1_future_aas_member`

```lean
theorem w1_future_aas_member (e : Int -> Bool) (mem : Int -> Prop)
    (own : Int -> Int) (lag : Int -> Nat) (hF : OwnerFamily e mem own lag)
    (t : Int) (ht : mem t) (hw : past e t (lag t) = w1) :
    mem (t + 2) ∧ lag (t + 2) = 3 ∧ past e (t + 2) 3 = aas ∧
      own (t + 2) = t - 1
```

Japanese: 「w1 の newest S は t+2 の実メンバー AAS に所有される」。All four conjuncts
are formal conclusions, not prose extras. G5: concrete yes; defined premise yes (`C`);
substantive offset exhaustion, not wrapper.

### 6. `w1_next_addition`

```lean
theorem w1_next_addition (e : Int -> Bool) (mem : Int -> Prop) (own : Int -> Int)
    (lag : Int -> Nat) (hF : OwnerFamily e mem own lag) (t : Int) (ht : mem t)
    (hw : past e t (lag t) = w1) : e (t + 1) = true
```

Japanese W: 「owner family の w1 メンバーの次符号は A」。The future sign is absent from
the expanded premise and is read from the forced AAS member. G5: concrete yes; defined premise
yes (`C`); harness classifies the proof substantive, not a syntactic wrapper. No E-351 theorem
is referenced.

### 7. `tight_w1_next_addition`

```lean
theorem tight_w1_next_addition (e : Int -> Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U B : List Nat) (lag : Nat -> Nat) (hU : U.Nodup)
    (hhall : ∀ A : List Nat, List.Sublist A U ->
      A.length <= (neighborhood e p A lag).length)
    (hB : List.Sublist B U)
    (htight : (neighborhood e p B lag).length = B.length)
    (hBp : ∀ b ∈ B, b < p) (hB_A : ∀ b ∈ B, e (b : Int) = true)
    (hB_lag : ∀ b ∈ B, lag b = 3 ∨ lag b = 7 ∨ lag b = 11)
    (hB_P2 : ∀ b ∈ B, P2 (past e (b : Int) (lag b)))
    (hB_min : ∀ b ∈ B, ∀ d, d < lag b -> 0 < d ->
      ¬ P2 ((past e (b : Int) (lag b)).take d))
    (t : Int) (ht : phase p t ∈ B)
    (hw : past e t (lag (phase p t)) = w1) : e (t + 1) = true
```

Every Hall, tightness, phase, addition, lag and minimality binder is explicit. Japanese:
「周期的な短い緊密 B へ W を移送」。G5: concrete yes; no unproved defined Prop in the
signature; proof is a faithful wrapper around `tight_owner_family` and local W (`W`). It is not
a separate substantive result.

### 8. `donor_cover_next_subtraction`

```lean
theorem donor_cover_next_subtraction (e : Int -> Bool) (u0 t : Int)
    (hdon : past e u0 11 ∈ donors) (htA : e t = true)
    (hw : past e t 7 = w1)
    (hcov : ∃ k : Nat, k < 7 ∧ e (t - 1 - (k : Int)) = false ∧
      t - 1 - (k : Int) = u0 - (oldestOffset (past e u0 11) : Int)) :
    e (t + 1) = false
```

Japanese: 「7 donor の真の最古 S を w1 が覆う3配置は、w1 の次 clock を S にする」。
It uses `oldestOffset`, not fixed 11. G5: concrete yes; no unproved defined Prop; finite donor
overlap proof (`R`).

### 9. `short_tight_avoids_trueOldest`

```lean
theorem short_tight_avoids_trueOldest (e : Int -> Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U B : List Nat) (lag : Nat -> Nat) (hU : U.Nodup)
    (hhall : ∀ A : List Nat, List.Sublist A U ->
      A.length <= (neighborhood e p A lag).length)
    (hB : List.Sublist B U)
    (htight : (neighborhood e p B lag).length = B.length)
    (hBp : ∀ b ∈ B, b < p) (hB_A : ∀ b ∈ B, e (b : Int) = true)
    (hB_lag : ∀ b ∈ B, lag b = 3 ∨ lag b = 7 ∨ lag b = 11)
    (hB_P2 : ∀ b ∈ B, P2 (past e (b : Int) (lag b)))
    (hB_min : ∀ b ∈ B, ∀ d, d < lag b -> 0 < d ->
      ¬ P2 ((past e (b : Int) (lag b)).take d))
    (u0 : Nat) (hdon : past e (u0 : Int) 11 ∈ donors) :
    Recaman.TrueOldestGateT6.trueOldestPhase e p u0 11 ∉
      neighborhood e p B lag
```

Japanese Q-kernel: 「明示した Hall と短い緊密 B の下で、lag-11 donor の真の最古 S phase
は N(B) に入らない」。G5: concrete yes; no unproved defined Prop; phase-to-clock transport,
AAS exclusion and w1 A/S contradiction are substantive (`R`). No positive mass, full U, donor
membership in U, or period upper bound is claimed.

### 10. `short_tight_avoids_ss2_donor`

```lean
theorem short_tight_avoids_ss2_donor (e : Int -> Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (B : List Nat) (lag : Nat -> Nat) (hBn : B.Nodup)
    (htight : (neighborhood e p B lag).length = B.length)
    (hBp : ∀ b ∈ B, b < p) (hB_A : ∀ b ∈ B, e (b : Int) = true)
    (hB_lag : ∀ b ∈ B, lag b = 3 ∨ lag b = 7 ∨ lag b = 11)
    (hB_P2 : ∀ b ∈ B, P2 (past e (b : Int) (lag b)))
    (hB_min : ∀ b ∈ B, ∀ d, d < lag b -> 0 < d ->
      ¬ P2 ((past e (b : Int) (lag b)).take d))
    (u0 : Nat) (hPdon : P2 (past e (u0 : Int) 11))
    (hmindon : ∀ d, d < 11 -> 0 < d ->
      ¬ P2 ((past e (u0 : Int) 11).take d))
    (hss : Recaman.OneSSMultiplicity.ssCount (past e (u0 : Int) 11) = 2) :
    Recaman.TrueOldestGateT6.trueOldestPhase e p u0 11 ∉
      neighborhood e p B lag
```

This is the strongest reviewed Q. Japanese: 「周期上の nodup な緊密 B の各窓が最小 P2 で
lag 3/7/11、donor が最小 lag-11 P2 かつ SS=2 なら、その真の最古 S phase は N(B) 外」。
The formal theorem is stronger than the original Q in dropping ambient U, its completeness,
positive sign sum, donor membership, and assumed Hall: `short_window_hall` constructs Hall on
every sublist of B. It proves exactly the same nonmembership conclusion and does not generalize
to lag >= 15, SS>=3, all-lag Gate T6, or the Recaman orbit. G5: concrete yes; no unproved defined
Prop; substantive composition (`R`).

### 11. `ownerFamily_of_minimal`

```lean
theorem ownerFamily_of_minimal (e : Int -> Bool) (mem : Int -> Prop)
    (own : Int -> Int) (lag : Int -> Nat)
    (hlag : ∀ b, mem b -> lag b = 3 ∨ lag b = 7 ∨ lag b = 11)
    (hP : ∀ b, mem b -> P2 (past e b (lag b)))
    (hmin : ∀ b, mem b -> ∀ d, d < lag b -> 0 < d ->
      ¬ P2 ((past e b (lag b)).take d))
    (haddA : ∀ b, mem b -> e b = true)
    (hown : ∀ b, mem b ->
      ∃ k ∈ sOffsets (past e b (lag b)), own b = b - (k : Int))
    (honto : ∀ b, mem b -> ∀ k ∈ sOffsets (past e b (lag b)),
      ∃ b', mem b' ∧ own b' = b - (k : Int)) :
    OwnerFamily e mem own lag
```

All six concrete inputs are visible: lag class, P2, minimality, current A, ownership within a
window, and onto coverage. Japanese: 「具体条件から OwnerFamily record を組み立てる」。G5:
concrete window binders yes; no unproved defined Prop hypothesis; this is a refactor/constructor
and not separate research (`W`).

### 12. `tight_owner_family`

```lean
theorem tight_owner_family (e : Int -> Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U B : List Nat) (lag : Nat -> Nat) (hU : U.Nodup)
    (hhall : ∀ A : List Nat, List.Sublist A U ->
      A.length <= (neighborhood e p A lag).length)
    (hB : List.Sublist B U)
    (htight : (neighborhood e p B lag).length = B.length)
    (hBp : ∀ b ∈ B, b < p) (hB_A : ∀ b ∈ B, e (b : Int) = true)
    (hB_lag : ∀ b ∈ B, lag b = 3 ∨ lag b = 7 ∨ lag b = 11)
    (hB_P2 : ∀ b ∈ B, P2 (past e (b : Int) (lag b)))
    (hB_min : ∀ b ∈ B, ∀ d, d < lag b -> 0 < d ->
      ¬ P2 ((past e (b : Int) (lag b)).take d)) :
    ∃ own : Int -> Int, Recaman.OwnerFamilyLagEleven.OwnerFamily e
      (fun t => phase p t ∈ B) own (fun t => lag (phase p t))
```

Japanese: 「Hall を満たす U の緊密な短窓 sublist B から、整数 clock 上の実 OwnerFamily
を構成する」。The conclusion is existence, not a premise; it lifts E-358's owner map through
periodic residues and proves every structure field, including onto. G5: concrete yes; no unproved
defined Prop hypothesis; non-wrapper realization (`R`). Historically this is a refactor that
extracts the construction already present inside E-359, not a new research result or separate
claim. It is the reason the C-local lemmas have nonempty periodic applications.

## Dependency and realizability audit

The non-circular chain is:

```text
short selector injection + shortOff locality
  -> Hall on every short sublist
E-358 tight_owner_map + periodic residue transport
  -> tight_owner_family -> concrete OwnerFamily
E-357 lag-11 and w2 exclusions + E-353 paired-old-S rules + OwnerFamily onto
  -> AAS/w1 classification -> w1 owns oldest -> future AAS -> W
E-348 donor/w1 overlap + E-350 AAS endpoint separation + W
  -> Q for an explicit donor
minimal P2 length 11 + SS=2 classification + constructed short Hall
  -> semantic Hall-free Q
```

E-351's `aas_after_w1_forced` is absent from the three frozen sources and cannot be used backward
to prove W. `full U`, minimal lag outside B, positive sign sum and orbit generation are not hidden
in any binder.

Realizability is not empty-only. The local finite family has members `{-3,0,2}`, words
`{AAS,w1,AAS}`, owners `{-6,-7,-1}`. Period 10 `SSAAAASAAA` has tight
`B={4,7,9}`. Period 20 `SSAAAASAAAAAAAAASAAA` has full supply `{4,7,9,19}` and proper tight
`B={4,7,9}`. These examples demonstrate local W, a periodic tight w1 family, and a proper-U
instance; they are controls, not universal proofs.

## Negative controls and remaining limits

- E-240, period 18 `AAAASSAAAASAAASASS`, tight
  `B={2,8,11,13}`, `N(B)={4,5,10,17}`, remains a valid non-pure-AAS control. The proof does not
  use the stopped pure-AAS route.
- Period 15 `AAAASAAASASASSS`: donor phase 3 has true offset 10/phase 8; fixed offset 11/phase 7
  is A. Any replacement of `oldestOffset` by 11 fails this control.
- Removing `OwnerFamily.onto` admits a singleton w1 root with next S. Allowing multivalued
  ownership lets the root consume all three S clocks and also permits next S.
- Removing tightness gives period 8 `SSAAAASA`, w1 at 7 followed by S.
- Removing SS=2 gives period 12 `AAAASAAASSSS`, donor 3, tight `B={7}`, `N={4}`, where the
  donor's oldest is covered.
- The no-tight period 11 control `AAAASASASSS`, `B={5}`, `N={4,9,10}`, and the no-SS2 period 12
  control are weakenings, not counterexamples to the frozen theorem.
- `short_supply_donor_deletion`, all later ShortTight declarations, arbitrary lag donors,
  SS2OldestPattern, the p32/33 holdout as independently certified evidence, actual Recaman
  orbit generation, E-070/E-067 and surjectivity remain outside this packet.

## Promotion decision

This packet fills the missing registration-prep statement material, but it cannot erase the
historical absence of a pre-formalization independent entry check or the first checker's missing
pre-correction source/raw log. Promotion still requires a separately owned destructive audit of
this exact source identity, a fresh successful repository check, an actual reserved registry ID,
and an official G5 file generated for the final cited symbol list. Until then both Q and W cards
remain `CONJECTURED` and no registry/frontier/proof-map change is authorized.
