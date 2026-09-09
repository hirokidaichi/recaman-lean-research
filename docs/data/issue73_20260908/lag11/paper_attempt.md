# H-20260908-01: lag-11 following-gap extension of φ7

- Unit: `H-20260908-01` only.
- Base revision: `8b07f93fbbb17352c091cabaa333fc366a66c04f`.
- Role: falsifier then paper-formalizer. No Lean, Audit, registry, frontier, or
  visualizer edits.

## Conclusion first

**`REFUTED`:** the original `H_inject11` gap-class statement. There is no
period-independent assignment of each of the 17 minimal lag-11 window types to a
`(S-index shift, following-gap class)` pair disjoint from the three U7 pools
that yields an injection. Two independent failures:

1. Type `HARD=(1,4,7,10,11)` has internal following gaps only `1` and `3`, and
   last-S following gap only `≥2`. It has no U7-disjoint exact gap at all.
2. Exact gap `2`, the only exact gap outside `{1,3,≥4}`, is not internally
   injective among the 11 types that possess it. The cyclic word
   `ASSSASSAAAASSA` (period 14, sign sum `0`) has min-lag-11 phases `t=0` of
   type `(2,3,8,9,11)` and `t=10` of type `(4,5,7,8,9)` charging the same S
   phase `3`. Independent P2 sums are recorded below. Neither type has another
   gap-2 option, so no gap-2 assignment avoids this pair.

**`STOPPED`:** the following-gap partition class as a U7-style proof pattern.
One permitted repair was used (type-indexed U7-avoiding offset, not a new gap
class). That repair does give an injection, but it is a 17-row lookup, not a
gap-class, and is not a template for lag 15. Reopen this class only for a new
invariant, not another lag.

**`PROVED-PAPER`:** the repaired count. For every period `p≥1` and every
`p`-periodic `ε:Z→{−1,+1}` (no positive-sum hypothesis),

```text
|U7 ∪ U11min| ≤ |D|,
```

via the audited φ7 together with the type-to-offset map `φ11` of Lemma 4.
This is strictly stronger than the finite matching `E-078` (`p≤18`). It does
not prove E-067/E-070: min-lag `≥15` remains allowed.

Hypothesis-card status for `H_inject11` as written: `REFUTED`. The residual
injection is a different statement, accepted under unit criterion 1.

## Exact statements

Notation as in Gate 3 / `docs/data/issue73_20260907/macro_proof_attempt.md`.
P2 at lag `d` is the pair of backward identities
`∑_{i=1}^d ε(t-i)=1` and `∑_{i=1}^d i·ε(t-i)=0`. Arithmetic forces `d≡3 (mod 4)`.
U7 uses the minimum such `d` among `{3,7}`:

| min d, type | image | following gap of the image |
|---|---|---|
| d=3, AAS | last S, `t-3` | `≥4` |
| d=7, h=1, S-offsets `{1,6,7}` | `S_{l-2}=t-7` | `=1` |
| d=7, h=2, S-offsets `{2,5,7}` | `S_{l-1}=t-5` | `=3` |

These three image pools partition a subset of `D`. In particular every S whose
following gap is `≥4` is the lag-3 image of the A three steps later (the
backward word from that A is AAS, and `d=3` is the shortest possible P2). So
exact gaps `4,5,7,…` are not U7-disjoint: they are occupied by φ7.

`U11min` is the set of A-phases whose least P2 lag is exactly 11. For `t` in
`U11min`, the length-11 backward word has five S-offsets, a 5-subset of
`{1..11}` summing to `33`, with no P2 prefix of length 3 or 7. There are 17
such types (`COMPUTED` by `lag11_classify.py`, finite list, not a period
census). `N_t` is the set of those five S-phases.

Original `H_inject11` (now `REFUTED`):

```text
there is a period-independent rule assigning each combinatorial
minimal lag-11 window type a unique (S-index shift, following-gap class)
pair disjoint from the three U7 classes, yielding an injection
φ11: U11min → D \ φ7(U7) with φ11(t) ∈ N_t.
```

Repaired statement (`PROVED-PAPER` below):

```text
Let c be the function of Lemma 4, sending each of the 17 types to one
of its five S-offsets. For t in U11min let τ(t) be its offset 5-tuple
and set φ11(t) = t - c(τ(t)) (mod p). Then φ11 is an injection
U11min → D \ φ7(U7) with φ11(t) ∈ N_t.
```

## Falsification

All P2 tests below recompute the two coefficient identities from the cyclic
word, not from incremental caches. Source revision
`8b07f93fbbb17352c091cabaa333fc366a66c04f`.

### HARD window

Newest-first length 11: `SAA SAA SAA SS`. Offsets `(1,4,7,10,11)` sum to 33.
Sign sum `11-10=1`. Prefix 3 contains only offset 1, not `(3)`. Prefix 7
contains `(1,4,7)` summing to 12, not 14. Internal following gaps: `4−1=3`,
`7−4=3`, `10−7=3`, `11−10=1`. Last-S following gap `≥2` because `t` is A.

### Wrap-around `p<11` and small cyclic completions

HARD as a length-11 unfolding forces `ε(t)=+1` and `ε(t-11)=−1`. For `p=11`
these are the same phase, so HARD never occurs. For `p` dividing `10=11−1` the
same obstruction hits offset 10 versus `t`. Exhaust of **all** binary words
(including nonpositive sum) for `p=1..12` found **0** HARD occurrences with
`p<12`, and 12 occurrences at `p=12`, all with residual size 5.

Cyclic completions of the HARD block `SSAASAASAASA`:

- single S after `t`: period 13, residual 5.
- A-padding `AA` / `AAA`: period 14/15, residual 4, the missing S is always
  offset 1 taken by lag 3 at `t+2`.
- `k=1,2,3,4` packed copies: `k` HARD phases, residual 5 each (the next copy
  starts with S, so last-S gap is 2, not a U7 pool).
- two copies with connector `AA`/`AAS`/`AAA`: first copy residual 4 (lag 3
  takes offset 1), second residual 5. Never empty.

Named boundary words `A^12`, `S^12`, `SAAA`, `SSSSAAAASAAA`, `AAASSASSSAA`,
`SAAASAASSSA` contain no HARD occurrence.

Exhaust `p=1..16` all words: 470 HARD occurrences, residual sizes
`{4: 108, 5: 362}`, taken kind only `(offset 1, lag3)`, empty residual 0.
This agrees with the earlier positive-sum scan `hard_type.txt` through `p=18`
(`HARD_OCCURRENCES=1559`, `EMPTY_RESIDUAL=0`, taken only offset 1 by lag 3)
and extends it to nonpositive sums on `p≤16`.

The other five gap-2-less types likewise have no empty residual on `p=1..12`.
Type `(2,3,7,10,11)` does occur with wrap `p<11` (8 words, domain size 3,
residual 2). Type `(4,5,6,7,11)` has residual 2, with lag 3 taking offsets 4
and 11 and lag-7 h=1 taking offset 5; two U7-incompatible S remain.

### Gap-2 collision (kills the un-repaired class)

Word `w=ASSSASSAAAASSA`, `p=14`, `t_A=0`, `t_B=10`. Direct sums:

```text
t=0, d=11: sign sum 1, moment 0, S-offsets (2,3,8,9,11); d=3: (−1,−4); d=7: (3,18)
t=10, d=11: sign sum 1, moment 0, S-offsets (4,5,7,8,9); d=3: (3,6); d=7: (1,−4)
```

Raw `(sign sum, moment, S-offsets)` on prefixes: at `t=0`, d=3 gives
`(−1,−4,(2,3))` and d=7 gives `(3,18,(2,3))`; at `t=10`, d=3 gives
`(3,6,())` and d=7 gives `(1,−4,(4,5,7))`. None is `(1,0)`, so neither
phase has a short P2. Both are genuinely min-lag 11.

Gap-2 charges: type `(2,3,8,9,11)` has unique gap-2 S at offset 11, phase
`(0-11) mod 14 = 3`. Type `(4,5,7,8,9)` has unique gap-2 S at offset 7, phase
`(10-7) mod 14 = 3`. Same image. This word is a cyclic completion of a
Z-glue at distance `7-11 ≡ 10 (mod 14)`.

## Lemma 1 (HARD vs φ7). `PROVED-PAPER`

Let `t` be A with min P2 lag 11 and S-offsets `(1,4,7,10,11)` in the
length-11 backward unfolding. Write the forced signs (offset `i` means time
`t−i`):

```text
i:  0  1  2  3  4  5  6  7  8  9 10 11
ε:  A  S  A  A  S  A  A  S  A  A  S  S
```

The three φ7 rules are exhaustive for U7. Each rule, anchored so that its
image is a prescribed HARD S, is an integer identity on times `t+k`, hence
also holds modulo `p`. Conflicts against forced signs are all-period.

- Offset 1, `s=t−1`, following gap `≥2`.
  lag 3: `t'=t+2`, needs `ε(t+1)=ε(t+2)=+1`. Possible; occupies iff those
  future signs are A.
  h=1: needs following gap 1, already false; also `t'=t+6` needs
  `ε(t'−6)=ε(t)=−1`, but `t` is A.
  h=2: `t'=t+4` needs `ε(t'−7)=ε(t−3)=−1`, offset 3 is A.
- Offset 4, `s=t−4`, following gap 3.
  lag 3: `t'=t−1` is S, not A; also gap `≠≥4`.
  h=1: gap `≠1`; `t'=t+3` needs `ε(t−3)=−1`, offset 3 is A.
  h=2: `t'=t+1` needs `ε(t'−7)=ε(t−6)=−1`, offset 6 is A.
- Offset 7, `s=t−7`, following gap 3.
  lag 3: `t'=t−4` is S.
  h=1: `t'=t` needs offset 4 equal to A, it is S.
  h=2: `t'=t−2` needs `ε(t−9)=−1`, offset 9 is A.
- Offset 10, `s=t−10`, following gap 3.
  lag 3: `t'=t−7` is S.
  h=1: `t'=t−3` needs `ε(t−9)=−1`, offset 9 is A.
  h=2: `t'=t−5` needs `ε(t'−6)=ε(t−11)=+1`, offset 11 is S.
- Offset 11, `s=t−11`, following gap 1.
  lag 3: `t'=t−8` needs `ε(t−10)=+1`, offset 10 is S.
  h=1: `t'=t−4` is S.
  h=2: `t'=t−6` needs `ε(t−8)=−1`, offset 8 is A.

Thus φ7 can occupy at most the phase of offset 1, and only by lag 3.
`N_t \ φ7(U7)` always contains every distinct phase among `{t−4,t−7,t−10,t−11}`.
These four offsets cannot all be congruent to 1 modulo `p`: that would require
`p∣3` and `p∣10`, hence `p∣1`. So the residual is nonempty, and empty residual
is impossible even after wrap identifications. In particular HARD is
incompatible with φ7 occupying all five of its S.

The same identities show that a U7 pattern occupying an internal HARD S cannot
be created by wrap-around: every conflicting pair is of the form `t−i` versus
`t−j` with `i,j∈{0,…,11}`. Confirmed by a wrap-aware occupancy scan for
`p=1..21` (`HARD_INTERNAL_U7_WRAP=[]`).

## Lemma 2 (gap 2 is never a φ7 image). `PROVED-PAPER`

U7 images have following gaps in `{1,3}∪[4,∞)`. An S with exact following gap
2 has next S two steps later, so the intermediate sign is A and the second
step is S. That blocks AAS (needs three A after the S), blocks h=1 (needs gap
1), and blocks h=2 (needs gap 3).

## Lemma 3 (the other five gap-2-less types). `PROVED-PAPER`

Each has at least one internal S whose three U7 patterns contradict the
forced window. Exact gap `≥4` is always a lag-3 image (Lemma 2's complement).
Conflicts, offset → why no U7 image:

- `(1,2,9,10,11)`, newest `SSAAAAAASSS`. Offset 9 has gap 7, hence is lag 3
  at `t−6`. Offset 10, gap 1: h=1 at `t−3` needs `ε(t−4)=−1`, offset 4 is A.
  Offset 11, gap 1: h=1 at `t−4` needs `ε(t−5)=−1`, offset 5 is A.
  Safe residual S: 10 and 11.
- `(1,5,6,10,11)`. Offsets 5 and 10 have gap 4, both lag-3 images. Offset 6,
  gap 1: h=1 at `t+1` needs `ε(t)=−1`, but `t` is A. Offset 11, gap 1: h=1 at
  `t−4` needs `ε(t−6)=+1`, offset 6 is S. Safe: 6 and 11.
- `(1,5,8,9,10)`. Offset 5 has gap 4, lag 3. Offset 8, gap 3: h=2 at `t−3`
  needs `ε(t−9)=+1`, offset 9 is S. Offsets 9 and 10, gap 1: h=1 needs
  `ε(t−3)` or `ε(t−4)` equal to S, both A. Safe: 8, 9, 10.
- `(2,3,7,10,11)`. Offset 7 has gap 4, lag 3. Offset 10, gap 3: h=2 at `t−5`
  needs `ε(t−11)=+1`, offset 11 is S. Offset 11, gap 1: h=1 at `t−4` needs
  `ε(t−5)=−1`, offset 5 is A. Safe: 10 and 11.
- `(4,5,6,7,11)`. Last S at offset 4 has following gap `≥5`, hence is always
  lag 3 at `t−1`. Offset 11 has gap 4, lag 3. Offset 5, gap 1, is compatible
  with h=1 in the future (and is occupied in the period-12 completion).
  Offset 6, gap 1: h=1 at `t+1` needs `ε(t)=−1`. Offset 7, gap 1: h=1 at `t`
  needs offset 1 equal to S, it is A. Safe: 6 and 7.

Together with Lemma 1, every gap-2-less type has a nonempty residual after φ7,
and a uniform choice of residual S (offsets 10, 4, 6, 8, 10, 6 respectively
in the order of this list plus HARD).

## Lemma 4 (one repaired charge). `PROVED-PAPER`

Allowed charges for a type: an S-offset that is either exact gap 2 (Lemma 2)
or U7-pattern-incompatible with the forced window (as in Lemmas 1 and 3).
Naive preference for gap 2 fails injectivity by the `p=14` word above: types
`(2,3,8,9,11)` and `(4,5,7,8,9)` have unique gap-2 offsets 11 and 7.

The one repair: choose, for each of the 17 types, one allowed offset so that
no two types with distinct offsets admit a sign-consistent placement of their
length-11 windows at the unique relative shift that would identify the charged
S. One such assignment (`SOLUTION0`) is

```text
(1,2,9,10,11)  → 10     (1,3,8,10,11)  → 3      (1,4,7,10,11)  → 4
(1,4,8,9,11)   → 4      (1,5,6,10,11)  → 6      (1,5,7,9,11)   → 7
(1,5,8,9,10)   → 8      (2,3,7,10,11)  → 10     (2,3,8,9,11)   → 9
(2,4,6,10,11)  → 4      (2,4,7,9,11)   → 4      (2,4,8,9,10)   → 4
(2,5,6,9,11)   → 6      (2,6,7,8,10)   → 7      (4,5,6,7,11)   → 6
(4,5,6,8,10)   → 6      (4,5,7,8,9)    → 7
```

The only novelty versus “gap 2 if present” is that `(2,3,8,9,11)` charges
offset 9 (gap 1, h=1-incompatible: `t'=t−2` is S) instead of its gap-2 S at
offset 11. HARD charges offset 4, which Lemma 1 shows is never a φ7 image.

Because every value of `c` is an S-offset of that type, `φ11(t)=t−c(τ(t))`
lands in `N_t`. Because the chosen S is allowed, it is not a φ7 image, so
the image lies in `D \ φ7(U7)`. (U7-incompatibility is by integer identities
against the forced window, hence wrap-safe, as in Lemma 1.)

## Lemma 5 (injectivity of φ11). `PROVED-PAPER`

If `φ11(t)=φ11(t')` then `t−t' ≡ c(τ(t))−c(τ(t')) (mod p)`.

If `c(τ(t))=c(τ(t'))`, then `t≡t'`. Several types share a charged offset
(`4`, `6`, `7`, or `10`); they still recover a unique source from the image.

If `c≠c'`, the two length-11 windows sit at relative shift `c'−c`. Their
forced signs (12 positions each) either conflict on Z, or the overlap
destroys min-lag 11 for at least one type. This is a finite check on the 17
types. The naive gap-2 assignment left 10 consistent Z-glues (including the
`p=14` pair). `SOLUTION0` leaves **0** consistent Z-glues: the CSP that produced it
rejected every remaining glue of allowed offsets.

For `p≥22`, `|c'−c|≤10`, so two windows of length 11 at that distance cannot
wrap around the period. The Z-obstruction is the cyclic obstruction.

For `1≤p≤21`, every ordered pair of types with distinct `c` was placed at the
unique residues identifying the charged S, forced signs were propagated
around the cycle, and free bits (always `≤10`) were exhausted. Result: 0
cyclic witnesses, 0 undecided placements. (Pairs with `t≡t'` because
`p` divides `c'−c` are a single addition phase, which cannot carry two
types.)

Therefore φ11 is injective for every `p≥1`. Combined with φ7 this gives
`|U7 ∪ U11min| ≤ |D|`.

The pairwise check is a complete enumeration of a finite combinatorial set,
not a period census and not a holdout sample. Reproduction:

```sh
python3 experiments/issue73_20260908/lag11_falsify_hard.py
python3 experiments/issue73_20260908/lag11_residual_charge.py
python3 experiments/issue73_20260908/lag11_repair_csp.py
python3 experiments/issue73_20260908/lag11_repair_allperiod.py
```

Script SHA-256 (as run):

| script | sha256 |
|---|---|
| `lag11_falsify_hard.py` | `05228c6d0a26a84015ba8409896eecf3566d0cbcb1320a8684ba9daa0ccc44fd` |
| `lag11_residual_charge.py` | `ef7d52dea43152f0e1668b501c578bd0e300b963830ea527278255c6d7ef26ad` |
| `lag11_repair_csp.py` | `f687be6acbc13f585fd349869fd65db0cbd09f0403c260f271cb52cf1b93ab65` |
| `lag11_repair_allperiod.py` | `3bf579a2598ee608ca7fbc8ca5275ec53438e4d3849f2c5b674ca9042a8d39aa` |

Regression: `SOLUTION0` on all words `p=1..14` assigned 1691 min-lag-11 events,
0 collisions, 0 images in φ7(U7). Packing and wrap tests produced no empty
HARD residual.

## Failed attempts

1. Exact gap 2 as the U7-disjoint class. Six types have no such S. Among the
   eleven that do, unique-option types `(2,3,8,9,11)` and `(4,5,7,8,9)`
   collide on `ASSSASSAAAASSA`.
2. Allow exact gaps outside `{1,3}`. HARD still has none. Every exact gap
   `≥4` is a lag-3 image, so those charges land in φ7(U7).
3. Last-S look-ahead “charge gap 2 when `t+1` is S”. Types with `h≥2` have
   last-S gap `≥3`, so they never acquire a last-S gap 2. HARD often has
   `t+1=t+2=A` (514 of 1559 positive-sum occurrences through `p=18`), and
   then last-S is the lag-3 image.
4. Prefer gap 2, else the smallest U7-incompatible offset. Recovers the same
   `p=14` collision because it still charges `(2,3,8,9,11)` to 11.
5. Oldest-S, second-moment, escape selector, all-A future debt: not revived.

## Remaining uncertainty

- The repaired map is a finite table. It is not a following-gap class and it
  is not visibly the same rule at lag 15, 19, …. A Lean statement should be
  the count `|U7 ∪ U11min| ≤ |D|` with a semantic bridge from actual windows
  to the 17-row map, not an opaque matching oracle.
- Pairwise Z-incompatibility of `SOLUTION0` was machine-enumerated. A human
  can recheck any one pair in the same way as Gate 3's three short types; the
  argument does not hide a leftover infinite family.
- `H_extend` (flexible residual Hall after φ7, without a uniform rule) is
  implied for the subclass `U11min` by the injection, and remains unproved
  for min-lag `≥15`.
- No Recamán freshness, reachability, or canonical-orbit hypothesis is used.
  No claim about surjectivity or about E-067/E-070.

## Next decision

Do **not** start a lag-15 following-gap classification. That is the same
stopped proof class.

Formalize Lemma 4–5 only if an auditor accepts the finite pairwise
obstruction as a paper case analysis. The Lean target is
`|U7 ∪ U11min| ≤ |D|` for every cyclic word.

Reopen the lag-by-lag class only if a **new invariant** appears that is not
another lag: a common charge for all `d≡3 (mod 4)` (for example “an S in the
minimal window that no shorter φ-map can occupy”, abstracted off the 17-row
table), or a closed-form all-L potential. A second repair of gap-classes, or
a larger type list, is not a reopen.

Changed files (this unit):

- `docs/data/issue73_20260908/lag11/paper_attempt.md` (this note)
- `experiments/issue73_20260908/lag11_falsify_hard.py`
- `experiments/issue73_20260908/lag11_residual_charge.py`
- `experiments/issue73_20260908/lag11_repair_csp.py`
- `experiments/issue73_20260908/lag11_repair_allperiod.py`
- `docs/data/issue73_20260908/lag11/falsify_hard.txt`

Read but not owned: `lag11_classify.py`, `lag11_hard_type.py`,
`lag11_hard_incompat.py`, `lag11_safe_charge.py`, and their existing outputs.
`hard_type.txt` was not clobbered.
