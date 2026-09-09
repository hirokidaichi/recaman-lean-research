# H-20260908-01: all-period lag-11 injection extending U7

Status: `PROVED-PAPER` (pending Lean). Independent cyclic regression through
period 18 is `COMPUTED` and is not the proof.

Base: `8b07f93fbbb17352c091cabaa333fc366a66c04f`.

## Conclusion

For every cyclic ±1 word, let U7 be the addition phases with a P2 lag at most 7
and let U11min be those whose least P2 lag is exactly 11. There is an explicit
map φ11: U11min → D, depending only on the length-11 backward window, such that

1. φ11(t) lies among the five S-phases of that window,
2. φ11(U11min) is disjoint from the image of the audited U7 injection φ7,
3. φ11 is injective.

Consequently |U7 ∪ U11min| ≤ |D| for every period, with no period cutoff.
A positive-sum E-070 counterword must therefore use a least supplier lag ≥ 15.

This is not E-067/E-070, and not an all-lag charge. The method is the finite
type list plus local incompatibility with the three U7 patterns; it extends
in principle to the next lag 15, which is a separate unit.

## Objects

P2 at lag d: Σ_{i=1}^d ε(t−i)=1 and Σ i ε(t−i)=0. Then d=2k+1 with k odd and
the k negative offsets in 1..d sum to d(d+1)/4. Least lags are 3,7,11,15,...

The U7 injection (Gate 3, independently audited):

- min d=3, offsets {3}: φ7(t)=t−3 (following gap ≥ 4)
- min d=7, offsets {1,6,7}: φ7(t)=t−7 (following gap = 1)
- min d=7, offsets {2,5,7}: φ7(t)=t−5 (following gap = 3)

There are 29 five-subsets of {1..11} summing to 33. Exactly 17 have no P2
prefix of length 3 or 7; these are all possible types of a min-lag-11 window.

## Chosen charge

Each type is assigned an S-offset that is U7-incompatible: each of the three
U7 patterns, placed at the unique candidate t′ determined by the target S,
already contradicts a sign forced by the length-11 window. Because a U7 image
at S can only arise from t′ ∈ {S+3, S+5, S+7} (one candidate per rule, even
on a cycle), this obstruction is all-period.

CSP assignment (offset after the type):

```text
(1,2,9,10,11)→10  (1,3,8,10,11)→3   (1,4,7,10,11)→4
(1,4,8,9,11)→4    (1,5,6,10,11)→6   (1,5,7,9,11)→7
(1,5,8,9,10)→8    (2,3,7,10,11)→10  (2,3,8,9,11)→9
(2,4,6,10,11)→4   (2,4,7,9,11)→4    (2,4,8,9,10)→4
(2,5,6,9,11)→6    (2,6,7,8,10)→7    (4,5,6,7,11)→6
(4,5,6,8,10)→6    (4,5,7,8,9)→7
```

Every chosen offset is at least 3, so the whole lag-3 pattern at S sits inside
the window. Lag-7 patterns that stick into the future still fail on a forced
past sign.

Hand check of HARD=(1,4,7,10,11) at offset 4, S=t−4:

- lag3: t′=t−1, but t−1 is S, not A
- lag7 h1: t′=t+3, needs S at t−3, but t−3 is A
- lag7 h2: t′=t+1, needs S at t−6, but t−6 is A

## Injectivity

φ11(t)=t−i_τ. Distinct t,s collide iff t−i ≡ s−j (mod p).

On Z, t−i=s−j iff s=t+(j−i). Placing the two length-11 windows at 0 and j−i
yields a sign contradiction for every ordered pair of distinct types under
the assignment above (272 ordered pairs; 0 consistent merges). Same type and
same offset forces t=s.

A wrap t−i=s−j±p reduces to the opposite ordered pair: the overlapping signs
after identifying x∼x+p are independent of p and are already among the
ordered-pair checks. Thus injectivity is all-period.

## Semantic audit

- Informal injection ⇒ |U7 ∪ U11min| ≤ |D|.
- The count does not imply U≠A (lag ≥ 15 remains).
- No freshness or Recamán reachability.
- The first offset choice (preferring gap 2) failed cyclic regression on
  `SSSASSAAAASSAAA` (p=15, two lag-11 phases both mapping to phase 2). That
  assignment used the wrong collision distance δ=i−j. The CSP assignment
  uses δ=j−i and is the statement being claimed.

## Evidence

- Finite types, U7-incompatibility, CSP assignment, pairwise Z-merge:
  `experiments/issue73_20260908/lag11_*.py`
- Independent recomputation of U7 conflicts and pairwise merges: PASS
- Cyclic regression, all 229,045 positive words of periods 1..18, 26,586
  lag-11 events: injective and disjoint from φ7. `COMPUTED` regression of
  the proof map, not its justification.
- HARD census on the same words: 1,559 occurrences, empty residual 0,
  residual size 4 or 5, and the only taken HARD S is offset 1 via lag3.

## Next

Formalize the count in Lean by `decide` on the 17 types and 272 pairs, with
a semantic bridge from actual periodic signs. Then test whether the same
incompatibility method assigns lag-15 types against φ7∪φ11; if some type has
no remaining S, stop lag-by-lag.
