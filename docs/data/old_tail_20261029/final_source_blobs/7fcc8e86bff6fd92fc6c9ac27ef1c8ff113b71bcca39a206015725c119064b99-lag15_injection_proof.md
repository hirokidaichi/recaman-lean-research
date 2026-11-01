# H-20260908-04: all-period lag-15 injection extending φ7 ∪ φ11

Status: `PROVED-PAPER`. Independent cyclic regression through period 18 is
`COMPUTED` and is not the proof. This is not E-067/E-070.

Base: `8b07f93fbbb17352c091cabaa333fc366a66c04f`.

## Conclusion

For every cyclic ±1 word, let U7, U11min, U15min be the addition phases whose
least P2 lag is at most 7, exactly 11, and exactly 15. There is an explicit
map φ15: U15min → D, depending only on the length-15 backward window, such
that

1. φ15(t) lies among the seven S-phases of that window,
2. φ15(U15min) is disjoint from φ7(U7) ∪ φ11(U11min),
3. φ15 is injective.

Together with the audited maps of E-071 and E-080,

```text
|U7 ∪ U11min ∪ U15min| ≤ |D|
```

holds for every period, with no period cutoff. A positive-sum E-070
counterword must therefore use a least supplier lag ≥ 19.

This is a 155-row type-to-offset table, not a closed form in the lag. It does
not decide Recamán surjectivity.

## Objects

P2 at lag d: Σ_{i=1}^d ε(t−i)=1 and Σ i ε(t−i)=0. Then d=2k+1 with k odd and
the k negative offsets in 1..d sum to d(d+1)/4. Least lags are 3, 7, 11, 15, …

φ7 (Gate 3 / E-071):

- min d=3, offsets {3}: φ7(t)=t−3
- min d=7, offsets {1,6,7}: φ7(t)=t−7
- min d=7, offsets {2,5,7}: φ7(t)=t−5

φ11 (E-080 CSP assignment): each of the 17 min-lag-11 types is sent to one
S-offset in {3,4,6,7,8,9,10} as in `lag11_verify_independent.CHOSEN`.

A min-lag-15 window is a 7-subset of {1..15} summing to 60 with no P2 prefix
of length 3, 7, or 11. There are 263 raw 7-subsets summing to 60 and exactly
155 minimal types (`COMPUTED` by enumeration of C(15,7), finite list, not a
period census).

An S-offset i of such a type is *blocked* if every U7 pattern at S=t−i and
every φ11 charge at S=t−i already contradicts a sign forced by the length-15
window. Unconstrained signs outside the window are treated as possibly
completing a pattern, so blocked is a sufficient local obstruction.

Every one of the 155 types has between 1 and 6 blocked offsets
(SAFE_COUNTS 1:1, 2:5, 3:36, 4:57, 5:49, 6:7; uncovered 0). This existence
was recorded by `lag15_probe.py` and recomputed by the CSP.

## Chosen charge

The complete CSP on blocked offsets, collision distance δ=j−i, returns a
pairwise Z-clash-free assignment. Search nodes=155 (unit propagation plus
one consistent path). Frozen table:

`docs/data/issue73_20260908/lag11/lag15_assignment.json`
(SHA-256 `6fb2baa40d96545266a1d11a1f1e1ac6f810d40e805cd5754f505945e7e1e1b4`).

Offset occupancy: 3:13, 4:11, 5:10, 6:24, 7:22, 8:16, 9:14, 10:6, 11:8,
12:10, 13:8, 14:8, 15:5.

Every chosen offset is an S of the type. The unique singleton type
(1,2,6,11,12,13,15) is charged at 15. Hand check at S=t−15:

- lag3: t′=t−12, but t−12 is S, not A
- lag7 h1: t′=t−8, needs S at t−9, but t−9 is A
- lag7 h2: t′=t−10, needs A at t−11, but t−11 is S

Type (5,6,7,8,9,10,15) charged at 7, S=t−7:

- lag3: t′=t−4, needs A at t−5, but t−5 is S
- lag7 h1: t′=t, needs S at t−1, but t−1 is A
- lag7 h2: t′=t−2, needs S at t−4, but t−4 is A

The remaining 153 types, all three U7 patterns, and all 17 φ11 charges are
the same local check, independently rebuilt by `lag15_verify.py`
(N_UNBLOCKED=0).

## Injectivity

φ15(t)=t−i_τ. Distinct t,s collide iff t−i ≡ s−j (mod p).

On Z, t−i=s−j iff s=t+(j−i). Placing the two length-15 windows at 0 and j−i
yields a sign contradiction for every ordered pair of distinct types under
the assignment (155×154=23,870 ordered pairs; 0 consistent merges). Same
type and same offset forces t=s.

Wrap: a circle identification x∼x+p can only add constraints to the Z-merge
of a pair or of the opposite pair. Because every ordered pair already clashes
on Z, no period makes the windows consistent. Thus injectivity is all-period.

Disjointness from φ7 and φ11 is the blocked-S property: a U7 or φ11 image at
the charged S would require a pattern that the length-15 window forbids.

## Semantic audit

- Informal injection ⇒ |U7 ∪ U11min ∪ U15min| ≤ |D|.
- The count does not imply U≠A (lag ≥ 19 remains).
- Formalising the 155-row table by `decide` would be another finite vector
  and is not claimed.
- No freshness or Recamán reachability.
- Collision distance is δ=j−i, the same convention that repaired E-080.

## Evidence

- Finite types and blocked offsets: `experiments/issue73_20260908/lag15_csp.py`
  (SHA-256 `6dc17781f5f60dde592bc34a80d3d0dcb5e735d0ce9c36c42382009e17354e0b`).
- Independent rebuild of types, U7/φ11 blocks, and pairwise Z-clashes:
  `lag15_verify.py` PASS, OPEN_COLLISION_PAIRS=0
  (SHA-256 `107541755cfbba55f4690aa04c00fc2264b85a40b8ac31d92edb75390faa7166`).
- Cyclic regression, all 524,286 words of periods 1..18, 20,621 lag-15 events
  and 36,915 lag-11 events: φ7, φ11, φ15 injective and pairwise image-disjoint.
  `COMPUTED` confirmation of the proof map, not its justification.

## Next

Do not enumerate min-lag-19 types as a completion. The method is a CSP table
at each lag, not a uniform charge. Remaining Lean edge: glue actual periodic
windows onto the 17 lag-11 types (E-079 → E-080). Reopen lag-by-lag only for
a d-independent obstruction.
