# Epoch report: where the periodic supply capacity is tight (2026-09-11)

Handoff document for one research epoch. It is not the status source of truth;
[`CURRENT_FRONTIER.md`](CURRENT_FRONTIER.md) and
[`EVIDENCE_REGISTRY.tsv`](EVIDENCE_REGISTRY.tsv) are.

## Conclusion first

The capacity inequality `|U| ≤ |D|` (E-070) was measured at its boundary rather than
pushed to a wider class. Three facts came out, and one natural strengthening died.

1. **The inequality is sharp at every period.** For every `p` there is a positive-sum
   word of period `p` with `|U| = |D|`, and the largest `|D|` attaining equality grows
   with `p` (6 by period 20), so sharpness is not an artefact of nearly-all-A words.
2. **The tight words lie entirely inside the class E-128 already proves.** Every minimal
   supply window of every tight word has `ssCount ≤ 1`. Across periods 8..31 there is not
   one tight word with a high-SS window. So the part of E-070 where equality lives is
   already a theorem, and the entire remaining content of E-070 is the strict case.
3. **On the tight words the charge is forced.** The bipartite graph sending each supplied
   addition to the subtractions inside its own minimal window has exactly **one** perfect
   matching on every tight word — 336 tight words, 1,110 edges, unique every time — and
   that forced matching is exactly the oldest-S rule of E-069, the rule that is `REFUTED`
   as a general charge.

Fact 3 settles the long-running question of why every named charge failed. The oldest-S
map is not a bad guess; it is the only possible charge wherever the inequality is tight.
It is refuted only on words that carry slack, where its collisions cost nothing. **No
selector search can succeed and none was ever going to**: the selector is determined where
it matters and irrelevant where it is wrong.

The natural way to turn this into a proof — pay one spare subtraction per collision — is
false. `slack ≥ c` fails at period 18 on `AAAASSAAAASAAASSSS` (`|U|=6`, `|D|=7`, collision
excess `c=2`, slack `1`) and again at period 21. The accounting has to be sublinear in the
collision count.

What replaces it is local and testable: **every high-SS window donates a deletable
subtraction from inside itself** (T6). In every word carrying such a window, every such
window can give up one of its own subtractions and the matching still saturates. That is
the statement a Lean proof should consume, and it is the next gate.

## What was measured

All claims are about free periodic sign words. No Recamán reachability, freshness,
NoSAAS or minimal-lag hypothesis enters any of them. Enumeration is over necklace
representatives, which is lossless because `|U|`, `|D|` and `ssCount` are rotation
invariant.

| Quantity | Range | Result |
|---|---|---|
| `\|U\| > \|D\|` (E-070 violation) | all positive-sum words, `p ≤ 31` | none |
| `U = A` (E-067 violation) | all positive-sum words, `p ≤ 31` | none |
| `\|U\| = \|D\|` attained | every `p` in range | yes |
| tight word with a high-SS window | `p ≤ 31` | none |
| local Hall matching saturates `U` | `p ≤ 31` | always |
| perfect matchings on a tight word | `p ≤ 22` | exactly 1, always |
| forced matching equals oldest-S | 1,110 forced edges | 1,110 |
| oldest position of a tight word's window is an S | 1,110 forced edges | 1,110 |
| `slack ≥ collision excess` | `p ≤ 24` | fails at `p=18` and `p=21` |
| high-SS window donates a deletable S | `p ≤ 22` | always, for every such window |
| net surplus from gluing tight blocks | 627,264 pairs, 6,751,269 triples, periods ≤ 40 | none |

Previous horizons for comparison: E-066 checked the strengthened `|U| ≤ |D|` to period 16
and the supply falsifier to period 18; E-081 checked `U = A` to period 22; the Hall gate
H-20260907-09 checked the matching to period 18. Extending a horizon does not by itself
promote a label, and nothing here is promoted on that basis. The label changes earned are
the `REFUTED` row for `slack ≥ c`, which is carried by an exhibited word, and the
formalisation of the scan bound below.

## What was formalised

Every computational search in this branch terminates its backward scan by a drift
argument: for a fixed start the backward partial sums satisfy `g(l) = g(l-p) + σ`, so the
minimum over all `l ≥ 1` equals the minimum over `1 ≤ l ≤ p`, and once the running sum
passes `1 - Gmin` no longer lag can bring it back to 1. That criterion had never been in
Lean, which meant every "this phase has no supplier at any lag" claim rested on an
unverified C++ loop. `Recaman/PeriodicSupplyBound.lean` proves it, and derives the lag
bound `d ≤ p(p+1)` from the positive period mass alone. A claim of the form "phase `t` of
this periodic word has no P2 supplier" is now a finite kernel-checkable statement.

## Controls and cross-checks

- The probe recounts the positive-sum words of period 19..22 and reproduces E-081's
  recorded 3,487,066 exactly; it aborts on any mismatch.
- The all-A word and `A^{p-1}S` are positive controls for tightness and both come out
  tight. Dropping the moment equation would make every phase of `AA` supplied with `D`
  empty; the checker distinguishes that.
- Both counterwords to `slack ≥ c` were re-derived by direct summation in an independent
  Python implementation (`verify_counterword.py`) sharing no code with the C++ probe.
- Discovery was `p ≤ 22`; `p = 23..31` was frozen before execution and run unrepaired.

## What this does not show

- E-070 and E-067 are still `CONJECTURED`. Nothing here proves either, and the absence of
  a counterexample through period 31 is not a theorem.
- Surjectivity and non-surjectivity are untouched. The E-065 reduction only makes E-067
  exclude eventually periodic exact continuations; variable-length and aperiodic block
  schemes remain open regardless.
- T2 says the tight words are inside E-128's class. It does **not** say E-128 plus a
  slack argument proves E-070; the slack argument is exactly what is missing.
- The seam-pumping search is targeted, not exhaustive, above period 31. It rules out one
  specific refutation route, not refutation.

## Next gate

Prove T6 for the smallest high-SS shape: a minimal P2 window with `ssCount` exactly 2.
The inputs that did not exist when E-128 was proved are now available — the leading-run
bounds E-166 (`SS=2` leading run in `{0,1,3}`) and E-169 (`a ≤ ssCount+1`), the SS-gap
theorems E-155/E-170/E-172, and the endpoint repetition budget E-131 whose `m = 1` case
is exactly "two windows sharing an endpoint force `ssCount ≥ 2`" — which is the converse
direction of the collision-to-high-SS link this epoch measured.

Do not restart a named selector. Do not extend the period horizon as a unit of work.
