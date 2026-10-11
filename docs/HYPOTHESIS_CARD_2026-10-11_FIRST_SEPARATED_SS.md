# Hypothesis card: first separated SS-run endpoint

- ID: `H-20261011-02`
- Base: research branch `codex/research-plan-20261003`, E-368/E-370 context, commit `167d07df424b85217010935934bd583d8995af23`
- Created: 2026-10-11
- Status: `CONJECTURED`; finite checks `COMPUTED`; weakened-history failure `REFUTED`
- Scope: periodic sign streams, not an actual Recamán orbit

## Exact candidate

For every `p>0` and `p`-periodic `e : ℤ → {A,S}` with positive period mass and no cyclic chronological `SAAS`, take two **phase-distinct current-A** sources whose **minimal positive P2** windows have SS count exactly 2, the same true-oldest S phase `s`, and whose two SS edges lie in separate chronological runs. Lift the common oldest S to an integer clock `s` in the shared core `C` of `W_A=C A`, `W_S=X C`. Let `q>s` be the chronological first S of the earlier of the two SS pairs of `C`. Candidate: `phase_p(q) ≠ phase_p(s)` and `phase_p(q) ∉ E_low`, where

`E_low = {phase_p(t-d) | e(t)=A, d>0, P2(past e t d), SS(past e t d)≤1, e(t-d)=S}`.

All positive lags and **all** eligible endpoints are included. Together with E-368's oldest-S exclusion, this candidate would supply two distinct phases outside `E_low`, hence the single-pair local capacity. It is stronger than Hall and could fail even if Hall holds. Period wrap must be checked explicitly; the constructed examples have `p` larger than both donor lags, and do not test it.

## Falsification gate and limits

Acceptance for a refutation: one complete periodic donor pair satisfying **all** quantified conditions with `q=s mod p` or with a current-A lowSS S-ended P2 window at phase `q`. Acceptance for proof: a uniform chronological exclusion plus a separate phase-distinctness argument; finite survival is never proof. Test donor lags `11,15,19,23` using the previously classified `X` forms, with period `reverse(X C) AA`; recompute minimal P2 prefixes, cyclic NoSAAS, and q endpoints. Stop this pass after these lags or on a counterexample, with no adaptive bound extension. Cases at `d=11,15,19` were already seen in the earlier separated-existence search; `d=23` is an exploratory extension, **not a fresh holdout**.

## Exact finite results

Run `python3 experiments/separated_first_run_test.py > docs/data/ss2_separated_20261011/first_run_test.jsonl`. The script enumerates mass-zero, moment-`−d` cores `C` of length `d−1` with exactly two nonadjacent SS edges, tests minimal `C A` and `X C`, cyclic NoSAAS, then scans the first chronological SS-run start `q` against every possible endpoint lag (up to `p(p+1)`, with early stop once the second SS edge is included). Results:

| `d_A` | moment-compatible cores | split-SS cores | minimal `C A` | tested minimal pair constructions | NoSAAS pair constructions | `q∈E_low` |
|---:|---:|---:|---:|---:|---:|---:|
| 11 | 11 | 3 | 0 | 0 | 0 | 0 |
| 15 | 112 | 18 | 4 | 4 | 1 | 0 |
| 19 | 1210 | 63 | 13 | 26 | 2 | 0 |
| 23 | 13894 | 157 | 36 | 36 | 4 | 0 |

Each `X` choice is a separate construction, so the pair count can exceed the number of cores. The `d_A=15,19,23` checked examples include the p45/57/69 witnesses. The seven NoSAAS constructions have `q` at clocks 6, 8, or 10, strictly inside the period and distinct from `s=0`; **no general phase-separation theorem follows**. This is a finite structural probe, not exhaustive over arbitrary periods or all possible `X` outside the prior paper classification.

## Weakening control (exact countermodel)

The circular period `SSAAAASASSAAA` has positive mass 3 and cyclic NoSAAS. It has two separate SS pairs, at clocks `(0,1)` and `(8,9)`, yet the first pair's start `q=0` is the endpoint of a current-A lowSS P2 window: current clock 7, lag 7, newest-first word `SAAAASS` (mass 1, moment 0, SS count 1, S-ended). Thus **NoSAAS plus separated SS pairs alone cannot prove the q-exclusion**. This control lacks the stipulated same-oldest *minimal P2 donor pair*; it is not a counterexample to the candidate. Computed weakening probes of the `C` construction also yielded no endpoint under the other weakened conditions through donor lag 23, but this 13-letter countermodel demonstrates that some donor geometry must enter a proof.

## Decision

The fixed-local-phase candidate remains `CONJECTURED`. A viable proof must analyze a putative lowSS endpoint at `q` with current strictly before the second SS pair, then use the P2 moment/minimality of both donors to contradict it; it must separately rule out `q=s mod p` in wrapping periods. Resume only with such a structural lemma or a full-premise counterexample. Do not register a new `PROVED-PAPER` or `PROVED-LEAN` claim from the seven finite successes.
