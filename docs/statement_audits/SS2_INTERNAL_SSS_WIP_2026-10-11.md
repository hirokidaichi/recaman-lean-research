# Provisional statement and meaning audit: internal SSS endpoint lemma

Historical draft, superseded by [E-372](E-372.md) and its independent audit.
The R/W/C/T role names in this draft are nonstandard; use the standard
real-content/wrapper/conditional/tautology classification in the final audit.

2026-10-11. Formalizer self-audit of `Recaman/SS2InternalSSS.lean` on draft PR #90. **Compiler, full check, and independent review pending.** This document does not register a `PROVED-LEAN` claim or promote E-370. If the module passes Lean, a separate independent audit and the standard `E-NNN.md` G5 statement audit are still required before a new evidence row.

## Exact signatures (verbatim from the proposed source)

```lean
theorem ssCount_append_SSS (w : List Bool) :
    2 ≤ ssCount (w ++ [false, false, false])
```

```lean
theorem internal_sss_ne_lowSS_endpoint
    (e : Int → Bool) (q t : Int) (l : Nat)
    (hq0 : e q = false) (hq1 : e (q + 1) = false)
    (hq2 : e (q + 2) = false)
    (htP : P2 (past e t l))
    (htss : ssCount (past e t l) ≤ 1)
    (hend : t - (l : Int) = q) : False
```

```lean
theorem internal_sss_phase_ne_lowSS_endpoint
    (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (q : Int)
    (hq0 : e q = false) (hq1 : e (q + 1) = false)
    (hq2 : e (q + 2) = false)
    (t : Int) (l : Nat)
    (htP : P2 (past e t l))
    (htss : ssCount (past e t l) ≤ 1) :
    endpointPhase p t l ≠ phase p q
```

The signatures quantify over the **actual** integer-clock sign stream and window `past e t l`. `P2` is the established mass-one/moment-zero predicate and `ssCount` counts overlapping adjacent S pairs. `endpointPhase p t l` is `phase p (t-l)`. The theorem does not bind a donor window `past e u d`, an `oldestOffset`, or a finite lowSS family. It is therefore only a local input to E-370, never a formalization of the collision-pair inequality.

## Meaning and proof obligations

1. The list lemma counts two distinct overlapping SS edges in an explicit SSS suffix. Its proof uses `OnePerRun.ssCount_append` and the exact count of the suffix.
2. The integer lemma derives `l≥3` from real `P2 (past e t l)`. If the endpoint is `q`, `past_append` places `[false,false,false]` at the oldest end of the actual candidate window. The suffix-count lemma contradicts `htss≤1`. `htP` and `htss` are independent ordinary source predicates; neither is a defined abbreviation for the conclusion. The proof does not assume the endpoint exclusion.
3. The phase lemma lifts congruence to an integer period shift with `SharpPeriodicSupply.lift_equal_mod`, transports the *same actual* P2/SS facts by `past_shift`, and applies the integer contradiction. There is no period-mass assumption, lag bound or assumed Hall condition.

The lemmas omit current-A. Their conclusion remains valid for any P2 current, so this is a genuine strengthening of the requested current-A endpoint exclusion. They also omit NoSAAS and donor minimality: those are needed elsewhere in E-370's collision classification, not in this first-clock fact. No claim is made for the case `q=s` of the full collision pair: the local lemma excludes only `phase(q)=phase(s)` there and does not produce two phases.

## Counterfactual/negative checks for independent review

- A word ending `SSS` has two overlapping SS edges, including when the triple wraps in a periodic representation. The proof must count edges in the lifted integer window, never from a period-limited bitset.
- If the candidate endpoint is `q` and lag is 1 or 2, a P2 window cannot exist; `p2_length_ge_three` discharges those lengths. For lag≥3, dropping `htss≤1` should admit a P2 candidate endpoint in some larger history (find a concrete example before final audit if one is needed).
- With only `SS` at `q,q+1`, the count is one. Replacing the SSS hypothesis by SS must invalidate this proof.
- `p=1` makes a periodic SSS stream all S and thus has no P2 window; the theorem's all-period wording includes this vacuous boundary. Use p22/p33 frozen models as nonempty larger-period controls.
- Circular NoSAAS-negative p33 and the `q=s` p32 model do not refute this standalone implication. They test later collision branches.
- The new theorem's conclusion is disjointness from the set of **S-ended endpoints**, not disjointness from every S phase in an original lowSS window. E-368 normalizes lowSS endpoint images; the full two-phase capacity step must prove both donor S phases are in the concrete donor neighborhood and outside that image.

## R/W/C/T scope table

| Role | This module establishes | Still needed for E-370 |
|---|---|---|
| R (real-stream fact) | Exact actual SSS signs and actual P2/SS≤1 window produce an integer-clock contradiction. | Derive the single-SSS geometry from the two actual minimal donor windows, not from a stand-in hypothesis. |
| W (window/period transport) | A periodic endpoint-phase equality moves the *same* window to the SSS first clock. | Show the second excluded phase is an actual S in a donor window and distinct from the true oldest phase, including wraparound. |
| C (capacity) | None. | Apply E-368's concrete lowSS image and count it together with two distinct excluded donor phases inside `N(L∪{v,w})`. |
| T (target/orbit) | None. | E-070/E-067 and surjectivity remain separate. |

## Commands/evidence at drafting

- `python3 scripts/harness_gate.py --lint-module Recaman/SS2InternalSSS.lean` on an isolated copy: **3/3 SUBSTANTIVE** (heuristic only).
- GitHub draft PR #90 CI: **pending at this drafting point**. No local Lean/lake/elan executable is available.
- Final audit must rerun `./scripts/check.sh`, inspect `#print axioms` output, add meaningful Lean controls, and independently read the final exact source. Never infer kernel acceptance from this static audit.
