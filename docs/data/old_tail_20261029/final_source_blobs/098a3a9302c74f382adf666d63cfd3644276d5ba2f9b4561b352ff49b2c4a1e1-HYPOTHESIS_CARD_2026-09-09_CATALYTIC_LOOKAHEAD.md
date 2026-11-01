# Hypothesis card: bounded catalytic lookahead potential

**Conclusion:** 一回の減算を先読みするF_1も、二回へ修理したF_2も、L=11のS辺で反証された。
候補二つは `REFUTED`（E-089）、今回のbounded-lookahead探索は `STOPPED`。
全lag容量E-070、供給不足E-067、任意の固定kの可否は未解決のままである。

- ID: `H-20260909-02`
- Owner: Codex (four roles sequentially)
- Created: 2026-09-09
- Status: `REFUTED` for k=1,2; this bounded-lookahead attempt `STOPPED`
- Branch: issue #73, new statistic gate after E-088
- Base revision: `8dfbfb8f15eb2ff3d84629385cde99cd9f2bc9aa`

## Exact bounded question

For every window length L≥1 and word w∈{A,S}^L, let T_b(w) append b and
discard the oldest sign. Let c(w,A)=1 when some P2 lag 1≤d≤L supplies w,
and 0 otherwise; c(w,S)=−1. P2 has the unchanged signed-sum 1 and weighted-sum 0.
Windows in this card's concrete examples are newest-first; continuations are forward.

Let R_k(w) be the maximum total charge over all finite future words containing
at most k occurrences of S. The empty continuation is allowed. Set F_k(w)=−R_k(w).
The frozen primary candidate is **k=1**, independent of L. The question is

```text
∀ L≥1, ∀ w∈{A,S}^L, ∀ b∈{A,S}, F_1(w)+c(w,b) ≤ F_1(T_b(w)).
```

This is a uniform finite formula, not the least full-automaton potential:

```text
h_r(w) = Σ(j=0..r−1) c(T_A^j(w), A)
R_0(w) = h_L(w)
R_k(w) = max(R_0(w), max(0≤r≤L) [h_r(w)−1+R_(k−1)(T_S(T_A^r(w)))]) .
```

After L consecutive A steps the window is all-A, with no supply, and further
A steps leave it unchanged. Thus every A block can be shortened to length≤L
without changing the score. This proves the finite formula and finiteness of R_k.

## Why this is distinct and useful

E-075 refuted R_0: an S can create two later all-A supplies. That statistic is
a negative control only. R_1 includes one intervening catalytic S and charges
its cost, addressing the recorded L=11 mixed continuation `AASAAA`.
It does not embed the Lean7 table, choose offsets by lag type, or search over
unrestricted future words. Letting k be unbounded would return to the original
unproved capacity problem; that is explicitly outside acceptance.

Dependency chain before any Lean implementation:

1. The formula equals the at-most-k-S optimization (A-block saturation).
2. Prepending A preserves the allowed family, hence
   `R_k(w) ≥ c(w,A)+R_k(T_A(w))` for every k.
3. The **weakest new lemma** is `R_1(T_S(w)) ≤ R_1(w)+1` for all L,w.
4. Then F_1 is a potential; telescope on every cyclic word, for arbitrary L.
5. Choose L covering the finite supply lags of a periodic word: E-070, then E-067.
   No implication to Recamán surjectivity/non-surjectivity is claimed.

## Frozen falsification and stopping rules

- Boundary controls: all-A/all-S at L=3,7; unchanged P2 checked by direct signed sums.
- Negative control: drop the moment condition on all-A. Its supplied A self-loop
  admits unbounded harvest, contradicting a finite potential. The shortening
  argument above then fails because the all-A self-loop has positive charge.
- Existing gates: L=11 windows `SSAAAAAASSS` on A and `AAASAASSSSS` on S;
  catalytic seed `AASSSSAAASS`; E-075's oldest-first `SSSAAAA`.
- Weakened history: all binary windows, with no actual-orbit reachability assumed.
- Discovery: all edges at L=3,7,11, stopping after the first failing width.
- Conditional holdout for this candidate: L=15,19, stopping after the first failing width.
  These are already-used windows for different properties, not new trajectory data.
- One permitted repair, frozen now: k=2, only if k=1 fails because a future S
  needs an additional catalytic S. Test the same schedule. No k=3 search and no L>19.
- A finite pass is `COMPUTED`, not a theorem. If no proof emerges and only finite
  certificates remain, stop without promoting the all-L statement.
- Counterexamples must include exact maximizing continuations and direct P2
  lag/sum/moment traces, checked by a separate string-based enumeration.

## Roles, acceptance, and scope

Proposer freezes the formula above. Falsifier executes the fixed cases and
schedule. Formalizer records the finite formula / A-step argument on paper
and does no Lean implementation before the S lemma survives. Auditor checks
the counterexample's quantifiers and distinction from a positive periodic cycle.

Accept a complete all-L proof, or an exact counterexample and `REFUTED` candidate.
If the single repair also fails, mark this bounded-lookahead class `STOPPED`.
Do not infer that all fixed k fail without a quantified argument.

## Evidence and decision

The statement and protocol above were written before computation. No formula
or test range was changed after execution. The only repair was the predeclared k=2.

### Exact finite evidence (`COMPUTED`)

All runs use the base revision above plus the new working-tree scripts, whose
SHA-256 values are printed in the logs and frozen in the [bundle](data/issue73_20260909/README.md).

| Candidate | L=3 (8 states) | L=7 (128 states) | L=11 (2,048 states) |
|---|---|---|---|
| F_1 | A failures 0 / S failures 0 | 0 / 0 | 0 / 21 |
| F_2 | A failures 0 / S failures 0 | 0 / 0 | 0 / 10 |

The candidate F_1 repairs E-075's `AAAASSS --S--> SAAAASS` (newest-first):
R_1 goes 1→2, so the S inequality is tight. It also passes both named L=11
gates: R_1 is 3→2 on `SSAAAAAASSS --A--> ASSAAAAAASS`, and 0→1 on
`AAASAASSSSS --S--> SAAASAASSSS`. Thus the new statistic passed the
specific reopening gates before its new failure was found.

### Counterexamples (`REFUTED`, E-089)

| k | Before window w | After T_S(w) | Exact R_k(w) → R_k(T_S(w)) |
|---|---|---|---|
| 1 | `SASSSAASSSS` | `SSASSSAASSS` | 1 → 3 |
| 2 | `AAASAASSSSS` | `SAAASAASSSS` | 0 → 2 |

In both cases the necessary S-bound permits an increase of at most 1 but the
increase is 2. Equivalently F_k falls by 2 on an edge whose cost is only −1.

For k=1, from the **after** window, forward continuation `AAAASAAA` has four
supplied additions at steps 3,4,6,8, with lags 3,11,7,3 and one S at step 5.
Its net charge is 4−1=3. For k=2, the after-window continuation `SAAAASAAA`
has four supplied additions at steps 3,4,7,9, with lags 11,3,7,3 and two S
steps, for net charge 2. Every stated lag has exact sum 1 and weighted sum 0.

Upper bounds matter: a profitable continuation alone does not determine R_k.
The independent verifier enumerates every future with at most k S letters
and each A block of length 0..11. There are 156 continuations per window for
k=1 and 1,884 for k=2. The A-block saturation argument proves this includes
a score-equivalent representative of every allowed finite continuation.
Both upper bounds and both maximizing witnesses agree with the table formula.
The verifier imports no discovery code and uses positive-position counts and
sums instead of signed bit accumulators.

### What caused the failure

From the k=1 before-window, `SAAAASAAA` uses two S letters and scores 2,
strictly above R_1=1. From the k=2 before-window, `SSAAAASAAA` uses three S
letters and scores 1, strictly above R_2=0. These are explicit witnesses;
R_3 was not searched or asserted to be exactly 1.

The distinction is structural: bounding the number of future S steps misses
successive reactivations of old supply. The repaired k=2 formula even fails
the previously named `AAASAASSSSS` gate, which k=1 had passed.

### Paper formalizer and semantic auditor

`PROVED-PAPER` auxiliary facts, not a new frontier theorem: the finite A-block
formula and the all-k A-step inequality follow from the saturation and
prepending arguments above. For any fixed L,k, the remaining S inequality
holds at every window iff R_(k+1)=R_k at every window. One direction follows
by prepending S. In the other, if all S inequalities hold, the A inequalities
already proved give a telescoping upper bound of R_k(w) for every future
score, because the terminal R_k is nonnegative. Hence R_(k+1)≤R_k; the
reverse inequality is inclusion of the admissible future families.

The counterexamples are finite sign-window potential failures. Neither is a
positive-score periodic cycle, a counterexample to E-070, or a reachable
Recamán-orbit counterexample. The candidate quantified over all binary windows,
so no reachability assumption is missing from these refutations. No claim is
made that every fixed k fails, that no other potential exists, or that the
known lag-11/15 capacity theorems fail.

### Handoff and next decision

- Hypothesis status: F_1 and F_2 `REFUTED`; tested route `STOPPED`.
- Commands: `PYTHONDONTWRITEBYTECODE=1 python3 experiments/issue73_20260909/catalytic_lookahead.py --k 1`,
  the same command with `--k 2`, and
  `PYTHONDONTWRITEBYTECODE=1 python3 experiments/issue73_20260909/verify_catalytic_witnesses.py`.
- Strongest evidence: exhaustive upper bounds independently verified, plus
  exact signed-sum/moment continuation traces; no Lean claim was added.
- Changed files: this card, two experiment scripts, frozen output bundle,
  E-089 registry entry and corresponding frontier/proof-map/portfolio notes.
- L=15,19 holdout was not run because discovery failed. No larger lag,
  period census, or k=3 repair was performed.
- Next decision: stop increasing the lookahead count. Reopen only with a
  structural invariant that handles repeated catalytic S steps without an
  arbitrary fixed count. Defining unrestricted optimal future profit alone
  would repackage the open capacity problem and is not acceptance.
