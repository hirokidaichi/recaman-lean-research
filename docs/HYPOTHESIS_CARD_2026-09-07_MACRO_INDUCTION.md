# Hypothesis card: fixed-block regeneration and the missing positive-drift case

- ID: `H-20260907-07`
- Owner: macro-induction parallel research worker
- Created: 2026-09-07
- Initial status: `CONJECTURED`
- Source revision: `612fcfaf74bfb49f3ae05a268057c82f70dcca26`
- Research branch: pattern 4, macro/block induction; no Lean implementation in this pass

## Exact question fixed before experimentation

Let `N` be a natural clock, let a finite seed history `F` of natural numbers
contain a current value `x_N`, and let
`x_(n+1) = x_n - (n+1)` iff that candidate is positive and absent from
`F union {x_(N+1),...,x_n}`, with addition otherwise. Is its sign sequence
**never eventually periodic**? Precisely, for every such exact finite-history
continuation, every `M >= N`, every `p > 0`, some `n >= M` has
`sign(n+p) != sign(n)`.

This is the first gate for a fixed finite-block regeneration family. The existing
periodic candidate no-go handles nonpositive period sign sum when the candidate
has a fixed floor; it leaves positive sign sum and quadratic divergence. We test
whether actual blocker supply excludes that remaining case. A variable-length,
aperiodic macro family is outside the claim.

Acceptance: either a complete new paper argument including all three sign-sum
cases, or an exact finite-phase counterexample to the proposed supply obstruction,
or a precise unresolved inequality and a stop decision. A finite census alone
will not be promoted to a theorem. No new interface or finite trace acceleration
counts as mathematical progress.

Stop: if the positive-drift blocker supply condition admits a periodic word not
excluded by subtraction freshness, or if reduction to bounded blocker lag needs
unproved global reachability. One repair at most, by adding exact subtraction
freshness rather than changing period bounds.

## Provenance and known obstructions

- `PeriodicCandidateNoGo` and `PERIODIC_CANDIDATE_NOGO_2026-09-01.md`: balanced
  candidate drift sum `-p^2` is PROVED-LEAN; asymptotic three-case argument is
  PROVED-PAPER. Positive sign sum is explicitly left open by that arithmetic.
- E-049: terminal survival can leave an initial 5/4 phase before its residue budget
  and wrap in a later 4/3 phase. A run formula alone does not transport history.
- E-050: phase capacity plus affine clock/value and level correction is no-go for
  exact seeded continuations. Do not repeat this potential class.
- E-056: arbitrary finite-prefix inclusion and density/range/parity do not rescue
  local survival. No claim here identifies arbitrary finite seeds with canonical
  initial-0 reachability.
- Chaffin's primary computation account describes ping-pong sections as two
  intervals, ending at stale lower landing or fresh lower opportunity. It supports
  the need to transport membership facts, not an infinite block induction proof:
  https://benchaffin.com/recaman/recaman.html

## Falsification plan

- Small cases: period 1, both signs; balanced period 2; local `SAAA` forced third
  addition as a positive control for internally supplied blockers.
- Weakened history: arbitrary finite seed is allowed, making any proved no-go
  stronger than a canonical-only claim. Infinite preload is a negative control.
- Discovery: exhaustive sign words with lengths 1 through 12, exact integer
  conditions for fixed-lag blockers; no canonical trajectory scan.
- Frozen holdout: lengths 13 through 18 after the candidate condition is fixed.
  These are new finite-word checks for this protocol, not an unused canonical
  trajectory range. They corroborate algebra only.
- Before any Lean implementation: extract the exact lag condition and either
  prove the all-period combinatorial lemma or mark it unresolved.

## Four roles

Proposer fixes the finite-block question above. Falsifier enumerates signatures
and tests weakened histories. Formalizer writes a paper dependency chain only.
Auditor checks quantifiers, finite-history dependence, and separates this no-go
from non-surjectivity. Status and exact evidence will be appended after results.

## Exact positive-drift reduction (PROVED-PAPER, independently audited)

Use `epsilon_t in {-1,+1}` for the step **into** clock `t`, so
`x_t-x_(t-1)=epsilon_t*t`. Let `p>0` be an eventual period and
`S=sum_(r=1)^p epsilon_r>0`. For each clock residue class there are constants
`b_r,c_r` with

```
x_n = A*n^2 + b_r*n + c_r,     A=S/(2p)>0,   r=n mod p.
```

The finitely many original seed values and all values before the eventual-period
start cannot block `x_(t-1)-t` for arbitrarily
large `t`, because that candidate tends to infinity. For a post-seed supplier
`j=t-1-d`, the difference equation is

```
x_(t-1) - x_(t-1-d) = t.                              (P1)
```

If `|b_r|<=B` and `|c_r|<=C`, putting `n=t-1` gives

```
n+1 >= (A*d-B)*(n+j)-2C.
```

For sufficiently large `n` with `n>=max(1,2C+1)` and nonnegative `j`,
`n+1+2C<=2n`, so this bounds
`d <= (B+2)/A`. Thus every supplier has one of finitely many lags. This is an
asymptotic finite bound, not a supplied-history hypothesis.

For a fixed phase and lag, expanding P1 yields

```
t * sum_(i=1)^d epsilon_(t-i)
  - sum_(i=1)^d i*epsilon_(t-i) = t.
```

An affine equation either holds identically or at most once. Since the number
of phases and allowable lags is finite, **every addition phase must have a lag**
with the exact word conditions

```
sum_(i=1)^d epsilon_(t-i) = 1,
sum_(i=1)^d i*epsilon_(t-i) = 0.                       (P2)
```

The implementation numbers backward offsets by `k-1`, and tests
`sum epsilon=1` and `sum (k-1)*epsilon=-1`; adding the first sum proves exactly
P2. No sign convention discrepancy is present.

A word-only bound follows: write `d=q*p+r`, `0<=r<p`. Then
`1=q*S+s_r` with `s_r>=-r`, hence `q<=p`, so `d<=p*(p+1)-1`.
The checker includes the slightly larger endpoint `p*(p+1)` for simplicity.

### The remaining finite-word lemma

For every nonempty periodic sign word with positive sign sum, is there an
addition phase `epsilon_t=+1` for which no `1<=d<=p*(p+1)` satisfies P2?

If yes, this excludes positive-drift periodic **exact finite-history**
continuations. The finite computation tests this lemma directly. It is
strictly stronger than the existing balanced candidate-drift lemma, but it
is not yet proved merely because tested periods pass.

### Other sign sums

`S<0` makes every phase tend to negative infinity and contradicts nonnegative
values. For `S=0`, the one-period value drift `D_r` depends on phase and has
`sum_r D_r=0`, while adjacent drifts differ by `p*epsilon_r`. Thus they are
not all zero and one is negative, again contradicting nonnegative values.
This is the value-walk counterpart of the existing candidate drift proof;
it does not need a positive candidate floor.

## Second bounded gate: a concrete matching map (frozen before its check)

Requested follow-up, at most ten minutes. For a positive-sum periodic word, let
`U` be addition phases admitting P2 and let `D` be subtraction phases. The exact
strengthening is `|U|<=|D|` (`CONJECTURED`). It implies the original existence of
an unsupported addition phase since `|A|>|D|`.

Fix one proposed injection, without assuming it: for `t in U`, choose the least
positive supplier lag `d_t` satisfying P2. Among the subtraction positions in
that backward interval, choose the **oldest**, i.e. the largest offset
`i<=d_t` with `epsilon_(t-i)=-1`, and map to phase `(t-i) mod p`.
The interval contains a subtraction because its signed first moment is zero.

Acceptance: prove this concrete map injective, or produce two distinct supplied
addition phases with the same image and record their exact minimal lags and
moment sums. Stop this map if a collision is found; no replacement injection is
automatically assumed. A bipartite matching test on all S phases in the intervals
may diagnose whether the map alone or the whole interval domain failed, but is
not an all-period Hall theorem.

## Results and evidence levels

The useful new result is the **PROVED-PAPER finite-lag reduction P1 -> P2**,
independently checked by the joint-generation and entry-barrier workers. The
full eventual-periodicity exclusion and `|U|<=|D|` remain **CONJECTURED**.
A fixed finite-block induction is therefore not yet proved impossible in full,
and this pass supplies no invariant for variable-length blocks.

| Evidence | Status | Exact outcome |
|---|---|---|
| Positive drift -> bounded suppliers -> P2 in every A phase | `PROVED-PAPER` | Proof above uses only finite past history, eventual periodicity, and the exact rule; no future freshness assumption |
| All positive-sum words, periods 1..12 | `COMPUTED` | 3,458 words; no word supplies every A phase |
| Frozen periods 13..18 | `COMPUTED` | 225,587 words; no word supplies every A phase |
| Strengthening `supplied A <= S`, periods 1..16 | `COMPUTED` | 56,747 words; zero violations; diagnostic chosen after the first census, not a second holdout |
| Longest-A-run start selection | `REFUTED` | `SSAAAASAAAAA`, phase 7, lag 7 |
| Longest-S-run/lexicographic start selection | `REFUTED` | `SSSASASAAAA`, phase 3, lag 47 |
| Max full-period first moment selection | `REFUTED` | `AASASASAASAAAASSS`, phase 7, lag 27; deterministic random discovery preserved as `OBSERVED` |
| Minimum-lag oldest-S injection | `REFUTED` | `SSSSAAAASAAA`: phases 7 and 11 both map to phase 8, at minimal lags 11 and 3 |
| Continue that particular injection proof | `STOPPED` | It fails the predeclared collision gate |

The last collision has exact suffixes (newest first):

```
t=7, d=11:  A A A S S S S A A A S   sum=1, first moment=0
t=11,d=3:   A A S                   sum=1, first moment=0
```

The full minimal-lag subtraction domains in that word are
`6->{3}`, `7->{0,1,2,3,8}`, `9->{2,3,8}`, `11->{8}`. They admit the matching
`6->3, 7->0, 9->2, 11->8`. Thus the concrete oldest-S choice fails, while this
counterexample does **not** refute the Hall condition for the whole domains.
Do not silently promote that finite alternative matching into a general map.

## Reproduction and exact outputs

All commands run from the repository root; source revision is frozen above.
Each exact log embeds the executing script's SHA-256. No canonical trajectory
range is designated unused or held out here.

```sh
python3 experiments/parallel20260907/macro_periodic_supply.py --min-period 1 --max-period 12 > docs/data/parallel20260907/macro_periodic_discovery.txt
python3 experiments/parallel20260907/macro_periodic_supply.py --min-period 13 --max-period 18 > docs/data/parallel20260907/macro_periodic_holdout.txt
PYTHONDONTWRITEBYTECODE=1 python3 experiments/parallel20260907/macro_witness_controls.py > docs/data/parallel20260907/macro_witness_controls.txt
PYTHONDONTWRITEBYTECODE=1 python3 experiments/parallel20260907/macro_phase_count.py --max-period 16 > docs/data/parallel20260907/macro_phase_count.txt
PYTHONDONTWRITEBYTECODE=1 python3 experiments/parallel20260907/macro_matching_map.py > docs/data/parallel20260907/macro_matching_map.txt
```

Owned changes: this card; the four `experiments/parallel20260907/macro_*.py`
scripts; corresponding five exact-output logs and `macro_manifest.txt` under
`docs/data/parallel20260907/`. No Lean module, shared frontier/registry, GitHub
issue, commit, or user visualizer files were changed by this worker.

## Semantic audit and decision

- The reduction is a necessary condition only. A word satisfying P2 everywhere
  need not realize an exact finite-history continuation; subtraction freshness
  and chronology can still fail. This stronger obstruction was not needed by
  the current census and must not be dropped from the eventual main claim.
- The source exception is finite: seed values **and the entire preperiod**.
  An infinite preload could block arbitrarily large candidates and invalidate
  the finite-lag proof; it is deliberately outside the quantifiers.
- The local `SAAA` identity supplies one A phase at lag 3, so no assertion says
  every A phase is unsupported. It is also a sharp example for `|U|<=|D|`.
- E-049 and E-050 are not bypassed: no phase survival is transported and no
  affine capacity is claimed. E-056's finite, parameter-dependent run family
  remains allowed; eventual periodicity is an additional global restriction.
- Chaffin's finite run compression is not an infinite recurrence theorem.
- Non-surjectivity is **not** proved or made conditional on P2. The direct use
  is to select against eventual fixed sign-block proofs if the finite-word
  lemma is proved. Variable-length or genuinely aperiodic regeneration remains
  available and requires a separate full-history invariant.
- Next question: prove or refute the Hall condition for the minimal P2-lag
  subtraction domains (hence `|U|<=|D|`), without assuming an injective producer
  map. A combinatorial counterword is as useful as a proof. Do not spend another
  unit merely extending the period horizon.
- Priority: this is a precise, bounded theorem opportunity and a structural
  filter for pattern 4. Its distance to an actual permanent missing value is
  still substantial; proof tractability alone must not be sold as a direct
  non-surjectivity route.
