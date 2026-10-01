# Minimal P2 windows: a sharp terminal-A budget

2026-10-01. Evidence `E-361`: **PROVED-PAPER**, not checked in Lean.
Hypothesis card: [H-20261001-01](HYPOTHESIS_CARD_2026-10-01_TERMINAL_A_BUDGET.md).

Follow-up 2026-10-01: section 3 alone is formalized in
`Recaman/FirstP2EndingS.lean` as E-362, including the least-index corollary.
Sections 2 and 4 (all-length terminal-A SS bounds) are now formalized in
`Recaman/TerminalASSBound.lean` as E-363, including maximum-run semantics.
The all-q witnesses below remain `PROVED-PAPER`.
Independent-session semantic review of the new Lean result is pending.
Historical pre-formalization statements below describe the original E-361 pass.

For every minimal P2 word, the number t of A signs beyond its true oldest S
is at most `max(q-1,0)`, where q counts adjacent SS pairs with overlap.
The bound is attained for every q, including arbitrarily large q. Thus an
SS=2 minimal donor has only the two possibilities t=0 and t=1, independently
of its length. This is a local word theorem; it does not prove an owner-map
constraint, tight-set avoidance, Gate T6, or a statement about actual orbits.

## 1. Definitions and exact claims

Let `W=(e_1,...,e_L)` with each `e_i` in `{+1,-1}`, written newest first,
with A=+1 and S=-1. Set

```text
H_0 = M_0 = 0,
H_j = sum_{i=1}^j e_i,
M_j = sum_{i=1}^j i e_i.
```

These are `LeadingRunSupply.mass (W.take j)` and `moment (W.take j)`.
P2 means `H_L=1, M_L=0`. Minimal means that no `0<j<L` satisfies
`H_j=1, M_j=0`, exactly the exclusion tested by `hasP2Prefix`.
Let `q=ssCount W` (SSS contributes two), and let t be the maximal terminal
A-run length. A P2 word contains S: an all-A word of mass 1 would be A,
whose moment is 1. Thus `r=L-t` is its true oldest-S offset.

The claims, universally quantified over all finite words W, are:

1. P2 implies `t<=q`, without minimality.
2. Minimal P2 and `t>0` imply `t<q`. Equivalently, every minimal P2 word
   satisfies `t<=max(q-1,0)`.
3. For every integer q>=0 there is a minimal P2 word with exactly q SS pairs
   and `t=max(q-1,0)`.

No length bound, NoSAAS condition, periodicity, current-A sign, matching,
Hall hypothesis, or initial-0 history occurs in these claims.

## 2. Suffix mass and the non-strict bound

Consider a suffix beginning before the terminal A run. Its part preceding
that run ends S. If this preceding part has s S signs in b nonempty S runs,
it has exactly `s-b` adjacent SS pairs and at least `b-1` A signs. Hence its
mass is at least `-1-(s-b)`. Since `s-b<=q`, the complete suffix, including
the final t A signs, has mass at least `t-q-1`.

Suffixes wholly inside the terminal A run have positive mass. Therefore,
if `t>=q+1`, every nonempty suffix has nonnegative mass, and the last suffix
has mass 1. But

```text
M_L = sum_{j=0}^{L-1} mass(e_{j+1},...,e_L)
```

because e_i occurs in exactly i suffixes. This gives `M_L>0`, contradicting
P2. Consequently `t<=q`. The case t=0 needs no argument.

## 3. A prefix-mass ceiling forces the first P2 to end S

**Lemma.** Suppose `H_j<=2` for every `0<=j<=L`, and at least one nonempty
prefix is P2. The *first* P2 prefix ends S.

List in increasing order all times at which `H_j=1`. At the first such
time b, every `H_i` with `0<=i<b` is at most 0: an integer walk with unit
steps cannot pass above 0 without first reaching 1. Summation by parts gives

```text
M_b = b H_b - sum_{i=0}^{b-1} H_i >= b > 0.
```

For consecutive visits a<b to mass 1, summation by parts also gives

```text
M_b - M_a = sum_{i=a}^{b-1} (1-H_i).
```

There are exactly two kinds of excursion between consecutive visits:

- If the first step is A, the height becomes 2. The next step must be S
  by the height ceiling. Thus `b=a+2`, the excursion is AS, and the moment
  change is exactly -1. This visit ends S.
- If the first step is S, every intermediate height is at most 0; reaching
  2 would pass through 1 first. There is at least one intermediate time,
  so the displayed sum is strictly positive. This visit ends A.

The moment starts positive at the first visit to mass 1. It cannot become
negative before hitting zero: its only decreases are integer steps of -1.
Its first zero must therefore be reached by an upper AS excursion, which
ends S. This proves the lemma, including the existence and direction of
the first zero; no assumption of positive earlier moments was inserted.

## 4. Strict bound for minimal words

Suppose W is minimal P2, `t>0`, and `t>=q`. Every suffix beginning before
the terminal run has mass at least `t-q-1>=-1` by section 2. Suffixes inside
the run have positive mass, and the empty suffix has mass 0. Because the
total mass is 1, each prefix satisfies

```text
H_j = 1 - mass(e_{j+1},...,e_L) <= 2.
```

Section 3 says the first P2 prefix ends S. Minimality says the first P2
prefix is W itself, but `t>0` says W ends A. This contradiction proves
`t<q`. In particular, q=0 and q=1 force t=0, and q=2 forces t<=1.

## 5. Sharp witnesses at every SS count

For q=0,1,2 use respectively

| q | W | t | P2 prefix lengths |
|---:|---|---:|---|
| 0 | `AAS` | 0 | 3 |
| 1 | `SAAAASS` | 0 | 7 |
| 2 | `AAASSSASASA` | 1 | 11 |

Direct integer sums prove the table. For q>=3 set

```text
n = q^2 - 2q - 2 >= 1,
W_q = AAA S (SA)^n S^q A^(q-1).
```

There are `n+q+2` A signs and `n+q+1` S signs, so mass is 1. The initial S
followed by the first S of `(SA)^n` contributes one SS. The final `S^q`
contributes q-1, and all other joins contribute none. Thus `ssCount W_q=q`
and its terminal A run has length q-1.

To compute the moment, first omit `(SA)^n`. The base word
`AAA S^(q+1) A^(q-1)` has moment

```text
(2q+3)(q+2) - (q+1)(q+8) = q^2-2q-2.
```

Inserting SA immediately after the first S changes the moment by -1:
SA has mass 0 and local moment 1, and the suffix `S^q A^(q-1)` has mass -1
and is shifted by two positions. Repeating the insertion n times makes
the moment zero. Inserting additional SA pairs before this suffix has the
same effect because the other inserted pairs have mass zero.

To verify minimality, enumerate *all* proper visits to mass 1. The first
is position 1, with moment 1. At the S of the i-th SA pair, `1<=i<=n`,
the moment is `-i-2`; at the first S of `S^q`, it is `-n-3`.
After this the height decreases from 1 to `2-q`, then increases through
the terminal A run to 1 only at the last position. There are no other
proper visits to mass 1. None of the listed moments is zero, proving
minimality for every q>=3. The length is `2q^2-2q-1`.

This is an abstract word construction. It makes no assertion that W_q
occurs in a canonical or seeded Recaman orbit. It proves that a uniform
constant bound on t cannot follow from minimal P2 alone.

## 6. Semantic audit and boundary controls

- The offset interpretation is exact in both directions: maximal terminal
  A length t means offset `r=L-t` is S and all larger offsets through L
  are A. Conversely this true-oldest-S specification gives precisely that t.
- The t=0 exception is essential: `AAS` has q=t=0. Do not state `t<q`
  without `t>0`.
- Removing minimality fails at `AASASSA`: mass 1, moment 0, q=t=1, with
  P2 prefixes at 3 and 7. This also shows the non-strict bound is sometimes
  attained. The first P2 still ends S, as section 3 requires.
- Removing mass=1 fails at `ASSA`: moment 0, q=t=1, no P2 prefix.
  Removing moment=0 fails at `A`: mass 1, q=0, t=1, no proper P2 prefix.
- The ceiling 2 cannot be changed to 3 in section 3: `AAASSSASASA` has
  maximum prefix mass 3 and its only P2 prefix is the entire A-ended word.
  This is consistent with the known E-130 SS=2 obstruction.
- Both inequalities and witnesses refer to real words, not free integers
  satisfying the conclusion. Minimality is used only in section 4 and is
  explicitly proved for the witnesses in section 5.
- The proof is self-contained and does not consume the uncommitted H-05
  module or its downstream claims. The proposer, falsifier, proof writer,
  and semantic auditor were separate passes of one session; this is not
  an independent-agent or human review, and no Lean result is claimed.

## 7. Computation and its limits

`experiments/terminal_a_budget.py` was frozen with the hypothesis card before
the first run; [pre-run hashes](data/terminal_a_budget_20261001/PRE_RUN_SHA256SUMS)
and [frozen protocol](data/terminal_a_budget_20261001/protocol.frozen.md)
record that version. The base revision is
`08c08565c743f39350c9b959e1df7d30aa1cae5d`; the script is the new file whose
SHA-256 appears in each JSON log. Exact outputs:
[discovery](data/terminal_a_budget_20261001/discovery.json),
[holdout](data/terminal_a_budget_20261001/holdout.json).

Reproduce from the repository root:

```bash
shasum -a 256 -c docs/data/terminal_a_budget_20261001/PRE_RUN_SHA256SUMS
python3 experiments/terminal_a_budget.py discovery
python3 experiments/terminal_a_budget.py holdout
```

| Range | All P2 words | Minimal | Minimal A-ended | Violations of any tested claim |
|---|---:|---:|---:|---:|
| Discovery L=3,7,11,15,19 | 3,021 | 1,811 | 729 | 0 |
| Holdout L=23 | 30,554 | 18,556 | 7,895 | 0 |

Independent literal enumeration at L=0..11 checks all 4,095 binary words
and matches the filtered generator's complete set of 34 P2 words. The
generator is exhaustive: mass 1 fixes the A count `(L+1)/2`; moment zero
fixes the sum of their offsets `L(L+1)/4`. These imply `L=3 mod 4`, so
other lengths contain no P2 words. All arithmetic is integral.

Sharp witnesses q=0..10 (discovery) and q=11..40 (holdout) pass; the largest
has length 3,119 and t=39. All these facts are `COMPUTED`, not the proof.
The holdout is disjoint for this claim; length 23 was not an untouched
range of the repository as a whole. No mathematical repair or failed falsifier
run occurred. The deliberately weakened statements fail on the controls above.
The unrelated cold repository build was interrupted to reuse a matching
existing compiled certificate; the handoff records that validation history.

## 8. Consequence for the next research decision

For an owner window of length L with true-oldest offset r, the old A-tail
`t=L-r` is now bounded by `max(q-1,0)` under minimal P2. If the owned S has
offset kx and `delta=r-kx`, its full extent older than that S is exactly
`L-kx=delta+t`. The present result controls t only. It does **not** control
delta, produce owners, or establish M1/M2 for a family.

The bounded unit is complete at `PROVED-PAPER`. The next useful unit is to
formalize the first-P2-ending-S lemma and this strict bound, with the same
word quantifiers, or to propose a separate falsifiable inequality involving
delta. Do not infer general Gate T6, E-070/E-067, or surjectivity. Stop this
unit here; neither an expanded census nor the old lag-15 certificate route
is warranted by this result alone.
