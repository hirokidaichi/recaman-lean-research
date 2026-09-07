# Issue 73: independent macro proof attempt

- Base revision: `b4b5afaaac126acaa0c4fc0042bdaa4fafd289a1`
- Scope: main word obstruction `U != A`, or strong count `|U| <= |D|`.
- Four roles are sequential: propose a precise proof input, falsify before using
  it, write only complete paper arguments, audit quantifiers and dependency.
- No Lean, old evidence bundle, shared maps, issue metadata, or Git mutation.

## Gate 1 fixed before new computation: the finite-word form

For a finite sign word `e_0,...,e_(L-1)`, call an index `t` supplied if `e_t=+1`
and there is `1<=d<=t` such that

```
sum_(i=1)^d e_(t-i)=1,
sum_(i=1)^d i*e_(t-i)=0.
```

Proposed stronger-looking lemma: the number of supplied indices is at most the
number of negative indices. There is no periodicity, positive drift, or supplied
history hypothesis. We will not assume the count; we seek a paper charge or an
explicit finite word violating it. No repeating shortest-lag Hall experiment is
run here (the parent owns that independent falsifier).

The finite lemma would imply the periodic count: repeat a period K times. Every
periodic supplied phase is supplied after at most `p*(p+1)` boundary positions,
so `K*|U|-O(p^2) <= K*|D|`; let K grow. Conversely, a finite violating word
can be completed by sufficiently many positive signs to have positive sign sum;
all its supplied indices remain supplied and no new negative index is added.
Thus it would give a positive periodic counterword to the strong count. This is
an equivalent count formulation, not by itself a new frontier result.

Boundary controls: all-positive words supply nothing; `SAAA` supplies its last
A and has one S, so constant one is sharp. Infinite initial preload is irrelevant:
this gate is exclusively exact coefficient identities, not actual history.

Acceptance: a complete argument for a concrete charge, or a counterexample
which identifies the invalid step. Stop a proposed charge immediately on a
collision. A new period cutoff alone is not a result.

## Gate 2 fixed before its falsifier: minimum-lag endpoint

A prospective simplification of the interval proof is: whenever a finite backward
word first attains `(sign sum, first moment)=(1,0)` at offset d, its final sign
is negative. If true, the oldest negative in a minimum-lag interval is exactly
the oldest position; if false, the counterexample stops this simplification.

Frozen check: enumerate finite backward words of lengths d=3,7,11,15,19,23,
by choosing `(d-1)/2` negative positions. Other d are excluded arithmetically:
`d=2k+1` and `sum negative positions=d(d+1)/4` force k odd, so d=3 mod4.
Stop at the first earliest-P2 word ending positive. Discovery lengths through15;
larger lengths are conditional frozen corroboration only if no earlier failure.
No trajectory or word-period horizon claim is made by this local signature test.

## Gate 3: an all-period injection for the short-lag subclass

**Claim (paper proof before regression, pending independent audit):** for any
cyclic sign word, let U7 be its A phases with some P2 lag d<=7. Then
`|U7|<=|D|`. No positive sign sum is needed. This is a limited all-period
statement; the full count remains unproved.

Let `s_l` be the most recent S before a supplied A at `t=s_l+h`, h>=1.
Index S occurrences bi-infinitely, with gaps `delta_l=s_(l+1)-s_l>=1`.
If D is empty there is no supply. Otherwise the cyclic S indexing is well-defined.
P2 gives d=2k+1 with k odd, so d<=7 means d=3 or d=7.

1. If minimal d=3, the backward pattern is AAS and h=3. Charge to S_l.
   Its following gap satisfies delta_l>=4 because t=s_l+3 is A.
2. If minimal d=7, there are exactly three S in that window. Put
   c=delta_(l-1), b=delta_(l-2). The moment equation is
   `3h+2c+b=14`; oldest-S inclusion gives `h+b+c<=7`.
   Since b,c>=1, h<=3. If h=3, the last three signs AAS give d=3,
   contrary to minimality. Hence h is 1 or 2.
   - h=1 gives `2c+b=11`, `b+c<=6`, so c=5,b=1. Charge to S_(l-2),
     whose following gap is exactly 1.
   - h=2 gives `2c+b=8`, `b+c<=5`, so c=3,b=2. Charge to S_(l-1),
     whose following gap is exactly 3.

The three image classes have following gaps >=4, 1, and 3, hence are disjoint.
Within each class, h is fixed and the S-index shift is fixed (0, -2, -1).
Equal image phases imply equal last-S phases, hence equal t phases. This proves
injectivity modulo the word period even if a length-7 interval wraps around the
period more than once. The proof is independent of the numeric period size.

**Falsifier frozen now:** exhaust words with periods1..14, including nonpositive
sums, and check each shortest d<=7, the gap classification and image injection.
Then deterministic random words periods15..80, 100 words each, seed7307.
These are regression controls for the explicit proof map, not new untouched
trajectory or word holdout ranges. Include all-A/all-S and periods shorter than
7. Stop and retract this proof on any mismatch.

**Consumer:** a positive-sum counterword with U=A must contain a supplied A whose
minimal P2 lag is at least11. This narrows the proof class; it does not settle
U!=A, and no deduction about actual non-surjectivity is asserted.

## Gate 4: second-moment sign does not give a primitive rank

A possible continuation of the short-lag proof is that every *minimal* P2 suffix
has negative second moment. That holds for the three short patterns and for the
positive-ending endpoint counterexample, but it must not be assumed. Freeze the
single boundary word `AAASSASSSAA` (newest-first), with S offsets
4,5,7,8,9, and explicitly check its first two moments, second moment, and shorter
P2 prefixes. Acceptance is a decisive counterexample or confirmation of this
one word only. A finite sign pattern never substitutes for an all-period proof.

Paper calculation: its S offsets sum to33 and their squares sum to235, while
`1+...+11=66` and `1^2+...+11^2=506`. Therefore its sign sum is1, first moment0,
and second moment `506-2*235=36>0`. The only possible shorter P2 lags are3 and7;
their pairs are `(3,6)` and `(1,-4)`, so11 is minimal. This disproves the proposed
strict-negative second-moment rank. `AAS` has second moment-4, so there is no
uniform sign at minimal P2 suffixes. The main count is untouched.

## Gate 5 fixed before its test: all-addition continuation debt

A concrete all-horizon potential candidate avoids selecting a supplier S.
For a length-L history word w, define F_L(w) to be the number of supplied A
steps, with P2 lag<=L, among the next L steps if all those steps are A.
After L further A steps no S remains, so later A steps cannot be supplied.

The A-transition identity is exact:
`F_L(next_A(w))=F_L(w)-supplied_L(w)`.
The only proposed new inequality is
`F_L(next_S(w))<=F_L(w)+1`.
If it holds, `P=-F_L` is a bounded all-period potential and proves the count.
This is a concrete formula (no maximization over arbitrary continuations).

Frozen falsifier: exhaust binary histories for L=3,7,11,15 in that order; stop at
the first violation of the S inequality. On failure, save the offending history,
both exact future all-A traces and counts. This kills only this explicit debt,
not the unknown possibility of a different all-L potential.

## Stable conclusions and evidence

1. **PROVED-PAPER:** Gate3, `|U7|<=|D|` for every cyclic sign word, with an
   explicit injection into each phase's actual minimum-lag S domain. Therefore
   the Hall condition holds for every subset of U7 as well. Independent proof
   reconstruction and the quotient-by-number-of-S argument are recorded in
   `short_lag_independent_audit.md` by a different worker. The parent owns any
   Lean implementation; this worker added no Lean source.
2. **COMPUTED:** the explicit injection passed all32,766 binary words of periods
   1..14, covering29,938 supplied A events, and6,600 deterministic random words
   of periods15..80, covering21,795 supplied A events. These checks are regression
   evidence for the paper proof, not its justification.
3. **REFUTED / STOPPED:** minimum-lag endpoint-is-S, by newest-first
   `SAAASAASSSA`, d11. Negative offsets1,5,8,9,10; the oldest position11 is A;
   the first P2 hit is11. The shortest-lag interval cannot generally be trimmed
   by identifying its oldest position with its oldest S.
4. **REFUTED / STOPPED:** uniformly negative second moment at a minimal P2 lag,
   by `AAASSASSSAA`, d11, second moment+36. `AAS` gives-4. This scalar rank is
   unavailable; the main count remains unrefuted.
5. **REFUTED / STOPPED:** the explicit all-A future-demand potential. At L7,
   history `SSSAAAA` has F=0, while adding one S gives F=2, with future all-A
   supplied offsets1 and3. The exact A-transition identity survives; the needed
   S-edge one-unit bound fails. A new S can reactivate demand supported jointly
   with older S steps, so single-run prospective demand is not a sufficient
   inventory. The automaton potentials found by the parent are a different class.

The all-period main claim `U!=A` and strong claim `|U|<=|D|` remain
**CONJECTURED**. This pass does not prove them, and no periodic word violating
them was found here. It gives a proved short-lag boundary and three concrete
failures of proposed general proof mechanisms. The open part requires longer
lags; a positive-sum all-A-supplied counterword, if one exists, must have at least
one minimum lag>=11. That is a statement about a fixed-sign periodic proof class,
not about permanent absence of any Recaman value.

## Commands, hashes, and handoff

All runs use base `b4b5afaaac126acaa0c4fc0042bdaa4fafd289a1`; every output records
its script SHA-256. From the repository root:

```sh
python3 docs/data/issue73_20260907/macro_minimum_endpoint.py > docs/data/issue73_20260907/macro_minimum_endpoint.txt
python3 docs/data/issue73_20260907/macro_short_lag_injection.py > docs/data/issue73_20260907/macro_short_lag_injection.txt
python3 docs/data/issue73_20260907/macro_second_moment_control.py > docs/data/issue73_20260907/macro_second_moment_control.txt
python3 docs/data/issue73_20260907/macro_all_addition_debt.py > docs/data/issue73_20260907/macro_all_addition_debt.txt
```

Owned changes are this note and the four uniquely prefixed scripts and outputs
above, plus `macro_manifest.txt`. No old hashed bundle, shared card/maps, Lean,
GitHub metadata, Git state, or user visualizer was changed. The next decision is
whether the parent's all-lag Hall/automaton work supplies a general mechanism;
otherwise stop these failed mechanisms and retain the audited short-lag lemma.
No further period-only enumeration is recommended as a substitute for that input.

## Gate 6: fixed short-lag map extension to minimum lag11

H_extend (frozen before this pass): for every positive-sum cyclic sign word,
retain the audited U7 injection exactly, delete its image S phases from each
minimum-lag11 row's S-domain, and ask whether these remaining domains satisfy
Hall. This is a statement about extending that particular injection; flexible
full-domain matching and the count |U11|<=|D| are weaker statements.

The proof map is fixed: lag3 -> last S; lag7 h1 -> second preceding S;
lag7 h2 -> preceding S. For every minimal-lag11 phase t the original domain is
all distinct S phases at offsets1..11. The conditional claim asks for an injective
choice among the remaining domains, with all U7 assignments unchanged.

Frozen discovery: all positive-sum words of periods1..12 in lexicographic S/A
order. Conditional corroboration: periods13..18 only if discovery has no failure.
This tests a new map-extension property on word ranges used previously; it is
not an untouched word-data holdout. Stop at the first failure. Independently
recalculate that word's lag equations and every original/residual domain, exhaust
Hall subsets for a deficiency witness, and test flexible matching on all U11
rows. Do not repair the map or claim failure of U11 capacity from extension failure.

### Gate6 outcome

**COMPUTED:** no H_extend failure in the frozen pass. Discovery periods1..12
checked3,458 positive words and287 minimal-lag11 rows. Conditional periods13..18
checked225,587 positive words and26,299 such rows. In total,229,045 words and
26,586 long rows admitted matching after keeping every audited U7 assignment fixed.
The residual domains contained95,234 phase incidences in total.

A separate verifier rebuilt every domain using the negative-offset count and
moment identity rather than incremental signed sums. It checked all229,045 words,
every short-map image, and all residual matching witnesses for membership,
injectivity, and completeness. All passed. This verifies the exact finite result;
it does not promote H_extend to an all-period theorem or establish full P2 Hall.
No failure occurred, so no counterexample, forced rerouting example, or repair is
reported. The conditional range is a new-property regression on old word ranges,
not an untouched-data holdout.

Reproduction:

```sh
python3 docs/data/issue73_20260907/macro_extension.py --min-period 1 --max-period 12 > docs/data/issue73_20260907/macro_extension_discovery.txt
python3 docs/data/issue73_20260907/macro_extension.py --min-period 13 --max-period 18 > docs/data/issue73_20260907/macro_extension_conditional.txt
PYTHONDONTWRITEBYTECODE=1 python3 docs/data/issue73_20260907/macro_extension_verify.py > docs/data/issue73_20260907/macro_extension_verify.txt
```

H_extend remains **CONJECTURED**, supported here only by the finite check. The
next mathematical question is whether the classified lag11 residual domains
have a uniform matching while this short map is fixed. This bounded diagnostic
has completed; an additional word-period extension is not its next gate.
