# Hypothesis card: a protected subtraction for arbitrarily long sharp windows

- ID: `H-20260909-06`
- Owner: Codex, proposer / falsifier / formalizer / auditor sequentially
- Created: 2026-09-09, within the one-hour research run
- Status: `PROVED-LEAN` (general periodic extension); concrete L=11/15 instantiations `PROVED-PAPER`
- Base revision: `8dfbfb8f15eb2ff3d84629385cde99cd9f2bc9aa`

## Exact bounded question

For every p≥1 and p-periodic e:Z→{A,S}, let D be its S phases and
U_L its A phases having a P2 lag 1≤d≤L. Assume an injection ψ:U_L→D
with backward offsets 1..L, and ψ(t)=t−3 modulo p whenever P2(t,3).
Let Q_L be the A phases t for which some m≥max(3,L+1) has
the preceding m signs all A and P2(t,4m−1).

Is `|U_L|+|Q_L|≤|D|`, uniformly over m, p, and L?
The proposed extension assigns Q_L to q=t−m−2 modulo p.
This is an infinite-lag subclass, not the all-lag capacity E-070.

## Dependency chain / weakest useful new lemma

H-03 gives d≥4m−1 and a sharp family. H-04's S-block consequence
gives S at offsets m+1..2m−1. H-05 prevents two sharp supplies in
one A run. Thus q is S and Q_L's assignment is injective.
Any short supply assigned to q must lie at q+j, 1≤j≤L; all of its
past of length≤L consists of two runs A^a S^b. The only P2 two-run
word is AAS, which lies at j=4 and is assigned to q+1, not q.
The weakest new lemma is this protected-S disjointness, not a new type table.

## Frozen falsifier

- Arbitrary sign windows, no freshness, recurrence, positive sum, or reachability.
- Generate every sharp partition word for L=11 and L=15.
- Discovery m=L+1..L+4; conditional holdout m=L+5..24.
- At every offset j=1..L from q, enumerate all P2 lags 1..L when
  the current sign is A. The only possible pair must be (j,d)=(4,3).
- Negative controls: m=4 or 5 with L=11, sharpFamily past plus a short
  continuation, can collide with the existing lag-11 charge at q.
  This tests necessity of a size restriction, not optimality of L+1.
- No permitted repair. Stop if a protected-S collision appears, or
  periodic lifting or injectivity requires an unstated history assumption.
- Acceptance: complete general paper proof, plus Lean for the local
  ingredients if feasible. Finite agreement alone does not pass.

## Evidence, semantic audit, and decision

### Complete paper proof

Use integer representatives of phases. For t∈Q_L, choose m as in the
definition and q=t−m−2. The sharp S-block theorem gives S on
`[t−2m+1,t−m−1]=[q−m+3,q+1]`; all signs on `[q+2,t]` are A, including t.
In particular q is S. The sign at t−m−1 is S, so m is the unique length
of the preceding A run. Hence the charge is well-defined. This also
prevents m from wrapping arbitrarily around a period containing an S.

**Injectivity on Q_L.** Suppose two charges agree modulo p. Shift one
source, its window, and its charge by an integer multiple of p so that
the charges agree as integers. P2 and all sign conditions are invariant
under this shift. `sharp_charge_injective` then makes the two lifted
source times equal. Their original phases are equal. Equivalently, if
the run lengths were m<n, the times would differ by k=n−m A steps;
the lags 4m−1 and 4n−1 would differ by exactly 4k, contradicting H-05.

**Disjointness from ψ(U_L).** Suppose ψ(u)=q modulo p. By locality,
ψ(u)=u−j with 1≤j≤L; lift u so that u=q+j. If j=1 the current sign
is S, contradicting u∈U_L. For j≥2 every past window of length d≤L
is inside `[q−L+2,q+L−1]`. Because m≥L+1, this interval consists of
S up to q+1 and A from q+2 onward. The window therefore has the form
A^a S^b. Its mass and moment equations force a=2,b=1 (`p2_two_runs`).
Consequently j=4,d=3, and the lag-3 convention charges u to u−3=q+1.
This cannot equal q modulo p: this configuration contains both S and A,
so p≠1. In the Lean version the local offset is chosen to be exactly 3
at a lag-3 source. This represents the same phase map and is always
allowed: a nonempty U_L implies L≥3. The theorem
`sharp_short_mod_disjoint` shifts the entire short window before applying
`sharp_protected_charge`, so the proof does not silently discard wraparound.

Thus the two injective images are disjoint subsets of D, proving
`|U_L|+|Q_L|≤|D|`. The source sets also are disjoint: a Q_L phase has
at least L preceding A signs, so every window of length≤L is all-A
and cannot satisfy P2.

**Instantiation.** The existing φ7∪φ11 map of E-080 uses offsets≤11 and
uses offset 3 at lag 3. Therefore, at every period,

```text
|U≤11| + |Q with m≥12 and lag 4m−1| ≤ |D|.
```

The paper map φ7∪φ11∪φ15 of E-086 has the same convention and offsets≤15,
so the corresponding bound holds with U≤15 and m≥16. Its new lags start
at 63 and are unbounded. These claims do not cover arbitrary non-sharp
windows of lag≥19. Neither E-067 nor E-070 is proved.

The new class is nonempty: periodically repeat a block consisting of the
newest-first sharpFamily(m) and the current A. Its length is 4m and total
signed sum is 2; the chosen phase belongs to Q_L whenever m≥max(3,L+1).
This is a sign-word witness, not a claim of Recamán reachability.

### Evidence and semantic audit

`PROVED-LEAN`: `sharp_protected_contact`, `sharp_protected_charge`,
`sharp_charge_injective`, and the stream S-block/gap lemmas are included
in the repository audit. The subsequent `Recaman.SharpPeriodicSupply`
module proves the modulo-p injection, S image, disjointness, and
**`periodic_capacity_extension`**, the general finite cardinality theorem.

The theorem quantifies over any duplicate-free lists U and Q of phase
representatives in 0..p−1. U has an assumed short injection into S with
offset≤L and the lag-3 convention; each member of Q carries its actual
sharp P2 window and run length. It constructs Q's injection and proves
`U.length+Q.length≤D.length`. Enumerating the whole U_L and Q_L gives
the intended statement. No capacity or injection for Q is assumed.
The Lean theorem is slightly stronger because it does not require the
current Q sign to be A; the intended Q_L is a subset of that domain.

**The concrete applications to the existing φ7/φ11/φ15 definitions remain
paper instantiations.** The general extension has been formalized, not
the 155-row lag-15 table. Final audit: 1,265 declarations, all permitted
dependencies. This distinction is recorded separately as E-095 versus E-093.

`COMPUTED`: every partition word passes at L=11,m=12..24 and L=15,m=16..24.
Each word has exactly the contact (j,d)=(4,3) among the tested short
sources, and no collision at q. The m=4,5 negative controls produce the
existing min-lag-11 type {1,2,9,10,11}, whose charge is 10 in
`Recaman/LagElevenSupply.lean`; their images equal q exactly.

```sh
PYTHONDONTWRITEBYTECODE=1 python3 experiments/issue73_20260909/sharp_capacity_extension.py
./scripts/check.sh
```

Exact output: [sharp_capacity_extension.txt](data/issue73_20260909/sharp_capacity_extension.txt).
No period census, type-table extension, or reachability assumption entered
the proof. **Decision: retain this uniform infinite-subclass extension.
The remaining formal obligation is instantiating the existing short maps;
the remaining research obligation is how to include non-sharp windows.**
