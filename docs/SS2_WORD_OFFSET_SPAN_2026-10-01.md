# Fixed SS=2 does not bound word offset span

Evidence E-365 retains its historical `PROVED-PAPER` label. The complete
all-k Lean proof and independent audit are now E-367; see
[Lean handoff](RESEARCH_HANDOFF_2026-10-01_SS2_WORD_OFFSET_SPAN_LEAN.md).
Card H-20261001-05 records the original paper unit, separate from E-364.

Even under minimal P2, SS=2, NoSAAS, a current A and terminal A length zero,
the distance from a marked S to the true oldest S can be arbitrarily large.
The marked S below is the newest S, not an owner supplied by a tight Hall
family. Consequently this is a no-go for a word-only constant-distance
argument, not a counterexample to an owner-family bound or to #73.

## Exact family

Use newest-first A=+1, S=-1 and one-based offsets. For every Nat k set

```text
C = SAAASSAAASS,
V_k = (SA)^k C (AS)^(3k),
H_k = A V_k.                  -- explicit current A
```

V_k is P2 and has no positive proper P2 prefix. It has exactly two
overlapping SS pairs, H_k has no SAAS substring, and

```text
length(V_k) = 8k+11,
newest S offset = 1,
true oldest S offset = 8k+11,
maximal terminal A-run t = 0,
Delta = (8k+11)-1 = 8k+10.
```

For every natural constant C0, k=C0 gives Delta>C0 while preserving all
these premises. This excludes any uniform constant bound derived only
from those word properties. It supplies no owner map, member set, onto
coverage, tightness, periodicity or actual Recaman realization.

## Complete proof

Let mass(w)=sum e_i and moment(w)=sum i e_i, exactly LeadingRunSupply's
definitions. The established append identity is

```text
M(uv)=M(u)+M(v)+length(u)*mass(v).
```

An SA pair has mass 0, moment 1; an AS pair has mass 0, moment -1.
Thus (SA)^k has mass 0, moment k, and (AS)^(3k) has mass 0, moment -3k.
Direct sums give C mass 1, moment 0, length 11, and exactly two SS pairs.
Appending C shifts its mass-one moment by 2k. Therefore

```text
mass(V_k)=1,
moment(V_k)=k+0+2k*1-3k=0.
```

This arithmetic alone would not prove minimality. To prove that property,
classify every positive proper prefix, in three exhaustive regions:

1. Inside the initial (SA)^k, mass is -1 at an odd length and 0 at an
   even length. No such prefix is P2.
2. Inside C, its positive proper mass-one prefix offsets are exactly
   r=3,5,7, with local moments 4,3,4. After the initial SA block their
   global positions/moments are (2k+3,3k+4), (2k+5,3k+3), and
   (2k+7,3k+4). Every moment is positive.
3. Starting at the complete C prefix, the mass-one visits are precisely
   after i complete AS pairs, 0<=i<=3k. Their positions are 2k+11+2i,
   with moment 3k-i. Prefixes after an odd number of signs in this last
   block have mass 2. The visit i=3k is the complete word. Every proper
   visit has i<3k and hence strictly positive moment. When k=0 this
   region contributes no proper visit.

The core table (including its end) is independently kernel checked:
mass-one offsets [3,5,7,11], moments [4,3,4,0]. All positions not listed
have mass different from one. The three-region split covers every prefix;
none of its proper mass-one moments is zero, proving minimal P2 for all k.

The alternating blocks contain no SS. Their joins to C are A|S on the
left and S|A on the right (when the blocks are nonempty), adding no SS.
The only two SS pairs are the ones inside C. Both first and last signs
of V_k are S, including k=0. This proves the stated offsets and t=0.

For NoSAAS of H_k, combine the current A with its initial SA block:
B_k=A(SA)^k is alternating. C's four-sign substrings belong to
{SAAA,AAAS,AASS,ASSA,SSAA}, excluding SAAS. The final AS block is
alternating as well. A four-sign substring crossing B_k|C is one of
ASAA, SASA, ASAS, according to whether it uses one, two or three signs
from the left block; impossible cases for a short block are simply absent.
A substring crossing C|AS^(3k) is ASSA, SSAS or SASA. No four-sign
substring can cross both joins because C has length 11. At k=0 the
right block is absent and only ASAA crosses the left join. This checks
every possible substring and proves NoSAAS.

The padding method is the existing E-122 construction with a different
fixed core. No new general padding theorem or many-source capacity result
is claimed; the contribution here is the exact SS=2 marked-offset family.

## Falsifier, controls and evidence limits

The card and script were frozen before runs. Base revision:
`cbe51b7b1216f9700f432eb14803277113c02af4`. Exact hashes and outputs:
`docs/data/ss2_word_offset_span_20261001/`.

```bash
shasum -a 256 -c docs/data/ss2_word_offset_span_20261001/PRE_RUN_SHA256SUMS
python3 experiments/ss2_word_offset_span.py discovery
python3 experiments/ss2_word_offset_span.py holdout
lake env lean docs/data/ss2_word_offset_span_20261001/core_controls.lean
```

Discovery k=0..10 and disjoint claim-specific holdout k=11..80 pass every
stated property and the complete proper mass-one position/moment table.
The largest checked word has length 651 and span 650. These facts are
`COMPUTED`, not the all-k proof; no untouched repository-wide data claim
is made. The full paper argument above establishes all k.

The wrong core AAASSSASASA at k=1 yields P2 prefixes at 7 and 19, so
padding an arbitrary P2 core does not guarantee minimality. Adding one
extra AS pair to the chosen k=1 word leaves moment -1 and an earlier P2
at 19. These predeclared controls fail exactly as expected.

## Next decision and stop recommendation

Stop attempts to bound Delta by a constant from minimality, SS=2,
NoSAAS, current-A and the terminal-A budget alone. To study actual
owner delta=r-kx, state which owner-family condition supplies kx, and
test that additional input separately. This family has no such condition
and does not decide whether the same words occur inside a tight family.
General #73, Hall capacity, Gate T6 and all protected labels are unchanged.

Same-session proposer/falsifier/paper-writer/auditor passes are complete;
the all-k statement is not claimed kernel checked or independently reviewed.
