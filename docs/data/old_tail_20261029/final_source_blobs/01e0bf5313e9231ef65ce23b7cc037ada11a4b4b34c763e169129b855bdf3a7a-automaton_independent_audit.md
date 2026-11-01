# Independent audit of the frozen finite-state certificates

- Owner: joint_generation / independent auditor.
- Base: `b4b5afaaac126acaa0c4fc0042bdaa4fafd289a1`.
- Scope: H-20260907-09 second gate and the saved L=3,7,11,15,19 certificates.
- Frozen acceptance: independently recompute supply by signed sums over every
  lag 1..L, verify both outgoing edge inequalities at every state, and confirm
  the conceptual positive-cycle reduction. Do not call the root supplier code
  and do not extend L or the word-period census.
- Final status: independent verification `COMPUTED`, all 1,118,480 edges PASS.
  No finite graph result is promoted to all L or all-lag capacity.

## Conceptual audit

A state encodes exactly the L preceding signs, newest at the least significant
bit. Appending a new sign shifts the earlier history back by one offset and
forgets only its oldest sign. In particular the P2 predicate is evaluated on
the preceding state, before appending the currently classified A.

The weight is −1 for S, +1 for A supplied at a lag at most L, and 0 for any
other A. On a directed cycle, the binary-shift consistency makes every state
exactly the length-L backward history of the periodic emitted word. This also
holds when the cycle period is shorter than L: repeated cycles reconstruct
all the older bits. The cycle weight is therefore `|U_L|−|D|`, with cyclic
phases counted once each. A positive cycle implies `|U|≥|U_L|>|D|`, refuting
E-070. It also automatically has positive sign sum because `|A|≥|U_L|>|D|`.
Once positivity of the sign sum is known, the word-only P2 bound
`d≤p(p+1)−1` ensures these short supplies are in the U used by E-070, even if
L exceeds that bound. It does not imply U=A and thus is not necessarily a
counterexample to E-067.

For a saved integer potential V with `V(next)≥V(state)+weight` on every edge,
summing around any cycle gives `0≥total weight`. These are finite certificates
of no positive cycle for the stated L. The validity of the certificates does
not depend on the queue algorithm that discovered V, provided every edge is
independently checked. It does not require the period to be bounded.

The parent/depth positive-cycle extraction path in the root search is guarded
by explicit cycle-transition and positive-weight assertions, plus two direct
periodic supplier checks. No positive-cycle branch occurred in the saved logs,
so this audit relies only on the potential branch and its all-edge verification.

## Independent checks

Completed: the checker uses direct signed sums and signed first
moments at every lag, including lags excluded by the root's mod-4 optimization.
Negative control: dropping the weighted-moment equation would incorrectly give
positive weight to the all-A self-loop; the certificate must reject that change.
Positive control: the third A of SAAA is supplied at lag 3 at every frozen L.


| L | States | Both outgoing edges checked | Supplied states |
|---:|---:|---:|---:|
| 3 | 8 | 16 | 1 |
| 7 | 128 | 256 | 18 |
| 11 | 2,048 | 4,096 | 305 |
| 15 | 32,768 | 65,536 | 5,035 |
| 19 | 524,288 | 1,048,576 | 82,196 |

The direct signed-sum predicate agrees with the recorded count at every L.
Both edge types have minimum slack zero and no negative slack. Every payload
SHA-256 agrees with its original discovery/holdout record; potential histograms
and lengths also agree. The reader accepts either raw text or gzip, hashing the
same decompressed payload. Both positive and negative controls pass.

The algorithm uses every lag from 1 through L. It neither calls the root
`is_supplied` function nor imports its optimized supplier dependency. New next
states are reconstructed from the decoded preceding signs, so a reversed
history convention would not silently reuse the root transition formula.

This audit validates the saved finite numerical certificates. The generic
cycle-word correspondence and telescoping implications above have complete
paper arguments, but the checked certificate payloads retain the evidence
label `COMPUTED`; this audit is not a Lean proof. The root's U7 development is separate; no Lean verification status is inferred
from this certificate audit.

## Reproduction and handoff

```sh
python3 experiments/issue73_20260907/geometry_certificate_audit.py > docs/data/issue73_20260907/geometry_certificate_audit.txt
```

Checker SHA-256:
`2b7433b9dd2a06c6d41fe4ef990bc1ae5b4843ba3683045b1f6fc87759f9165c`.
Exact output includes each payload hash and all per-L counts. No horizon was
extended, no potential was changed, and no old bundle, Lean source, shared map,
Git/GitHub state, or user visualizer was edited. Owned additions are this audit,
the checker, and its exact output log. Decision: accept these five certificates
as independently checked finite evidence; retain the all-L conjecture as open.
