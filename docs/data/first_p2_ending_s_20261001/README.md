# First P2 ending S: frozen finite falsification

Conclusion: no counterexample to issue #74 or the proposed shifted-moment
invariant was found in the frozen literal enumeration. These results are
`COMPUTED`; the general proof is `Recaman/FirstP2EndingS.lean` (E-362).

Base revision: `65f457efdd36a2ec8f47283a9ddc36e173333d56`.
Protocol: H-20261001-02, [frozen card](protocol.frozen.md).
Script SHA-256: `7b18283d797474dd280729a8e03cc6cbf54e39da1d2cc03a2ed2abd439dad140`.
The script and initial card were hashed before either run. The initial card
was later copied byte-for-byte to protocol.frozen.md; only its path in the
hash manifest was redirected to that immutable copy before updating the
live card. Its pre-run digest is unchanged.

From the repository root:

```bash
shasum -a 256 -c docs/data/first_p2_ending_s_20261001/PRE_RUN_SHA256SUMS
python3 experiments/first_p2_ending_s.py discovery
python3 experiments/first_p2_ending_s.py holdout
```

Exact outputs are [discovery.json](discovery.json) and [holdout.json](holdout.json).
The holdout ran once after discovery and before Lean implementation.

| Phase | Lengths | Literal words | Ceiling ≤2 | No-P2 nonempty | With P2 | First-P2 / D violations |
|---|---|---:|---:|---:|---:|---:|
| Discovery | 0..11 | 4,095 | 2,638 | 2,339 | 298 | 0 / 0 |
| Holdout | 12..16 | 126,976 | 70,290 | 62,848 | 7,442 | 0 / 0 |

The ranges are disjoint for this protocol, not previously untouched repository
data. This enumerates all binary words, including words with no P2 prefix.
It checks the first P2 specifically, strengthening the original E-361 script's
test for existence of some S-ended P2. It also checks D>0 for every nonempty
ceiling-two word without any nonempty P2 prefix. Each shorter prefix is itself
in the enumeration where its length falls in the selected range.

Negative controls: AASASSA has ceiling 2, P2 at 3 and 7 and ends A; this
refutes removing minimality from the whole-word theorem. AAASSSASASA has
ceiling 3 and only P2 at 11, ending A; this refutes replacing 2 by 3.
Empty/A/ASSA have no P2 prefix. AAS has its first P2 at 3, ending S.

No repair, changed constants, or expanded census was needed. The statement
is about abstract words, so history was maximally weakened from the start.

## Lean verification

```bash
lake env lean docs/data/first_p2_ending_s_20261001/semantic_controls.lean
python3 scripts/harness_gate.py --lint-module Recaman/FirstP2EndingS.lean
python3 scripts/report_vacuity.py --all Recaman/FirstP2EndingS.lean
./scripts/check.sh
```

The standalone controls verify the weakened-statement counterexamples in
the kernel and apply the least-index corollary to AASASSA. Lean exits zero
with no diagnostics. [Lint](lint.log): 3/4 substantive declarations.
[Vacuity](vacuity.log): 0/4 flagged. [Full check](check.log): 391 jobs pass,
2,553 audited declarations use only permitted axioms. A copied build cache
from the exact same base-revision worktree was used; Lake checked inputs
and rebuilt the changed module and root. No build directory is shared.

Independent-session semantic review is still pending. These logs and the
same-session G5 audit do not claim that condition was met.
