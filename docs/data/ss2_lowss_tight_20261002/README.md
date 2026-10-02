# H-20261002-01 reproduction and handoff

Conclusion: E-368 proves arbitrary-length low-SS tight avoidance and one
extra S phase in the presence of a minimal SS2 donor. Both are periodic
sign-history theorems, not an orbit or general Hall result. The hypothesis
card status is PROVED-LEAN. Parent #73 remains open.

Base revision: 8ee8588f1015955c2474674ba1656cb296f8157c. One new module:
Recaman/SS2LowSSTight.lean. Root/Audit, registry, statement audits, card,
proof map/frontier/development log, reproducible experiment and viewer
manifest are synchronized. No protected label changes.

## Reproduction

Run from the repository root:

```bash
shasum -a 256 -c docs/data/ss2_lowss_tight_20261002/PRE_RUN_SHA256SUMS
python3 experiments/ss2_lowss_tight.py discovery
python3 experiments/ss2_lowss_tight.py holdout
lake build Recaman.SS2LowSSTight
lake env lean --trust=0 docs/data/ss2_lowss_tight_20261002/semantic_controls.lean
python3 scripts/report_vacuity.py --all Recaman/SS2LowSSTight.lean
python3 scripts/harness_gate.py --lint-module Recaman/SS2LowSSTight.lean
./scripts/check.sh
make test
```

Script and imported-generator hashes plus the original preimplementation
card are frozen in PRE_RUN_SHA256SUMS. Discovery lengths3/7/11/15/19 and
holdout23 are reused ranges, not untouched repository-wide data. JSON
records exact outputs: 916 minimal SS2 donors and 10,206 actual earlier-A
suffix candidates, zero collisions. Later low-SS covers are excluded by
the existing all-length chronology theorem, not by this finite scan.
Independent integer prefix-sum recomputation agrees. Finite evidence is
COMPUTED and never substitutes for the all-length proof.

## Strongest evidence and limitations

The generic suffix lemma supplies the substantive structural edge. It
proves a proper P2 prefix of any SS2 P2 word shaped Y-A/P2-suffix/A-tail,
contradicting donor minimality. E-128 normalizes each member inside its
original lag and provides injection. Tightness makes this image onto N(B),
so modular endpoint exclusion implies actual neighborhood avoidance.
The extra-S inequality also proves that the recursive oldest offset
selects an actual S before counting it. Exactly one extra S is asserted.

Manual R/W/C/T aligned with the independent auditor is 3/6/0/0; heuristic vacuity is 0/9 and module
lint is 9/9 substantive. Helper transports are not separate advances.
Parent p26/d19 nonempty tight application, basic offset boundaries and
donor-minimality countermodel are in semantic_controls.lean.

## Failed weakenings and next decision

Removing donor minimality admits AASASASASSSAAAS with proper P2 prefix3;
removing SS2 admits AAASSSSAAAS with SS3. The same-donor high-SS endpoint
control refutes unrestricted endpoint exclusion, not tight-set avoidance.
The p17 w1 singleton covers the donor phase but is not tight. No earlier
current-S cover was found in the frozen range, so that assumption's
necessity is not claimed. Initial implementation failures were elaboration
(coercion, index metavariable, core tactic name), not mathematical repairs.

The long low-SS p36 singleton is not tight and tests endpoint/slack only;
nonempty tight examples separately test the tight theorem. No theorem
asserts multiple donors have distinct oldest phases. Remaining uncertainty
is high-SS tight members and general T6/capacity/orbit realization. Stop
this completed low-SS unit; choose one concrete high-SS interaction for a
new frozen falsification protocol, without reviving constant-span repairs
or increasing a finite census ceiling.

## Final audit and validation

Separate entry and final semantic audits PASS. The final review binds to
source SHA256 `8e0bcf9497e11fafd93fb5f625f43a8b6f788ebe8d1de4f6c471e979ddc63a73`.
Full `./scripts/check.sh` and `make test` pass: 396 build jobs, 2657 audited
declarations, only permitted axioms, empirical regressions and manifest.
Independent controls were also rerun with `--trust=0` after archival.
The module compiled at 09:53 UTC within the frozen route gate.

Additional reproducible commands:

```bash
python3 docs/data/ss2_lowss_tight_20261002/entry-independent.py
lake env lean --trust=0 docs/data/ss2_lowss_tight_20261002/independent_controls.lean
lake env lean docs/data/ss2_lowss_tight_20261002/independent_axioms.lean
```

The archived independent Python checker has only its root/output paths
adapted for portability; its enumeration and prefix-sum logic are unchanged.
The original command record retains the auditor's /tmp paths; archived
files carry the corresponding independent_ names. The auditor's kernel
controls consume the new theorems at p18 tight, p36 lag15 and p28 nonminimal
A-ended supplier cases; p28 normalization explicitly proves f(7)=3 inside
the original lag7 neighborhood. A period36 variant changes only the donor
current bit to S and still applies the strict-capacity theorem.
