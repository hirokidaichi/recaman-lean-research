# Writer validation commands

All proposed live metadata was tested in isolated copy
`/tmp/recaman-registration-0200.WgTYMy/repo`. Exact output and exit codes are under `raw/`.

| Command | Timeout | Exit | Exact headline |
|---|---:|---:|---|
| `python3 scripts/harness_gate.py --check-registry docs/EVIDENCE_REGISTRY.tsv` | 120 s | 0 | `Harness gates G1-G5: 11 PROVED-LEAN rows >= E-344 pass.` |
| `python3 scripts/harness_gate.py --check-protected docs/EVIDENCE_REGISTRY.tsv docs/PROTECTED_CLAIMS.tsv` | 120 s | 0 | `Protected claims: 4 central rows keep their pinned labels.` |
| `python3 scripts/harness_gate.py --lint-module Recaman/ShortTightDonorAvoidance.lean` | 120 s | 0 | `20/21 substantive theorems`; cited three are substantive |
| `python3 scripts/report_vacuity.py --all Recaman/ShortTightDonorAvoidance.lean` | 120 s | 0 | `0/21 theorems flagged` |
| `python3 scripts/harness_gate.py --audit-template E-360 docs/EVIDENCE_REGISTRY.tsv` | 120 s | 0 | three cited signatures printed |
| `./scripts/check.sh` | 600 s | 0 | registry 360 / PROVED-LEAN 155; 392 jobs; axiom audit 2572; all passed |

The first rejected two-symbol isolated package had already passed G1-G5/protected/lint/vacuity but
its full check stopped at `E-360 is not referenced by docs/CURRENT_FRONTIER.md`. That exact failure
is recorded in `revision_notes.md`; it is not reused as a success. The three-symbol package was
rebuilt with the bounded frontier/proof-map drafts and checked fresh.
