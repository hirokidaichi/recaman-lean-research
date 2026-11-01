# Commands

- Repository cwd: `/Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research` unless noted.
- Isolated cwd: `/tmp/recaman-weekly-audit-20260924-0230-sol` for fixed recomputation and audit artifacts.
- Read-only commands used: `git status --short`, `git rev-parse HEAD`, `date`, `find`, `wc`, `sed`,
  `nl`, `rg`, `sha256sum`, `diff`, `cmp`, `awk`, `ps`, and direct reads of source, cards, manifests,
  archived raw outputs, the automation evidence JSON, and live automation TOML.
- Manifest verification: `sha256sum -c` on the 02:00 parent manifest, 02:00 independent
  `SHA256SUMS.final`, and slot0100/0130/0200 manifests.
- Independent fixed arithmetic: `python3 source/audit_checks.py`; no external timeout because it is a
  fixed literal check completing in under one second. Source prehash and stdout/stderr/exit are saved.
- Existing full-U fixed regression: `timeout 30s python3 -u source/verify_donor_length_boundary.py`;
  source copied byte-for-byte from the repo and prehashed before execution. stdout/stderr/exit are saved.
- Candidate verification: `source/run_checks.sh`, with exact output in `raw/`. It performs no Lean or
  research computation beyond the fixed H-04 checks listed above.
- No `report_vacuity.py`, `harness_gate.py`, Lean build, `scripts/check.sh`, discovery census, shard run,
  or range extension was executed in this audit slot.
