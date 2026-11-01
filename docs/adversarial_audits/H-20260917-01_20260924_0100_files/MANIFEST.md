# Independent audit artifact manifest

Final audit conclusion: `AUDIT_REPORT.md`.
Exact command ledger: `COMMANDS.md`.
Complete file hashes: `SHA256SUMS` (excludes only itself).

## Lean checks

- `vacuity.*`: exact `report_vacuity.py --all` stdout/stderr/exit.
- `lint.*`: exact `harness_gate.py --lint-module` stdout/stderr/exit.
- `check.*`: exact full `scripts/check.sh` stdout/stderr/exit.
- `shorttight.sha256`: target source identity.

## Independent fixed controls

- `independent_controls.py`: final v2 helper source.
- `independent_controls.v2.pre.sha256`, `.stdout`, `.stderr`, `.exit`: v2 evidence.
- `independent_controls.v1.reconstructed.py`: post-run reconstruction of the accidentally
  unpreserved v1 source; its hash equals `independent_controls.pre.sha256`.
- `independent_controls.stdout`, `.stderr`, `.exit`: original v1 run.
- `independent_controls.v1.reconstructed.replay.*`: byte-identical replay of v1 raw output.
- `e133_source.pre.sha256`, `e133_replay.*`: existing original p=16 scanner replay. This is not
  a new independent implementation or a full recertification of E-133.

## Final identity checks

- `writer_manifest_verify.*`: 52/52 writer-packet checksum verification.
- `full_composition.*`: both full-card proposals equal frozen original + LF + corrected append.
- `final_state.*`: final HEAD, target/candidate hashes, dirty repo inventory, and residual-process
  check. The repo was already dirty; this auditor made no repo write.

All diagnostics and reports in this directory are outside the repository, as required.
