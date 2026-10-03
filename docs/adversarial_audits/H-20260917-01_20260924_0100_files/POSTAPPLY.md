# Post-application verification

Checked at `2026-09-24T01:17:51+0900` in
`/Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research`.

- HEAD unchanged: `08c08565c743f39350c9b959e1df7d30aa1cae5d`.
- Research Lean source unchanged: `bb12f35acc8e48c584cead52d675e36b034afda22f0f28ecfd245031f70fee85`.
- Applied main card SHA-256:
  `adab6db01a6cf362a889a5371a2fb5d942897ff15f1246e8f941939c5958d857`;
  byte-equal to approved `proposed_main_card_full_live_ready.md` (`cmp=0`).
- Applied deletion card SHA-256:
  `e872cf0a4c8b62c0e7d4f1e8b317e2cfa74c58013d5128a7b4e0c07fceba9f2a`;
  byte-equal to approved `proposed_deletion_card_full_live_ready.md` (`cmp=0`).
- Weekly report SHA-256:
  `d433403a3e9a94ca99d52f7f0e664ebf4ae550ce718ccb420778fcd2ec7037c8`.
  The approved weekly section SHA
  `1523a4cc2d7dc094d7d8c11328cd4584feb6656c7eda1e9b63f10054733e13a6`
  occurs exactly once, begins at byte offset 513, and is the complete suffix (`suffix_bytes=0`).
  The preceding 513 bytes are the parent-authored heading/partial-report notice.
- No audit/check/helper process remained.

Exact stdout/stderr/exit: `postapply.stdout`, `postapply.stderr`, `postapply.exit`.
The original `SHA256SUMS` and `AUDIT_REPORT.md` were not changed after the pre-application freeze.
The original manifest has 39 entries and verified 39/39 OK. An earlier parent message from this
auditor said 36/36; that was a counting error, not a checksum failure.
