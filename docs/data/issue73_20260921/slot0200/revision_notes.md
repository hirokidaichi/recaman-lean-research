# Registration-draft revision notes

## Rejected v1: two audit symbols

The first metadata draft cited only `w1_next_addition` and `short_tight_avoids_ss2_donor`.
At the independently recorded review, the auditor and parent observed that H-20260920-01's exact W
has two conclusions: `own t = t - 7` and `e (t + 1) = true`. Promoting the whole card from a row
that cited only next-A would be incomplete. The correction adds `w1_owns_oldest` as a third audit
symbol and quotes its G5 signature. No theorem, hypothesis, proof, source file, computation, or
mathematical conclusion changed. This is a registration citation repair, not the card's permitted
mathematical repair.

The rejected files and hashes are preserved as:

- `rejected_v1_2symbol_proposed_registry_row.tsv`:
  `0addcf3a4fe8dcb147ace8732c4c2f8642a5c4ba967d17123c72bdc2489cec4b`
- `rejected_v1_2symbol_EVIDENCE_REGISTRY.proposed.tsv`:
  `e867b740426ef263610a0af599864502105231f5687ac9dab6f006befe33ebda`
- `rejected_v1_2symbol_E-360.md`:
  `c694998d8007f58f36bc0ea247b099c7ba11bd66c563d4be4dc33a40232c8365`

The first isolated full check of v1 stopped with exit 1 after the module/import gates because
`E-360` was not referenced by `docs/CURRENT_FRONTIER.md`. The preceding v1 G1-G5, protected,
lint, vacuity, and audit-template checks passed. The stopped full check is a metadata dependency
failure, not a Q/W counterexample or Lean failure. The three-symbol revision includes minimal
frontier and proof-map append drafts and must be checked anew.

## Clock correction

The initial message to the auditor was labelled 02:13 based on an incoming status label, but the
parent's independent clock was 02:11. The repository `date` sample after that finding was
`2026-09-21 02:11:34 JST (+0900)`. This note uses command-derived time and does not backdate the
draft freeze.
