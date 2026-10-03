# Approval before live E-360 application

- decision: **PASS / 合格**
- auditor: GPT-5.6 Sol `/root/sol_20260921_registration_audit0200`
- decision clock: `2026-09-21 02:17:16 JST (+0900)`
- bundle verification clock: `2026-09-21 02:17:50 JST (+0900)`
- HEAD: `08c08565c743f39350c9b959e1df7d30aa1cae5d`

The corrected three-symbol registration bundle may be applied live. Approval is limited to byte-identical application of the payloads below. The initial two-symbol draft is rejected and preserved; it may not be applied.

## Approved payload hashes

- registry: `012c7e42974931c115efc2e64d9a254deaeb58ff78ac440af713cdb1a497a076` (`EVIDENCE_REGISTRY.proposed.tsv`)
- official G5: `a95cb573b86e99368daa68e2080091e5772b11f0081c1cc45df3fe4c60d63565` (`E-360.live-ready.md`)
- Q card: `2e9c54c289925a0c6072a519495369f2345a72ddf7361b8fbebdd425eadac8d3`
- W card: `ab7259ef648dc9c1607658a102b7120f4cdcd6e4083b36b3ae8798d09fbca2f0`
- current frontier: `d5b8f93bb943c5ccc24b3dc43a02e058acc086f0bceae18b52de98f7196decbf`
- proof map: `53496ad0b5d7705d4784e01505e11755db69cae2372ce6bc62f189fa553845b3`
- handoff: `a202f5228b9af75aaf58304564dfc112ea56c07ecd87c695ddaaa43346ab8883`
- writer bundle manifest: `cea01ab4661643495e42afc2303bd531f10caaf24c2bc0a577decbbaa0303c95` (`SHA256SUMS`, 35 entries)
- writer manifest narrative: `9d3153f6b2583970d198cac9c40bba3245b8dcfd201267ef135b5550a7984763` (`MANIFEST.md`)

Frozen mathematical sources remain:

- ShortTight lines 1--358: `bb12f35acc8e48c584cead52d675e36b034afda22f0f28ecfd245031f70fee85`
- OwnerFamily: `0bc2293b5d67f7ef5865f7a3f67b2fbf10aeb76bfa92eac9a086cc893c5846f4`
- PeriodicOwnerFamily: `a90c8f2ac7e6b98dfda4a260434d2e44d3e35781c3212f6a04b7952e9ef6b4c0`

## Exact registered symbols

1. `Recaman.ShortTightDonorAvoidance.w1_owns_oldest`
2. `Recaman.ShortTightDonorAvoidance.w1_next_addition`
3. `Recaman.ShortTightDonorAvoidance.short_tight_avoids_ss2_donor`

This is the minimum set matching both exact W conclusions and Q. W remains conditional on the expanded four-field `OwnerFamily`; Q remains restricted to positive-period periodic sign words, nodup tight in-range current-A B phases with minimal P2 lag 3/7/11 windows, and a minimal lag-11 SS=2 donor.

## Pre-application evidence

Writer isolated bundle raw files:

- `raw/g1_g5.log`: exit 0, 11 gated rows.
- `raw/protected.log`: exit 0, 4 protected labels unchanged.
- `raw/lint.log`: exit 0, 20/21 substantive; all cited symbols substantive.
- `raw/vacuity.log`: exit 0, 0/21 flagged.
- `raw/audit_template.log`: exit 0, all three exact signatures.
- `raw/full_check.log`: exit 0, registry 360 / PROVED-LEAN 155, 392 jobs, axiom audit 2572.
- `raw/source_hash_status.log`: frozen source hashes and HEAD recorded.

Independent auditor reproduction:

- `raw/isolated_g1_g5.three_symbols.raw.log`: exit 0.
- `raw/isolated_protected.three_symbols.raw.log`: exit 0.
- `raw/official_g5_template.three_symbols.raw.log`: exit 0.
- `raw/lean_core.raw.log`, `raw/harness_lint.raw.log`, `raw/report_vacuity.raw.log`, `raw/full_check.pre_registration.raw.log`: exit 0.
- `raw/qw_premise_matrix.v2.raw.log`: exit 0; positive/negative controls and exact nonempty OwnerFamily realization.
- `raw/core_audit_signatures_axioms.raw.log`: exit 0; exact signatures and permitted axioms only.

`shasum -a 256 -c` on the writer's 35-entry manifest passed at 02:17:50 JST; exact output is `raw/writer_bundle_manifest_verify.raw.log`.

## Application condition

After copying the seven approved payloads to their live paths, independently verify their hashes, rerun G1-G5, protected claims, `git diff --check`, and `./scripts/check.sh`. Any byte mismatch, source hash change, missing live G5, changed protected label, or failed check revokes this approval. Do not apply or promote later ShortTight declarations, SS2OldestPattern semantics, used p32/p33 holdout, arbitrary lag, general Gate T6, orbit claims, or Recaman-sequence surjectivity.

The historical missing daytime entry audit and 01:00 checker-source retention gap remain unresolved process history; this PASS does not rewrite them.

## Post-application confirmation

Final decision remains **PASS / 合格**. The writer reported application at `2026-09-21 02:20:47 JST`. Independent verification at `02:21:08 JST` found all seven live files byte-identical to the approved payloads and all approved hashes exact. The frozen source hashes and HEAD remained unchanged. Live G1--G5, protected claims, and `git diff --check` exited 0. Independent `./scripts/check.sh` completed at `02:21:19 JST` with registry 360 / PROVED-LEAN 155, 392 jobs, and 2572 permitted-axiom reports, exit 0. See `raw/post_apply_identity_gates.raw.log` and `raw/post_apply_full_check.raw.log`.
