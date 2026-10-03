# Commands and execution provenance

Audit root: `/tmp/recaman-weekly-audit-20260924-0130-sol/`

Repository cwd unless otherwise stated:
`/Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research`

Repository HEAD at entry: `08c08565c743f39350c9b959e1df7d30aa1cae5d`.
Entry clock: `2026-09-24 01:33:30 JST (+0900)`.

## Independent fixed controls

The v1 source was saved before execution and prehashed in
`prehash/FIXED_CONTROLS_PRE_RUN.sha256`:
`d8fcbf11d929f76d25c8daf9f93718d281acf93eef81a69defbf05f99250f5b8`.

```text
cwd=/tmp/recaman-weekly-audit-20260924-0130-sol
argv=timeout 120s python3 -u source/fixed_controls_v1.py
stdout=raw/fixed_controls_v1.stdout
stderr=raw/fixed_controls_v1.stderr
exit=0
stderr_bytes=0
completed=2026-09-24 01:35:39 JST
```

The parent requested more explicit H-02/H-04 premise fields. The v1 source and
raw output were preserved. The changed source was saved separately as v2 and
prehashed in `prehash/FIXED_CONTROLS_V2_PRE_RUN.sha256`:
`881807083aae6028722f7df5fd3919686ce40adf221574179a721f61955d6fbc`.

```text
cwd=/tmp/recaman-weekly-audit-20260924-0130-sol
argv=timeout 120s python3 -u source/fixed_controls_v2.py
stdout=raw/fixed_controls_v2.stdout
stderr=raw/fixed_controls_v2.stderr
exit=0
stderr_bytes=0
completed=2026-09-24 01:37:05 JST
```

Both runs are deterministic literal recomputations with no seed, discovery
range, holdout, search cap, or range extension. They check only the fixed p13,
p4, p9, p16 and five word-level controls already consumed on 2026-09-23.

## Lean and harness checks

Inputs were prehashed in `prehash/GATE_INPUTS_PRE_RUN.sha256`. Target hashes:

- `Recaman/ShortTightDonorAvoidance.lean`: `bb12f35acc8e48c584cead52d675e36b034afda22f0f28ecfd245031f70fee85`
- `Recaman/SS2OldestPattern.lean`: `a9540f5f891198ec91eefd73f62f9e35d4e59f645936dc3a349504e529b325de`

Each command had an external 120 second timeout and completed before it.

```text
argv=timeout 120s python3 scripts/report_vacuity.py --all Recaman/ShortTightDonorAvoidance.lean
stdout=raw/vacuity_short.stdout stderr=raw/vacuity_short.stderr exit=0
result=0/21 flagged

argv=timeout 120s python3 scripts/report_vacuity.py --all Recaman/SS2OldestPattern.lean
stdout=raw/vacuity_ss2.stdout stderr=raw/vacuity_ss2.stderr exit=0
result=0/13 flagged

argv=timeout 120s python3 scripts/harness_gate.py --lint-module Recaman/ShortTightDonorAvoidance.lean
stdout=raw/lint_short.stdout stderr=raw/lint_short.stderr exit=0
result=20/21 substantive; tight_w1_next_addition classified wrapper

argv=timeout 120s python3 scripts/harness_gate.py --lint-module Recaman/SS2OldestPattern.lean
stdout=raw/lint_ss2.stdout stderr=raw/lint_ss2.stderr exit=0
result=13/13 substantive

argv=timeout 120s ./scripts/check.sh
stdout=raw/check.stdout stderr=raw/check.stderr exit=0
result=392 jobs; 2572 declarations; allowed axioms only
completed=2026-09-24 01:36:20 JST
```

The diagnostic source was saved before execution and prehashed in
`prehash/TARGET_AXIOMS_PRE_RUN.sha256` as
`db3a3c7c68d1398c5fd82512c6417000f10b06ef61e21d11c3ade162517c1347`.

```text
argv=timeout 120s lake env lean /tmp/recaman-weekly-audit-20260924-0130-sol/source/TargetAxioms.lean
stdout=raw/target_axioms.stdout stderr=raw/target_axioms.stderr exit=0
completed=2026-09-24 01:38:34 JST
```

The raw output contains the elaborated signatures and allowed axioms for the
H-02 target, H-03 equality, H-04 literal certificate, and the H-05 local three.
Lean/harness acceptance is not used as the semantic or procedural verdict.

## Frozen archive verification

All successful commands below used `sha256sum -c` and exited 0. Raw outputs are preserved.

```text
cwd=<repo>/docs/adversarial_audits/H-20260920-02_20260923_0130_files
argv=sha256sum -c SHA256SUMS
raw=raw/h02_manifest.stdout, raw/h02_manifest.stderr
result=149/149 OK

cwd=<repo>/docs/adversarial_audits/H-20260920-03_20260923_0200_files
argv=sha256sum -c SHA256SUMS
raw=raw/h03_manifest.stdout, raw/h03_manifest.stderr
result=32/32 OK

cwd=<repo>/docs/adversarial_audits/H-20260920-04_20260923_0100_files
argv=sha256sum -c SHA256SUMS
raw=raw/h04_manifest.stdout, raw/h04_manifest.stderr
result=29/29 OK

cwd=<repo>/docs/adversarial_audits/H-20260920-04_20260923_0100_files
argv=sha256sum -c SHA256SUMS_CORRECTION
raw=raw/h04_correction.stdout, raw/h04_correction.stderr
result=1/1 OK

cwd=<repo>/docs/adversarial_audits/H-20260920-05_20260923_0230_files
argv=sha256sum -c SHA256SUMS.v2
raw=raw/h05_manifest.stdout, raw/h05_manifest.stderr
result=42/42 OK

cwd=<repo>
argv=sha256sum -c docs/adversarial_audits/H-20260920-02_20260924_0130_parent_files/BASELINE_SHA256SUMS
raw=raw/parent_baseline_verify.stdout, raw/parent_baseline_verify.stderr
result=17/17 OK

cwd=<repo>/docs/data/issue73_20260924/slot0130
argv=sha256sum -c SHA256SUMS
raw=raw/writer_manifest.stdout, raw/writer_manifest.stderr
result=35/35 OK
manifest_sha256=99d301678e022040dc0b626dccd354fb51db0dc10e312956959451c8061b1552
```

The first attempt to verify the parent baseline used
`cwd=<repo>/docs/adversarial_audits/H-20260920-02_20260924_0130_parent_files`
and `argv=sha256sum -c BASELINE_SHA256SUMS`. The manifest paths are
repository-relative, so it exited 1 with 17 `No such file` errors. That failed
output appeared directly in the tool transcript before raw-file routing was
added; it is described here rather than reconstructed as a raw file. No source
was changed. The exact same manifest was then checked from the repository root
with the successful argv/raw record above.

## Read-only inspection

Read-only commands included `sed`, `nl`, `rg`, `find`, `wc`, `git rev-parse`,
`git status --short`, `git log -1`, `sha256sum`, and `diff -u` over the required
protocol, plan, README/status/roadmap/glossary/proof-map/portfolio entries,
four live cards, both target sources, the paper, 9/23 audit reports and archive
contents, 9/24 handoff/weekly report, and the slot0130 proposal. They made no
repository writes. The exact high-value executable commands and their raw
outputs are the records above; exploratory file reads were not mathematical
experiments.
