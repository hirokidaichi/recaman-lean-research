# Commands and raw-output map

## Context

- cwd for repository reads: `/Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research`
- audit cwd: `/tmp/recaman-weekly-audit-20260924-0200-sol`
- HEAD: `08c08565c743f39350c9b959e1df7d30aa1cae5d`
- start: `2026-09-24 02:03:58 JST`
- repository mode: read-only; no stage, commit, gate/protected/registry/source edit
- short `date`, `git`, `find`, `stat`, `wc`, `cat`, `sed`, `rg`, `tail`, `sha256sum`, `cmp`, `ps`
  inspection commands had no external process timeout. A tool yield value is not a timeout.

Required documents were read directly: `AGENTS.md`, `README.md`, `docs/AI_RESEARCH_PROTOCOL.md`,
`docs/STATUS_REPORT_2026-08-30.md`, `docs/ROADMAP.md`, `docs/CURRENT_FRONTIER.md`, relevant
`docs/GLOSSARY.md`, `docs/PROOF_MAP.md`, `docs/RESEARCH_PORTFOLIO.md`,
`docs/EVIDENCE_REGISTRY.tsv`, the one-week plan, all H-01 through H-05 and deletion cards,
daily handoffs, 01:00/01:30 and historical independent audits, Lean sources, paper, experiment source/raw.

The exact declaration inventory command was:

```sh
rg -n '^(theorem|private theorem|def|private def) ' Recaman/SS2OldestPattern.lean
```

- cwd: repository root
- external timeout: none
- exit: 0
- stdout/stderr: `raw/ss2oldest_all_symbols.stdout`, `raw/ss2oldest_all_symbols.stderr`
- exit file: `raw/ss2oldest_all_symbols.exit`

It printed 13 theorem declarations. The first 3 are the previously limited-audit declarations; the
remaining 10 names are quoted in `AUDIT_REPORT.md`.

## Persisted runner

Runner source: `source/run_persisted_checks.py`, pre-run SHA recorded in
`prehash/RUNNER_PRE_RUN.sha256`. It used `subprocess.run(..., capture_output=True, timeout=30)` for
each of four jobs and saved exact argv/cwd/timeout/elapsed/exit in `raw/run_metadata.json`.

1. `python3 source/inventory_check.py`
   - cwd: audit directory
   - timeout: 30 seconds
   - final exit: 0, 29/29
   - raw: `raw/inventory_check.{stdout,stderr,exit}`
2. `shasum -a 256 -c /tmp/recaman-weekly-audit-20260924-0200-sol/prehash/REPO_TARGETS.sha256`
   - cwd: repository root
   - timeout: 30 seconds
   - final exit: 0, 15/15
   - raw: `raw/repo_targets_verify.{stdout,stderr,exit}`
3. `shasum -a 256 -c SHA256SUMS`
   - cwd: `docs/adversarial_audits/H-20260917-01_20260924_0100_files`
   - timeout: 30 seconds
   - final exit: 0, 39/39
   - raw: `raw/prior_0100_manifest.{stdout,stderr,exit}`
4. `shasum -a 256 -c SHA256SUMS`
   - cwd: `docs/adversarial_audits/H-20260920-02_20260924_0130_files`
   - timeout: 30 seconds
   - final exit: 0, 63/63
   - raw: `raw/prior_0130_manifest.{stdout,stderr,exit}`

The final inventory checker SHA is
`98edd884537a4e6a1c525f1e88acc55eb51b7e634adba9bca6337e61397d5c85`, frozen in
`prehash/INVENTORY_CHECK_FINAL_PRE_RUN.sha256` and copied to `source/inventory_check.v4.py`.
This checker verifies text presence, evidence labels, exact theorem count/names and forbidden
overclaims. It is not a semantic proof audit.

## Failed and prior checker versions

- v1: `source/inventory_check.v1.py`, SHA `63791cae...`; exit1 because it incorrectly expected
  E-240 registry label `REFUTED`. The first REPO_TARGETS file was empty due wrong checksum-generation
  cwd, so that job also exited1. Exact raw/metadata: `raw/run_v1/`.
- v2: SHA `33d13afe...`; corrected E-240 and rebuilt 15-target checksum, then 19/19 and 15/15.
  Raw: `raw/run_v2/`. `source/inventory_check.v2.py` was reconstructed after its initial alias-save
  omission; its SHA matches the pre-run hash. This is not described as original source retention.
- v3: `source/inventory_check.v3.py`, SHA `db8b1bc8...`; declaration count and names passed, but an
  over-strict contiguous prose-string condition failed. Exact raw/metadata: `raw/run_v3/`.
- v4 prefinal and final: unchanged source SHA `98edd884...`; both exit0. The prefinal candidate run is
  in `raw/run_v4_prefinal/`; the final frozen-candidate run is the top-level `raw/` set.

## Full-file byte checks

Command:

```sh
sh /tmp/recaman-weekly-audit-20260924-0200-sol/source/byte_compare_final.sh
```

- cwd: repository root
- external timeout: none; elapsed below one second
- source prehash: `prehash/BYTE_COMPARE_FINAL_PRE_RUN.sha256`
- exit: 0
- raw: `raw/byte_compare_final.{stdout,stderr,exit}`
- result: weekly and main-card full files equal original bytes + one LF + approved append bytes.

An exploratory GNU-style `cmp -n` invocation returned exit1/EOF on this macOS `cmp`; no conclusion
used it. The portable frozen script instead uses `head -c`, explicit LF inspection and `tail -c`.

## Lean policy

No Lean build, vacuity check, lint, or `./scripts/check.sh` was run in this 02:00 inventory slot.
Current source hashes match the archived 01:00/01:30 targets. The cited vacuity 0/21 and 0/13,
lint 20/21 and 13/13, and full check exit0 with 392 jobs/2572 declarations are prior same-source
results, whose manifests were verified above; they are not represented as current executions.

## Finalization

Final process inventory, final time, report/command hashes and manifest verification are stored under
`raw/` and described in `AUDIT_REPORT.md`. `SHA256SUMS` excludes itself and the final manifest
verification raw files to avoid a checksum self-cycle.
