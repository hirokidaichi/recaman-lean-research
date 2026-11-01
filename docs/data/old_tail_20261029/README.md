# 2026-10-29 reproduction packet

Conclusion: E451 is kernel-checked three-A-run actual free-gap. E456 is a derived four-interval supply19/residual bound, NOT absence or a general C1 theorem. Read ../../RESEARCH_HANDOFF_2026-10-29_DAILY.md first.

## Files and evidence

- START.json: revision/dirty tracked diff and all436 initial Lean file hashes.
- FINAL_SOURCE_MANIFEST.json + final_source_blobs/: all450 final mathematical Lean files, including untracked dependencies, and core gate/build inputs. The digest matches after the final standard full check. FINAL_VERIFICATION.json points to the raw final check log/result.
- REPRODUCTION_MANIFEST.json expands the restoration inputs with EVERY evidence-registry artifact, G5 file, and current architecture/frontier input. This expansion was captured after the main check. A correct restoration of bytes is not a completed cold validation.
- cold_project/: earlier449 Lean source snapshot before E456; optional cold512MB rebuild failed in existing ShortPeriodicSupply. No resource-increased retry was made.
- COMMAND_INDEX.json: exact recorded worker/Lean argv, start/end/exit and raw log links. Failed attempts remain. Frozen per-command target bytes are under frozen/.
- CPU_ACCOUNTING.json: separately measured mathematical/fixed-control workers, guard validation, and Lean/build validation. Include failed/killed jobs; no claim of a generic process-tree cap or measured agent thinking CPU.
- H02_PREFLIGHT.json / H09_PREFLIGHT.json: finite discovery and reserved independent holdout. H02 posthoc lacked a separate preflight, stays OBSERVED. Existing finite rows are not a fresh holdout.
- DOMAIN_CONTROLS.json / FOUR_RUN_CONTROL.json: fixed nonvacuity checks, COMPUTED only. They do not establish absence of counterexamples or canonical orbit reachability.
- STATEMENT_CONTRACTS.json and FOUR_RUN_STATEMENT_CONTRACT.json: post-implementation expected whole-type checks, not preimplementation freezes. Their Lean files are audit fixtures, not research modules. The optional dependency_audit.lean fixture failed and is not a main import or proof dependency.
- SEMANTIC_AUDIT.md / UNIT_INDEX.md: exact domain/countermodel/dependency distinctions, mapping journal units to stable hypothesis IDs.
- AUTOMATION_FINAL_READBACK.json: same automation/thread/cadence retained and exact next-entry prompt read back. It is not evidence of future120min completion.

## Restore the byte snapshot without executing a build

Use restore_sources.py with a NEW, non-existing destination directory. It refuses an existing destination, verifies each blob hash and rejects paths outside that destination. It does not alter the current checkout or start Lean/CPU research jobs.

```sh
python3 docs/data/old_tail_20261029/restore_sources.py /absolute/path/to/new-restore-directory
```

This creates only the recorded inputs, not .lake caches, Git metadata, the journal, or the entire research history. The Lean toolchain is pinned by lean-toolchain and has no third-party Lake package dependencies. A future replay still needs its declared CPU/memory/deadline contract; restoring this packet does not reopen STOPPED cold/H06/r4 jobs or permit a resource-only retry.

Normal verified command in the current working tree was ./scripts/check.sh:451jobs/3027 declarations, permitted axioms only. New14 main Lean files passed module lint. No gate changes/stage/commit/push by this session.
