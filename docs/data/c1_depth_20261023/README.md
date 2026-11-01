# 2026-10-23 evidence packet

The mathematical source is in the two generated Recaman/ThreeNonsupplied*Data modules and
Recaman/BlockSuffixPositivity.lean. `generate_lean_data.py` reads `checker_prefix.txt` and
certificate.json; `generate_q_lean.py` reads q_checker_prefix.txt and q-certificate.json.
The old `checker_suffix.txt` and `certificate-closed-only.lean.txt` are diagnostic history,
not inputs to the current generated modules.

Protocols precede all searches. RUNS/INDEPENDENT_RUN/SIGNATURE_RUN/CERTIFICATE_RUN/Q_RUN/
HIGHER_RUNS/RELAXED_HIGHER_RUN/HIGHER_INDEPENDENT_RUN/Q4_RUNS/TERMINAL_SUPPORT_RUN freeze sources and argv.
`audit_artifacts.py` verifies their source hashes, summarizes the fixed word classes, and saves
rounded external user+sys accounting. Tiny literal-control CPU is capped but not measured;
Lean/compiler CPU is validation and is not completely measured for the early attempts.

`higher-holdout.json` is incomplete: its wall guard was reached. It is not evidence of global absence.
The separate prefix-free higher model completed and was independently reconstructed.
COMPUTED r4 data is not a kernel proof. All raw stdout/time/model outputs are retained.

One whole-array kernel check was stopped at approximately7GB RSS; a whole balanced lookup
attempt was also stopped. The final checker uses balanced lookup and32-row chunks.
These were engineering changes to certificate evaluation; no mathematical predicate was weakened.
The complete source used by the successful kernel checks is preserved in the final source snapshot.

The final source snapshot was refreshed only to clarify that E-383 is historical bounded
computation superseded by E-386 for az<=3. Its manifest is the authoritative final dirty hash.
The mathematical Lean sources still match the successful check-final-math run.
`finalize_daily.py` refuses an open journal, writes exact closed metrics into DAILY, and
hashes the packet plus external journal/DAILY in final-packet-manifest.json. The final
manifest excludes itself and Python bytecode caches. No stop-tail is backfilled as work.
