# 2026-10-24 evidence packet

Conclusion first: nine bounded inputs E-390–394/E-396–399 are PROVED-LEAN; E-395 refutes only an internal
stronger auxiliary. E-388/r4 classification remains COMPUTED, general C1 remains open. See the daily handoff
and RESEARCH_NOTE_2026-10-24_C1_INPUTS.md for quantifiers and mathematical connections.

Authoritative source reproduction: `python3 docs/data/c1_four_20261024/generate_final_sources.py` checks
byte identity without changing sources; `--write` writes the two generated small modules. It uses the
small FourNonsuppliedData template and q4-certificate/q_checker_prefix, not the stopped r4 generators.
The q4 input was reused from2026-10-23, then kernel verified for16 explicit roots only.

`final-source-manifest.json`, `final-dirty.patch` and `source_snapshot` preserve the dirty Lean overlay,
including all untracked dependencies; HEAD alone does not reproduce the checked state. Initial source
hashes/patch are in start artifacts. `preserved-work-verification.json` checks unrelated tracked changes.

Exploration: frozen protocol/RUNS plus macro_graph/macro_independent, then last-free and motif run records.
Exact stdout/json/time files are retained. Source/input hashes are checked by provenance-check.json.
Known reused examples and unpopulated holdout shards are explicit, not labeled fresh holdout evidence.

STOPPED engineering: generate_lean/generate_function_blocks/generate_natblocks, bench_four.lean.txt,
all four-*.lean.txt and conditional-four-induction.lean.txt describe failed large-table variants.
They are not active checked research results. validation*_result/kernel-first-stop preserve process/RSS guards.
Do not regenerate the current framework with those scripts or resume by only raising time/memory.

Final checks: check-low-mass-final.log, registry-reopen-gates-final.log, lint-*-final.log,
test-tools-final.log, SEMANTIC_AUDIT.md and generated statement_audits E-390–394/E-396–399.
Final actual-time accounting is published only after the genuine research_session stop by finalize_daily.py. H13 extends E-399 to exact low-mass old-window/actual-A EndN equivalence.
The final manifest excludes itself/pycache; CPU is separate from confirmed journal wall intervals.
