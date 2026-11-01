# Commands and exact outputs

Frozen input/revision/source records precede exploration. Run guards are in each script/validation_watch.
All paths below are relative to this packet unless a repo path is shown.

| Command / operation | Protocol / output | Evidence scope |
| --- | --- | --- |
| python3 .../macro_graph.py | PROTOCOL.md, RUNS.json, macro-discovery.stdout/.time, macro-certificate.json | finite relaxed A-event graph |
| python3 .../macro_independent.py | macro-independent.stdout/.time/.json | all normalized states/edges plus928 unused long-gap controls |
| lake build FourNonsuppliedData, four representations | kernel-first-stop.json, validation-result.json, validation-natblocks-result.json, validation-split-result.json; logs/time | STOPPED resource failures; no r4 kernel proof |
| python3 .../last_free_chain.py | LAST_FREE_RUN.json, last-free-result.json/stdout/time |26 model candidates; existing actual witnesses |
| python3 .../last_free_independent.py | LAST_FREE_INDEPENDENT_RUN.json, last-free-independent.json/stdout/time |88 actual pairs, holdout0; E-395 only |
| python3 .../motif_gaps.py | MOTIF_RUN.json, motif-gaps.json/stdout/time | six known nodes; not fresh unseen range |
| lake env lean Recaman/BlockSuffixPositivity.lean | lean-*.log | individual compilation, including failed syntax/constructor attempts |
| ./scripts/check.sh | check-low-mass-final.log, earlier check*.log | final399entries/183Lean,408jobs/2782decl; earlier failures retained |
| bash scripts/check_research_registry.sh | registry-reopen-gates-final.log | reopened gates synchronized,39 G1–G5 cases,4 protected |
| python3 scripts/harness_gate.py --lint-module ... | lint-four-final/lint-sixteen-final/lint-block-final.log |7/8,29/30,145/159 substantive (heuristic) |
| make test-tools | test-tools-final.log | dev7/session12/harness18 all pass |
| make brief | brief-final.txt (final refresh) | latest labels/current next unit |
| python3 .../generate_final_sources.py | final-source-reproduction.json | byte-identical small final modules |
| automation_update(existing recam-n-6-8) | automation-update-args/result/before/after/verification.json | prompt updated; schedule/thread/status preserved |
| python3 scripts/research_session.py start/checkpoint/stop | ../daily_research/2026-10-24.json, final-journal-status.json | genuine clock; waiting/gaps excluded |
| python3 .../finalize_daily.py | final-allocation.json, final-packet-manifest.json, DAILY/card metrics | requires real closed journal; no retrospective time |

The timed five exploratory jobs sum to approximately6.66CPU seconds/6.73wall seconds at two-decimal time precision.
Lean/kernel/engineering/recording CPU is not fully measured; the total CPU is unknown, not6.66.
