# Commands and raw streams

Working directory for every command:
`/Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research`.
HEAD at start: `08c08565c743f39350c9b959e1df7d30aa1cae5d`.
Started `2026-09-23 02:32:50 JST`; candidate frozen before the 02:42 deadline.
No command extends the declared discovery/holdout ranges. All substantive
executions use a 120-second wall timeout.

| Command | Exit | stdout | stderr |
|---|---:|---|---|
| `gtimeout 120s python3 experiments/issue73_20260920/ss2_intervening_prefix.py --mode discovery` | 0 | `replay_discovery.stdout` | `replay_discovery.stderr` |
| `gtimeout 120s python3 experiments/issue73_20260920/ss2_intervening_prefix.py --mode holdout` | 0 | `replay_holdout.stdout` | `replay_holdout.stderr` |
| `gtimeout 120s python3 docs/data/issue73_20260923/slot0230/literal_checker.py` | 0 | `literal_checker.stdout` | `literal_checker.stderr` |
| `gtimeout 120s lake env lean docs/data/issue73_20260923/slot0230/Diagnostics.lean` | 0 | `diagnostics.stdout` | `diagnostics.stderr` |
| `gtimeout 120s lake env lean Recaman/SS2OldestPattern.lean` | 0 | `direct_lean.stdout` | `direct_lean.stderr` |
| `gtimeout 120s python3 scripts/report_vacuity.py --all Recaman/SS2OldestPattern.lean` | 0 | `vacuity.stdout` | `vacuity.stderr` |
| `gtimeout 120s python3 scripts/harness_gate.py --lint-module Recaman/SS2OldestPattern.lean` | 0 | `lint.stdout` | `lint.stderr` |
| `gtimeout 120s ./scripts/check.sh` | 0 | `check.stdout` | `check.stderr` |

Every `.exit` file contains the literal exit status. Every stderr file is empty.
Both replay stdout files are byte-identical (`cmp` exit 0) to the corresponding
daytime JSONL. `SOURCE_SHA256SUMS.at_freeze` records target, dependencies,
root/Audit, original card/paper/plan, frontier/registry/proof map/protected,
experiment, original outputs, and pre-holdout hash record.

The first executions of the newly written `literal_checker.py` and
`Diagnostics.lean` lacked separately persisted pre-run hashes. The later
`SOURCE_SHA256SUMS.at_freeze` must not be read as retroactive proof of those
first runs' source identity. Their initial sources and raw outputs were retained.
At `2026-09-23 02:38:31 JST`, before a single replay, their unchanged hashes
were saved in `AUX_PRE_REPLAY_SHA256SUMS` as respectively
`7b2d748d00725adc1957d1cb8f0c737c134c795a392673c04f319c414cffe17a` and
`f0ad3cf2367174942e75d137b27a22a0f6a3eb579c3e15f82810e4b10387fe94`.
Each was then run once with `gtimeout 60s` into `*_replay.stdout/stderr`;
both exits are zero, stderr is empty, and byte comparison to each first stdout
is zero. This confirms the current sources reproduce the raw results, while
leaving the first-run provenance gap explicitly unresolved.

Read-only context commands included `git status --short`, `git rev-parse HEAD`,
`sha256sum`, `rg`, `sed`, `nl`, and `cat` over AGENTS instructions, README,
AI research protocol, status report, roadmap, current frontier, glossary,
proof map, portfolio, registry, today's handoff, both relevant cards, paper,
source, experiment, and frozen outputs. The exact relevant E-069, E-130,
E-133, E-240, E-345, E-351, and E-360 entries were checked. No stage, commit,
source edit, or process remains from these commands.
