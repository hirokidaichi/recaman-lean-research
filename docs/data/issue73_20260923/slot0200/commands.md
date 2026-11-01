# H-20260920-03 slot0200 command record

All commands ran in
`/Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research`.
HEAD before execution: `08c08565c743f39350c9b959e1df7d30aa1cae5d`.
The worktree was already dirty; no pre-existing files were edited by this
worker. No seed was used. All finite runs below revisit known ranges; p15
was a historical holdout and is not a fresh holdout now.

| Command (exact argv after shell redirection) | Pre-run source SHA-256 | Timeout | Exit | Raw stdout / stderr |
|---|---|---:|---:|---|
| `python3 -u docs/data/issue73_20260923/slot0200/prefix_semantics.py` | `0b7ab1830fc5dc05616cc02081b0a483a0aa56ef2d72190994f1a64f41c20f5d` | 90s via `timeout` | 0 | `prefix_semantics.stdout` / `prefix_semantics.stderr` |
| `python3 -u experiments/issue73_20260920/short_prefix_reduction.py --mode discovery` | `95eb3fb1f49c20087fea345ec1404461ddebc8f0bf0751d9e2c1f41e44830a61` | 180s via `timeout` | 0 | `replay_discovery.stdout` / `replay_discovery.stderr` |
| `python3 -u experiments/issue73_20260920/short_prefix_reduction.py --mode holdout` | same original source hash | 180s via `timeout` | 0 | `replay_holdout.stdout` / `replay_holdout.stderr` |
| `python3 scripts/report_vacuity.py --all Recaman/ShortTightDonorAvoidance.lean` | target Lean `bb12f35acc8e48c584cead52d675e36b034afda22f0f28ecfd245031f70fee85` | 90s via `timeout` | 0 | `vacuity.stdout` / `vacuity.stderr` |
| `python3 scripts/harness_gate.py --lint-module Recaman/ShortTightDonorAvoidance.lean` | same target Lean hash | 90s via `timeout` | 0 | `lint.stdout` / `lint.stderr` |
| `./scripts/check.sh` | same target Lean hash; root/Audit already dirty | 180s via `timeout` | 0 | `check.stdout` / `check.stderr` |
| `lake env lean docs/data/issue73_20260923/slot0200/SignatureAudit.lean` | `817bf728d9e003571a8c6b7aa945756f67bd75037f121d92c05671054368abe8` | 90s via `timeout` | 0 | `signature.stdout` / `signature.stderr` |

`cmp replay_discovery.stdout docs/data/issue73_20260920/daytime/short_prefix_discovery.jsonl`
and the analogous p15 holdout comparison both exited 0, with no output:
the replay bytes match the original raw files. The frozen originals have
SHA-256 `6694755065b89e8f76a4f19b8471e1fc2d0a6393265ed6eff2f778ce939c460a`
and `be783e95eb9ceefec330ae59bc5e681ddfcc43fd787107a12bd54a78972b16b9`.

`prefix_semantics.py` is a new independent finite control, not a proof or a
new holdout. It enumerates singleton current-A examples at p1..12, checking
the exact P2 mass/moment definition and actual modular subtraction phases.
Its source was hashed before execution. It returned 8,190 cycles,
5,786 strict tight instances of the broader source signature,
5,630 exact-card tight identity instances, 945 exact-card strict nontight
instances, and zero exact-card strict tight singleton instances. The
original all-sublist experiment gives the stronger finite coverage for
the exact-card strict/tight intersection.

`report_vacuity.py` reported `0/21` flagged. The module lint reported
`20/21` substantive. `check.sh` completed 392 jobs and 2,572 axiom-audited
declarations. These are tool outcomes, not a semantic nonvacuity decision.
The explicit source and statement review is in `statement_audit.md`.

No failed command was used to infer a research result. The previously
reported zero `tight_nonminimal` count is not a command failure: the old
script's `PASS` condition did not require this count to be positive.
