# Commands and raw-log index

- Working directory for every command:
  `/Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research`
- HEAD at freeze: `08c08565c743f39350c9b959e1df7d30aa1cae5d`
- Time zone: JST (`+0900`)
- No new diagnostic or helper source was created or executed. Therefore the pre-execution source-SHA
  rule did not need a new-source entry. Existing scripts and target sources were hashed in
  `raw/precheck_identity.log` before checks.

## Identity and source snapshots

At 2026-09-24 01:05:06 JST, the packet recorded `git rev-parse HEAD` and SHA-256 for the target
Lean source, both OwnerFamily dependencies, root, Audit, registry, official E-360 G5, both live
cards, plan, prior handoff, and all three executed scripts. Exact output:
`raw/precheck_identity.log`.

The two live cards were copied byte-for-byte before drafting:

- `original_main_card_at_freeze.md`: SHA-256
  `2e9c54c289925a0c6072a519495369f2345a72ddf7361b8fbebdd425eadac8d3`
- `original_deletion_card_at_freeze.md`: SHA-256
  `c138c3ca29fe0971ac0b6d41480c8ebf0d790202267883a4c2a9805b937d43bb`

Their hashes matched the live cards at freeze. Raw source/audit/registry snapshots and inherited
original control output are under `raw/`; they are copies, not reruns or new holdouts.

The first packet wording grouped unrestricted all-lag deletion with failed/stopped interpretations.
Because that could be read as a status claim about the still-open general problem, the exact old
packet was preserved as `raw/candidate_packet.before_parent_correction.md` (SHA-256
`12823899eec9c17bc9b8a20e9400a19f5e0724af1cd36c611c7a7354ac35a32a`) before correction. The live
candidate now separates refuted controls from unlicensed, still-open extensions. No mathematical
hypothesis or evidence label changed.

After independent review, the then-current packet and all proposed-card variants were preserved in
`raw/before_independent_correction/`. The correction limits E-358/E-359 to the dependency of the
current registered proof/application route rather than claiming mathematical uniqueness, and
quotes the actual premises that prevent E-351 `aas_after_w1_forced` from proving next-A. Again no
mathematical hypothesis or evidence label changed.

The independent auditor then reported the corrected wording as semantic-PASS pending final freeze
and independently confirmed both full live-ready files equal their frozen original card, one
newline, and the corresponding corrected append. The writer reproduced both comparisons with
`diff -u` process substitutions; both exits were 0. The pre-correction manifest and earlier
identity log remain in `raw/` and are not presented as final.

## Executed checks

```text
start=2026-09-24 01:06:58 JST
argv=timeout 120s python3 scripts/report_vacuity.py --all Recaman/ShortTightDonorAvoidance.lean
exit=0
```

Result: 0/21 theorems flagged. Raw metadata/stdout/stderr:
`raw/vacuity.command.log`, `raw/vacuity.stdout.log`, `raw/vacuity.stderr.log`.

```text
start=2026-09-24 01:06:59 JST
argv=timeout 120s python3 scripts/harness_gate.py --lint-module Recaman/ShortTightDonorAvoidance.lean
exit=0
```

Result: 20/21 classified substantive; `tight_w1_next_addition` is the one wrapper. This heuristic
does not establish meaning or novelty. Raw files: `raw/lint.command.log`, `raw/lint.stdout.log`,
`raw/lint.stderr.log`.

```text
start=2026-09-24 01:06:59 JST
end=2026-09-24 01:07:05 JST
argv=timeout 120s ./scripts/check.sh
exit=0
```

Result: root 389/389 modules, import contracts 110, registry 360 entries / 155 PROVED-LEAN,
G1-G5 11 rows, protected 4 rows, build 392 jobs, axiom audit 2,572 declarations. Raw files:
`raw/full_check.command.log`, `raw/full_check.stdout.log`, `raw/full_check.stderr.log`.

## Not executed

- No new mathematics exploration, period-range extension, p32/33 rerun, new holdout, Lean source,
  registration, promotion, or live-card edit.
- No OS/pure-AAS/lag15 brute-force branch was reopened.
- No `--audit-template E-360` skeleton was generated: the official exact G5 already exists and was
  compared against the source. The weekly verbatim comparison is `verbatim_statement_audit.md`.
