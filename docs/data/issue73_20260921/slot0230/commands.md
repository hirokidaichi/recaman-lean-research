# Commands run in slot0230

All commands ran from
`/Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research`.

```sh
date '+%Y-%m-%d %H:%M:%S %Z'
git status --short
git rev-parse HEAD
shasum -a 256 Recaman/ShortTightDonorAvoidance.lean docs/EVIDENCE_REGISTRY.tsv \
  Recaman/OwnerFamilyLagEleven.lean Recaman/PeriodicOwnerFamilyLagEleven.lean
python3 scripts/report_vacuity.py --all Recaman/ShortTightDonorAvoidance.lean
python3 scripts/harness_gate.py --lint-module Recaman/ShortTightDonorAvoidance.lean
sed -n '360,391p' Recaman/ShortTightDonorAvoidance.lean
python3 docs/data/issue73_20260921/slot0230/control_replay.py
./scripts/check.sh
```

No new Lean source, exploratory experiment, registry row, or E-number was created. The packet adds
`control_replay.py` solely to reproduce the fixed named audit controls; it performs no discovery or
holdout search.

After independent audit and explicit parent authorization, the live H-20260921-01 card alone was
replaced by the byte-identical approved proposal using `apply_patch`. The initial live version was
first preserved as `HYPOTHESIS_CARD_2026-09-21_SHORT_SUPPLY_DONOR_DELETION.preapply.md`. A `diff -u`
between the approved proposal and applied live card exited 0.
