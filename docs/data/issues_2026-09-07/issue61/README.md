# #61 verification artifacts

Unit: H-20260907-03 / E-060. Base revision:
`ad3367af4d508cdb1ddcbf84492fbb3c4fdf1672` plus the changes in this commit.
Lean 4.33.1; standard library only. Run commands from the repository root.

## Fixed finite audit

```bash
python3 experiments/clock112_closure_audit.py
```

Exact output: [boundary_audit.txt](boundary_audit.txt). This replays clocks 0 through 99734,
checks already certified endpoints, and tests the local-crossing / weakened-history interpretations.
It discovers no new statistical conjecture and claims no unused holdout.
The printed revision identifies the base checkout during the run; the script SHA-256 identifies
the uncommitted script used at that time. After committing, the revision line changes on rerun.
None of this output is assumed by the Lean proof.

## Lean and repository checks

```bash
lake env lean Recaman/PermanentAboveClock112Exclusion.lean
./scripts/check.sh
git diff --check
```

The consumer compiled on its first attempt. [check_summary.txt](check_summary.txt) preserves
the exact summary lines and all three new declarations' axiom reports from the final full check.
All dependencies use only the repository's permitted Lean axiom set.
[source_sha256.txt](source_sha256.txt) identifies the consumer, certificate type, theorem owners,
root, Audit, import contract, evidence registry, and finite-audit script tested.

## Import deletion controls

After building dependencies, the following reproduces [import_ablation.txt](import_ablation.txt).
Each trial removes only one direct import from a temporary copy of the consumer. Expected result:
compilation fails for each deletion. These controls test dependency ownership, not mathematical
independence or the sufficiency of every field of the replay certificate.

```bash
python3 - <<'PY'
from pathlib import Path
import subprocess
import tempfile

source = Path('Recaman/PermanentAboveClock112Exclusion.lean').read_text()
with tempfile.TemporaryDirectory() as folder:
    for owner in ['Recaman.PermanentAboveClock112FirstOccurrence',
                  'Recaman.DeepNineteenTraceCertificate']:
        trial = Path(folder) / 'Clock112ImportTrial.lean'
        trial.write_text(source.replace('import ' + owner + '\n', '', 1))
        run = subprocess.run(['lake', 'env', 'lean', str(trial)],
                             capture_output=True, text=True, timeout=60)
        assert run.returncode != 0, owner
        first = next(line.split('error', 1)[1] for line in run.stdout.splitlines()
                     if 'error' in line)
        print(f'removed={owner} expected_failure=PASS{first}')
PY
```

Conclusion and semantic audit: [hypothesis card](../../../HYPOTHESIS_CARD_2026-09-07_CLOCK112_CLOSURE.md).
This closes the clock-112 obligation; it does not certify coverage through clock777 or reopen a
global proof route.
