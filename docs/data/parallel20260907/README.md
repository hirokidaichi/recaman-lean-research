# Five-pattern parallel research: reproducibility bundle

Research date: 2026-09-07. Repository source base:
`612fcfaf74bfb49f3ae05a268057c82f70dcca26`.

The experiment programs were new, uncommitted files at execution time. The base
revision identifies their repository context, **not** a commit already containing
the programs. Their exact content is identified by the SHA-256 embedded in each
output and by [SHA256SUMS](SHA256SUMS). The commit containing this bundle preserves
those sources together. Some programs report the executing HEAD as well as the
base; that metadata line will change when rerun after committing.

All arithmetic and membership checks use exact integers, except the κ diagnostic,
which uses exact rational numbers. No experiment output is a proof of an infinite
claim. See the [ranked report](../../PARALLEL_APPROACH_TRIAGE_2026-09-07.md), its five
hypothesis cards, and the two independent paper/scope audits in this directory.

## Commands

Run from the repository root. Redirect fresh results to a separate location to
preserve the original observations. In this table every program path is relative
to `experiments/parallel20260907/`; invoke it with `python3`.

| Program and arguments | Preserved exact output | Role |
|---|---|---|
| `entry_probe.py --limit 1000000` | [entry_probe.txt](entry_probe.txt) | Existing canonical range; first-hit source classification |
| `entry_canonical_swap.py` | [entry_canonical_swap.txt](entry_canonical_swap.txt) | Fixed canonical/modified-history witness; no new holdout |
| `entry_source_birth.py` | [entry_source_birth.txt](entry_source_birth.txt) | Second-pass birth inequality falsifier; fails at 5@129 |
| `birth_connected_support.py --mode discovery` | [birth_discovery.txt](birth_discovery.txt) | Frozen enrichment inputs: prefix horizons 0, 4, 128 |
| `birth_connected_support.py --mode holdout` | [birth_holdout.txt](birth_holdout.txt) | Frozen enrichment inputs: 1000, 10000, 200000; old trajectory data reused |
| `macro_periodic_supply.py --min-period 1 --max-period 12` | [macro_periodic_discovery.txt](macro_periodic_discovery.txt) | Frozen discovery; 3,458 positive-sum words |
| `macro_periodic_supply.py --min-period 13 --max-period 18` | [macro_periodic_holdout.txt](macro_periodic_holdout.txt) | Frozen holdout; 225,587 positive-sum words |
| `macro_witness_controls.py` | [macro_witness_controls.txt](macro_witness_controls.txt) | Post-holdout selector diagnostics; exploratory search labelled OBSERVED |
| `macro_phase_count.py --max-period 16` | [macro_phase_count.txt](macro_phase_count.txt) | Post-holdout strengthening diagnostic; 56,747 words |
| `macro_matching_map.py` | [macro_matching_map.txt](macro_matching_map.txt) | Frozen oldest-S injection falsifier; period-12 collision |
| `periodic_audit_kappa.py` | [periodic_audit_kappa.txt](periodic_audit_kappa.txt) | Fixed exact-rational counterexample to minimum-κ selection |
| `periodic_search.py` | [periodic_search.txt](periodic_search.txt) | Separately frozen second pass; seed 20260907; 90,640 evaluations with repetitions |
| `holes_capacity.py` | [holes_capacity.txt](holes_capacity.txt) | Finite regressions for the abstract absorption argument |

For example:

```sh
PYTHONDONTWRITEBYTECODE=1 python3 experiments/parallel20260907/macro_matching_map.py > /tmp/parallel20260907-macro-matching-map.txt
shasum -a 256 -c docs/data/parallel20260907/SHA256SUMS
./scripts/check.sh
```

The second-pass search protocol is [periodic_search_protocol.md](periodic_search_protocol.md).
Canonical entry provenance is detailed in [entry_README.md](entry_README.md).
Scripts importing another local experiment are covered together with
their imported source by the common manifest; an individual script hash alone
does not identify such a dependency.

## Audit and limits

- [periodic_independent_audit.md](periodic_independent_audit.md) checks the positive
  quadratic drift, finite preperiod removal, bounded supplier lag and P2 reduction.
- [scope_independent_audit.md](scope_independent_audit.md) checks all five units and
  the boundaries between arbitrary histories and canonical reachability.
- [validation.txt](validation.txt) records repository checks, source/output hash
  consistency and Python syntax validation. No Lean source or theorem was added.
- Finite-word enumeration has no cutoff-independent force. A word satisfying all
  addition identities would refute the proposed word obstruction, but would not
  establish an actual greedy periodic orbit: subtraction freshness remains separate.
- The stopped static-summary and hole-only abstractions are proper weakenings of
  actual history. Their countermodels do not prove canonical non-surjectivity.

## Next bounded question

Prove or refute the all-period P2 obstruction in H-20260907-07. A stronger possible
route is `|U| <= |D|`, where U is the supplied addition phases and D is the
subtraction phases. The oldest-S map is already refuted. A general Hall argument,
if used, must prove its condition for every subset; a finite matching is insufficient.
Further horizon extension alone is not the next unit's acceptance criterion.
