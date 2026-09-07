# Issue 73 first pass: sources, exact output, and validation

Base revision: `b4b5afaaac126acaa0c4fc0042bdaa4fafd289a1`.
New programs and the Lean module were working-tree files when executed; the base
does not pretend to contain them. [SHA256SUMS](SHA256SUMS) identifies their exact
content, their dependencies and all evidence artifacts. The commit containing
this bundle preserves them together. Rerunning after committing changes the
reported current HEAD, but not the fixed base or mathematical inputs.

Conclusion: [arbitrary-period short supplier capacity](../../ISSUE73_PERIODIC_SUPPLY_2026-09-07.md).
The all-lag conjecture in [issue #73](https://github.com/hirokidaichi/recaman-lean-research/issues/73)
remains open. The new `PROVED-LEAN` result has **lag<=7**, with no upper bound
on the word period. Raw automaton certificates for other lag limits remain
`COMPUTED`; they were not promoted to an all-lag result.

## Reproduction

Run from the repository root. Preserve original output by redirecting new runs
to `/tmp` or a new directory. Use `PYTHONDONTWRITEBYTECODE=1` for Python runs.

| Command after `python3` | Preserved output | Evidence role |
|---|---|---|
| `experiments/issue73_20260907/hall_falsifier.py --mode discovery` | [hall_discovery.txt](hall_discovery.txt) | Frozen new Hall property, periods1..12 |
| `experiments/issue73_20260907/hall_falsifier.py --mode holdout` | [hall_holdout.txt](hall_holdout.txt) | Frozen conditional periods13..18; previously used word ranges |
| `experiments/issue73_20260907/automaton_falsifier.py --mode discovery --output-dir /tmp/issue73-potentials` | [automaton_discovery.txt](automaton_discovery.txt) | Shift graphs for L=3,7,11,15 |
| `experiments/issue73_20260907/automaton_falsifier.py --mode holdout --output-dir /tmp/issue73-potentials` | [automaton_holdout.txt](automaton_holdout.txt) | Frozen graph for L=19 |
| `experiments/issue73_20260907/geometry_certificate_audit.py` | [geometry_certificate_audit.txt](geometry_certificate_audit.txt) | Independent direct sign/moment check of all 1,118,480 graph edges |
| `experiments/issue73_20260907/geometry_escape_selector.py` | [geometry_escape_selector.txt](geometry_escape_selector.txt) | New escape selector falsification |
| `experiments/issue73_20260907/geometry_escape_family.py` | [geometry_escape_family.txt](geometry_escape_family.txt) | Exact regression for the algebraic counterfamily |
| `docs/data/issue73_20260907/macro_minimum_endpoint.py` | [macro_minimum_endpoint.txt](macro_minimum_endpoint.txt) | Minimum-lag oldest-sign counterexample |
| `docs/data/issue73_20260907/macro_second_moment_control.py` | [macro_second_moment_control.txt](macro_second_moment_control.txt) | Exact positive second-moment counterexample |
| `docs/data/issue73_20260907/macro_all_addition_debt.py` | [macro_all_addition_debt.txt](macro_all_addition_debt.txt) | Future-run debt counterexample |
| `docs/data/issue73_20260907/macro_short_lag_injection.py` | [macro_short_lag_injection.txt](macro_short_lag_injection.txt) | Regression for the all-period paper U7 injection |
| `docs/data/issue73_20260907/macro_extension.py --min-period 1 --max-period 12` | [macro_extension_discovery.txt](macro_extension_discovery.txt) | Fixed U7 map plus lag11, new property |
| `docs/data/issue73_20260907/macro_extension.py --min-period 13 --max-period 18` | [macro_extension_conditional.txt](macro_extension_conditional.txt) | Conditional continuation over previously used words |
| `docs/data/issue73_20260907/macro_extension_verify.py` | [macro_extension_verify.txt](macro_extension_verify.txt) | Independent domain and matching-witness verification |

Scripts that import other experiment modules require those exact source files;
the common manifest includes them. Source hashes embedded in output identify
the executing programs, rather than treating a Git base alone as provenance.

## Potential encoding and lossless storage

`automaton_L*_potential.txt.gz` stores the exact generated potential vector,
one decimal integer per line before compression, indexed by a mask whose least
significant bit is the newest sign. Bit1 means A, bit0 means S. The original
logs contain SHA-256 of the **uncompressed** payload. Compression used
`gzip.compress(payload, mtime=0)` and was verified by exact decompression.
The five raw payloads total 1,118,480 bytes; the gzip files total 26,112 bytes.
The independent audit accepts either raw or gzip paths and validates the same
uncompressed hashes. No data were discarded to shrink the bundle.

## Mathematical and semantic audits

- [macro_proof_attempt.md](macro_proof_attempt.md): paper U7 injection, exact
  failed generalizations, fixed-map extension protocol and results.
- [short_lag_independent_audit.md](short_lag_independent_audit.md): independent
  all-period injection proof, including small periods and cyclic quotient.
- [lean_semantic_audit.md](lean_semantic_audit.md): exact P2 equivalence, actual
  sign windows, arbitrary period telescoping, and lag11 scope control.
- [geometry_attempt.md](geometry_attempt.md): escape counterfamily and the
  unresolved subtraction-sink obstruction in the geometric descent argument.
- [automaton_independent_audit.md](automaton_independent_audit.md): independently
  computed edge inequalities and cycle-to-word semantics; finite evidence only.
- [literature_audit.md](literature_audit.md): limited primary-source search;
  no claim of exhaustive coverage or mathematical novelty.

## Repository validation

```sh
lake env lean Recaman/ShortPeriodicSupply.lean
./scripts/check.sh
shasum -a 256 -c docs/data/issue73_20260907/SHA256SUMS
git diff --check
```

[validation.txt](validation.txt) records the final build, import/registry audits,
axiom audit, Python syntax and source/output hash checks. The five new major
declarations are in `Recaman/Audit.lean`. The earlier parallel-research bundle
and the user's untracked visualizer were not changed.
