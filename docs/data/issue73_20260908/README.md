# Issue 73 second pass: sources, exact output, and validation

Base revision: `8b07f93fbbb17352c091cabaa333fc366a66c04f`.
New programs and Lean modules were working-tree files when executed.
[SHA256SUMS](SHA256SUMS) identifies scripts and evidence artifacts.

Conclusion: [lag-11 capacity and lag-by-lag stop](../../ISSUE73_LAG11_CAPACITY_2026-09-09.md).
The all-lag conjecture in [issue #73](https://github.com/hirokidaichi/recaman-lean-research/issues/73)
remains open. The new `PROVED-LEAN` result is `|U7 ∪ U11min| ≤ |D|` with no
upper bound on the word period. Lag-15 remains `PROVED-PAPER`. The lag-by-lag
type-to-offset class is `STOPPED`.

Do not treat `recaman-visualizer/` or `__pycache__/` as part of this bundle.

## Reproduction

Run from the repository root. Preserve original output by redirecting new runs
to `/tmp` or a new directory. Use `PYTHONDONTWRITEBYTECODE=1` for Python runs.

| Command after `python3` | Preserved output | Evidence role |
|---|---|---|
| `experiments/issue73_20260908/lag11_classify.py` | [lag11/classify.txt](lag11/classify.txt) | 29 raw / 17 min-lag-11 types |
| `experiments/issue73_20260908/lag11_verify_independent.py` | [lag11/verify_csp.txt](lag11/verify_csp.txt) | U7-blocked CSP assignment, pairwise clash |
| `experiments/issue73_20260908/lag11_regression.py` | [lag11/regression_csp.txt](lag11/regression_csp.txt) | Cyclic regression p=1..18 of φ11 |
| `experiments/issue73_20260908/lag15_csp.py` | [lag11/lag15_csp.txt](lag11/lag15_csp.txt) | 155-type injective assignment |
| `experiments/issue73_20260908/lag15_verify.py docs/data/issue73_20260908/lag11/lag15_csp.txt` | [lag11/lag15_verify.txt](lag11/lag15_verify.txt) | Independent rebuild |
| `experiments/issue73_20260908/lag15_regression.py docs/data/issue73_20260908/lag11/lag15_csp.txt 18` | [lag11/lag15_regression.txt](lag11/lag15_regression.txt) | Cyclic regression of φ15 |
| `experiments/issue73_20260908/uniform_selector.py` | [lag11/uniform_selector.txt](lag11/uniform_selector.txt) | d-independent selector stop (E-088) |
| compiled `counterword_search.cpp` `19 22` | [counterword/summary.txt](counterword/summary.txt) | Exhaustive U=A, p=19–22 |
| compiled `automaton_Ln.cpp` `23` | [potential/L23_cpp.txt](potential/L23_cpp.txt) | No positive cycle, max P=5 |

Lean:

```sh
lake env lean Recaman/LagElevenSupply.lean
lake env lean Recaman/LagElevenPeriodic.lean
./scripts/check.sh
```

Python scripts that import siblings must be run from
`experiments/issue73_20260908/` or with that directory on `PYTHONPATH`.

## Mathematical notes

- [lag11/injection_proof.md](lag11/injection_proof.md): paper φ11, wrap argument
- [lag11/paper_attempt.md](lag11/paper_attempt.md): gap-class refutation, SOLUTION0
- [lag11/lag15_injection_proof.md](lag11/lag15_injection_proof.md): paper φ15
- [geometry/inventory_attempt.md](geometry/inventory_attempt.md): I_inv / I_win stop
- [potential/formula_attempt.md](potential/formula_attempt.md): Lean7 embedding stop
- Cycle handoffs: `HANDOFF_CYCLE2_LAG15.md` … `HANDOFF_CYCLE6_STOP.md`

Python `automaton_Ln.py --horizon 23` crashed after emptying its queue
(`potential/L23.txt`). The C++ rerun is the L=23 certificate.
