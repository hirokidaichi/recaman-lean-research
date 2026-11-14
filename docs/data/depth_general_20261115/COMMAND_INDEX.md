# Executed research and validation command index — 2026-11-15

This index is reproducibility evidence, not an extra work/CPU credit. Each exact argv/hash/deadline/output is in its start/result/log receipt. Guard fixture signal exits are expected test results, not mathematical worker failures. Scope/caps are documented in the separate protocols; per-process Lean caps are not generic process-tree caps. Publication commands occur only after journal stop and are recorded separately in publication_snapshot/chat.

| Tag | Category | Exit | Measured CPU seconds | Receipt |
|---|---|---:|---:|---|
| FULL-CHECK | mixed fullcheck | 0 | 14.106048999999999 | [FULL-CHECK-result.json](FULL-CHECK-result.json) |
| H01-COUNTER-R | individual Lean | 1 | 1.999415 | [H01-COUNTER-R-result.json](H01-COUNTER-R-result.json) |
| H01-COUNTER | individual Lean | 1 | 0.730253 | [H01-COUNTER-result.json](H01-COUNTER-result.json) |
| H02-TRANSPORT-R | individual Lean | 1 | 0.40402299999999997 | [H02-TRANSPORT-R-result.json](H02-TRANSPORT-R-result.json) |
| H02-TRANSPORT | individual Lean | 1 | 0.387959 | [H02-TRANSPORT-result.json](H02-TRANSPORT-result.json) |
| H05-SOURCE-COST | individual Lean | 0 | 0.38425299999999996 | [H05-SOURCE-COST-result.json](H05-SOURCE-COST-result.json) |
| H06-BUDGET | individual Lean | 0 | 0.8925299999999999 | [H06-BUDGET-result.json](H06-BUDGET-result.json) |
| H08-COMPLETION-R | individual Lean | 0 | 0.291242 | [H08-COMPLETION-R-result.json](H08-COMPLETION-R-result.json) |
| H08-COMPLETION | individual Lean | 1 | 0.292304 | [H08-COMPLETION-result.json](H08-COMPLETION-result.json) |
| H09-PRELOAD-R | individual Lean | 1 | 0.29356899999999997 | [H09-PRELOAD-R-result.json](H09-PRELOAD-R-result.json) |
| H09-PRELOAD | individual Lean | 1 | 0.305786 | [H09-PRELOAD-result.json](H09-PRELOAD-result.json) |
| H10-LOADER-R | individual Lean | 0 | 0.5890869999999999 | [H10-LOADER-R-result.json](H10-LOADER-R-result.json) |
| H10-LOADER | individual Lean | 1 | 0.567326 | [H10-LOADER-result.json](H10-LOADER-result.json) |
| H11-POSITIVE-R | individual Lean | 0 | 0.273637 | [H11-POSITIVE-R-result.json](H11-POSITIVE-R-result.json) |
| H11-POSITIVE | individual Lean | 1 | 0.273065 | [H11-POSITIVE-result.json](H11-POSITIVE-result.json) |
| METADATA-FINAL | metadata guard | 0 | 5.760422999999999 | [METADATA-FINAL-result.json](METADATA-FINAL-result.json) |
| bounded-preload-discovery | math worker | 0 | 0.030437999999999996 | [bounded-preload-discovery-result.json](bounded-preload-discovery-result.json) |
| bounded-preload-holdout | math worker | 0 | 0.096954 | [bounded-preload-holdout-result.json](bounded-preload-holdout-result.json) |
| counter-certificate | math worker | 0 | 0.029259999999999998 | [counter-certificate-result.json](counter-certificate-result.json) |
| guard-cpu | guard fixture | -24 | 1.003105 | [guard-cpu-result.json](guard-cpu-result.json) |
| guard-exec | guard fixture | 0 | 0.028179 | [guard-exec-result.json](guard-exec-result.json) |
| guard-fork | guard fixture | 0 | 0.028232 | [guard-fork-result.json](guard-fork-result.json) |
| guard-normal | guard fixture | 0 | 0.028988 | [guard-normal-result.json](guard-normal-result.json) |
| guard-wall | guard fixture | -9 | 0.025172999999999997 | [guard-wall-result.json](guard-wall-result.json) |
| height-free-discovery | math worker | 0 | 0.092884 | [height-free-discovery-result.json](height-free-discovery-result.json) |
| height-free-holdout | math worker | 0 | 0.103308 | [height-free-holdout-result.json](height-free-holdout-result.json) |
| preload-discovery | math worker | 0 | 0.037778 | [preload-discovery-result.json](preload-discovery-result.json) |
| preload-holdout | math worker | 0 | 0.712162 | [preload-holdout-result.json](preload-holdout-result.json) |
| reserve-trim-certificate | math worker | 0 | 0.034235 | [reserve-trim-certificate-result.json](reserve-trim-certificate-result.json) |
| two-free-preload-discovery | math worker | 0 | 0.03078 | [two-free-preload-discovery-result.json](two-free-preload-discovery-result.json) |
| two-free-preload-holdout | math worker | 0 | 0.096236 | [two-free-preload-holdout-result.json](two-free-preload-holdout-result.json) |

## Exact argv

### FULL-CHECK

```sh
./scripts/check.sh
```

### H01-COUNTER-R

```sh
lake env lean -j1 -M512 -o .lake/build/lib/lean/Recaman/InitialSFreePlateauCounterexample.olean Recaman/InitialSFreePlateauCounterexample.lean
```

### H01-COUNTER

```sh
lake env lean -j1 -M512 -o .lake/build/lib/lean/Recaman/InitialSFreePlateauCounterexample.olean Recaman/InitialSFreePlateauCounterexample.lean
```

### H02-TRANSPORT-R

```sh
lake env lean -j1 -M512 -o .lake/build/lib/lean/Recaman/HeightAdaptiveInitialSTrim.olean Recaman/HeightAdaptiveInitialSTrim.lean
```

### H02-TRANSPORT

```sh
lake env lean -j1 -M512 -o .lake/build/lib/lean/Recaman/HeightAdaptiveInitialSTrim.olean Recaman/HeightAdaptiveInitialSTrim.lean
```

### H05-SOURCE-COST

```sh
lake env lean -j1 -M512 -o .lake/build/lib/lean/Recaman/InitialSSourceCut.olean Recaman/InitialSSourceCut.lean
```

### H06-BUDGET

```sh
lake env lean -j1 -M512 -o .lake/build/lib/lean/Recaman/DepthSixClockTwoFourBudget.olean Recaman/DepthSixClockTwoFourBudget.lean
```

### H08-COMPLETION-R

```sh
lake env lean -j1 -M512 -o .lake/build/lib/lean/Recaman/SuffixSourceCompletion.olean Recaman/SuffixSourceCompletion.lean
```

### H08-COMPLETION

```sh
lake env lean -j1 -M512 -o .lake/build/lib/lean/Recaman/SuffixSourceCompletion.olean Recaman/SuffixSourceCompletion.lean
```

### H09-PRELOAD-R

```sh
lake env lean -j1 -M512 -o .lake/build/lib/lean/Recaman/FiniteSuffixPreloading.olean Recaman/FiniteSuffixPreloading.lean
```

### H09-PRELOAD

```sh
lake env lean -j1 -M512 -o .lake/build/lib/lean/Recaman/FiniteSuffixPreloading.olean Recaman/FiniteSuffixPreloading.lean
```

### H10-LOADER-R

```sh
lake env lean -j1 -M512 -o .lake/build/lib/lean/Recaman/BoundedHeightAreaLoader.olean Recaman/BoundedHeightAreaLoader.lean
```

### H10-LOADER

```sh
lake env lean -j1 -M512 -o .lake/build/lib/lean/Recaman/BoundedHeightAreaLoader.olean Recaman/BoundedHeightAreaLoader.lean
```

### H11-POSITIVE-R

```sh
lake env lean -j1 -M512 -o .lake/build/lib/lean/Recaman/TwoFreeHeightPositive.olean Recaman/TwoFreeHeightPositive.lean
```

### H11-POSITIVE

```sh
lake env lean -j1 -M512 -o .lake/build/lib/lean/Recaman/TwoFreeHeightPositive.olean Recaman/TwoFreeHeightPositive.lean
```

### METADATA-FINAL

```sh
bash scripts/check_research_registry.sh
```

### bounded-preload-discovery

```sh
/opt/homebrew/opt/python@3.14/bin/python3.14 /Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research/docs/data/depth_general_20261115/run_single.py --worker 1 /Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research/docs/data/depth_general_20261115/bounded_height_plateau_certificate.py discovery
```

### bounded-preload-holdout

```sh
/opt/homebrew/opt/python@3.14/bin/python3.14 /Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research/docs/data/depth_general_20261115/run_single.py --worker 1 /Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research/docs/data/depth_general_20261115/bounded_height_plateau_certificate.py holdout
```

### counter-certificate

```sh
/opt/homebrew/opt/python@3.14/bin/python3.14 /Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research/docs/data/depth_general_20261115/run_single.py --worker 1 /Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research/docs/data/depth_general_20261115/counter_certificate.py
```

### guard-cpu

```sh
/opt/homebrew/opt/python@3.14/bin/python3.14 /Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research/docs/data/depth_general_20261115/run_single.py --worker 1 /Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research/docs/data/depth_general_20261115/guard_fixture.py cpu
```

### guard-exec

```sh
/opt/homebrew/opt/python@3.14/bin/python3.14 /Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research/docs/data/depth_general_20261115/run_single.py --worker 1 /Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research/docs/data/depth_general_20261115/guard_fixture.py exec
```

### guard-fork

```sh
/opt/homebrew/opt/python@3.14/bin/python3.14 /Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research/docs/data/depth_general_20261115/run_single.py --worker 1 /Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research/docs/data/depth_general_20261115/guard_fixture.py fork
```

### guard-normal

```sh
/opt/homebrew/opt/python@3.14/bin/python3.14 /Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research/docs/data/depth_general_20261115/run_single.py --worker 1 /Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research/docs/data/depth_general_20261115/guard_fixture.py normal
```

### guard-wall

```sh
/opt/homebrew/opt/python@3.14/bin/python3.14 /Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research/docs/data/depth_general_20261115/run_single.py --worker 1 /Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research/docs/data/depth_general_20261115/guard_fixture.py wall
```

### height-free-discovery

```sh
/opt/homebrew/opt/python@3.14/bin/python3.14 /Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research/docs/data/depth_general_20261115/run_single.py --worker 2 /Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research/docs/data/depth_general_20261115/height_free_probe.py discovery
```

### height-free-holdout

```sh
/opt/homebrew/opt/python@3.14/bin/python3.14 /Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research/docs/data/depth_general_20261115/run_single.py --worker 2 /Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research/docs/data/depth_general_20261115/height_free_probe.py holdout
```

### preload-discovery

```sh
/opt/homebrew/opt/python@3.14/bin/python3.14 /Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research/docs/data/depth_general_20261115/run_single.py --worker 2 /Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research/docs/data/depth_general_20261115/preloaded_plateau_certificate.py discovery
```

### preload-holdout

```sh
/opt/homebrew/opt/python@3.14/bin/python3.14 /Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research/docs/data/depth_general_20261115/run_single.py --worker 2 /Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research/docs/data/depth_general_20261115/preloaded_plateau_certificate.py holdout
```

### reserve-trim-certificate

```sh
/opt/homebrew/opt/python@3.14/bin/python3.14 /Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research/docs/data/depth_general_20261115/run_single.py --worker 2 /Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research/docs/data/depth_general_20261115/reserve_trim_certificate.py
```

### two-free-preload-discovery

```sh
/opt/homebrew/opt/python@3.14/bin/python3.14 /Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research/docs/data/depth_general_20261115/run_single.py --worker 1 /Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research/docs/data/depth_general_20261115/two_free_plateau_certificate.py discovery
```

### two-free-preload-holdout

```sh
/opt/homebrew/opt/python@3.14/bin/python3.14 /Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research/docs/data/depth_general_20261115/run_single.py --worker 1 /Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research/docs/data/depth_general_20261115/two_free_plateau_certificate.py holdout
```

