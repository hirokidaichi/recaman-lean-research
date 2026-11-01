# Reproducibility run index — 2026-10-26

Exact original argv/start metadata and stdout are immutable per-tag records. A few derived discovery JSON summaries were regenerated for a counterexample witness; use the separate original stdout log when comparing the initial run. Retained source hashes identify the exact version.

The supported mathematical-worker contract is one reviewed cooperative Python process, no descendants, shared thread CPU limit, wall/deadline kill, exact wait4 CPU. It is not a generic process-tree or adversarial security guarantee.

## Mathematical workers and guard validation

| Tag | Actual start JST | Worker CPU s | Exit | Exact worker source SHA | Source bytes | stdout |
| --- | --- | --- | --- | --- | --- | --- |
| guard-normal | 06:10:02.806698+09:00 | 0.034526 | 0 | 439e58e539878d2e95f11922de42721e3f0ebd9735832cd920d4b87ff54ae1da | [guard_fixture.py](guard_fixture.py) | [log](guard-normal.log) |
| guard-fork | 06:10:02.921592+09:00 | 0.029657 | 0 | 439e58e539878d2e95f11922de42721e3f0ebd9735832cd920d4b87ff54ae1da | [guard_fixture.py](guard_fixture.py) | [log](guard-fork.log) |
| guard-exec | 06:10:03.001128+09:00 | 0.029581 | 0 | 439e58e539878d2e95f11922de42721e3f0ebd9735832cd920d4b87ff54ae1da | [guard_fixture.py](guard_fixture.py) | [log](guard-exec.log) |
| guard-wall | 06:10:03.079444+09:00 | 0.025565 | -9 | 439e58e539878d2e95f11922de42721e3f0ebd9735832cd920d4b87ff54ae1da | [guard_fixture.py](guard_fixture.py) | [log](guard-wall.log) |
| guard-cpu | 06:10:03.309493+09:00 | 1.002354 | -24 | 439e58e539878d2e95f11922de42721e3f0ebd9735832cd920d4b87ff54ae1da | [guard_fixture.py](guard_fixture.py) | [log](guard-cpu.log) |
| free-gap-discovery | 06:12:33.210318+09:00 | 0.114283 | 0 | 5ad0bda170588a4613694441c6a5fc90fc12d5479bd036f810d1f036c0e0d2c7 | [free_gap_discovery.py](free_gap_discovery.py) | [log](free-gap-discovery.log) |
| free-gap-holdout | 06:12:41.996164+09:00 | 0.228558 | 0 | 1795428c538ad352205e0d1df8be1c3bfa48e831a525bedde630cf3d5db41003 | [free_gap_holdout.py](free_gap_holdout.py) | [log](free-gap-holdout.log) |
| a-run-discovery | 06:14:59.748380+09:00 | 0.090767 | 0 | c19f3b5d80cae6ed8a1cda725c365962a94e97db160d946056b99c6da777afb3 | [a_run_discovery.py](a_run_discovery.py) | [log](a-run-discovery.log) |
| a-run-holdout | 06:15:05.950044+09:00 | 0.041943 | 0 | 20a5bd0b4542d90f95a6598bbd927bf6e3aa202c99f194572d14919d8862e60b | [a_run_holdout.py](a_run_holdout.py) | [log](a-run-holdout.log) |
| two-run-discovery | 06:27:35.596859+09:00 | 0.081289 | 0 | b7969f452920f015813646dd6b373622212946477f76262442eeb458240b42ab | [two_run_discovery.py](two_run_discovery.py) | [log](two-run-discovery.log) |
| two-run-holdout | 06:27:42.969528+09:00 | 0.048599 | 0 | d891c3921b30529ed2ead8be9d5896679b1a54ab5d208c79ab634fc1210ce5bc | [two_run_holdout.py](two_run_holdout.py) | [log](two-run-holdout.log) |
| run-budget-discovery | 06:38:05.642597+09:00 | 0.112364 | 0 | 5931e5c7773ea8174e4267f174aa4796c4f46cf721607c5eb503d687ddc39dd4 | [run_budget_discovery.py](run_budget_discovery.py) | [log](run-budget-discovery.log) |
| run-budget-holdout | 06:38:22.570573+09:00 | 0.040943 | 0 | a4cf7c0268d10cab2a6457e376401449c7c69608f48eacfd789d09019b4aad28 | [run_budget_holdout.py](run_budget_holdout.py) | [log](run-budget-holdout.log) |
| old-ray-discovery | 06:54:21.876318+09:00 | 0.059063 | 0 | 14193cdefb458e96d2c4783c9058b1b6f792b967e074cd404a62effbf0c2e3bc | [old_ray_discovery.py](old_ray_discovery.py) | [log](old-ray-discovery.log) |
| old-ray-holdout | 06:54:27.254311+09:00 | 0.126831 | 0 | 997bb4e5769868a7acd317066ff428f267e3db70bc4193760ee99fc01fd79768 | [old_ray_holdout.py](old_ray_holdout.py) | [log](old-ray-holdout.log) |
| old-tail-discovery | 07:02:38.541259+09:00 | 0.101218 | 0 | 8a560cf4540318c2b9877c53283bbeec71a29a10f80bd50d933fea19f3ecad2c | [old_tail_discovery.py](old_tail_discovery.py) | [log](old-tail-discovery.log) |
| old-tail-holdout | 07:03:05.850724+09:00 | 0.064324 | 0 | 6fec3daf4a0d09b3f7b502e88718f4d30a649a46a6de08a0de0c691433bd00e6 | [old_tail_holdout.py](old_tail_holdout.py) | [log](old-tail-holdout.log) |
| old-budget-graph | 07:12:18.593543+09:00 | 0.685781 | 0 | 6ee75a2c030b4e7eeafd8dbae3d9007ac3d8d871d99bf3694dc48d80f4b95c5a | [old_budget_graph.py](old_budget_graph.py) | [log](old-budget-graph.log) |
| old-budget-independent | 07:12:28.732368+09:00 | 0.825756 | 0 | c79fb9e8568ebdbe1d28edfdf0d0d84ee81e47bff4a7e2e107a59646c1a7bc97 | [old_budget_independent.py](old_budget_independent.py) | [log](old-budget-independent.log) |
| three-run-discovery | 07:31:17.387661+09:00 | 0.317576 | 0 | 22f31477ecdf51dad06bc3db4dd5c28d4ef37b324593e4865841113b5b91e9ae | [three_run_discovery.py](three_run_discovery.py) | [log](three-run-discovery.log) |
| three-run-holdout | 07:31:21.901182+09:00 | 0.174138 | 0 | f5304f900d8f95055c680e89e3849191e201bc510157c80021f2e3f7968d8886 | [three_run_holdout.py](three_run_holdout.py) | [log](three-run-holdout.log) |
| three-source-discovery | 07:34:18.880071+09:00 | 0.823823 | 0 | d8cda12871d0faff7ec81deb7343ae05063fb1d17131208411c0be81224675d7 | [three_source_discovery_v1.py.txt](three_source_discovery_v1.py.txt) | [log](three-source-discovery.log) |
| three-source-holdout | 07:34:24.348830+09:00 | 0.051491 | 0 | d88c0b41098a59c2737dc30a5bc54e67b5e8030822ba8339645fcb93ec0132ef | [three_source_holdout.py](three_source_holdout.py) | [log](three-source-holdout.log) |
| three-source-repair | 07:34:57.189594+09:00 | 0.834077 | 0 | 2f360da21d06f92dc30fac30b5e949c0eef12d951bda998d951e3afa495f0208 | [three_source_discovery.py](three_source_discovery.py) | [log](three-source-repair.log) |
| three-source-replay | 07:35:43.629842+09:00 | 0.036114 | 0 | d93eefd073104c683dd0c6dc0d3661bdf313368ebeb2f12c63f2449e546481a3 | [three_source_replay_v1.py.txt](three_source_replay_v1.py.txt) | [log](three-source-replay.log) |
| three-source-actual-audit | 07:40:36.478395+09:00 | 0.039695 | 0 | 2ad6df04aeb1a8e7d172a63a133812a81ef74d99b14eec55137c619da014950d | [three_source_replay.py](three_source_replay.py) | [log](three-source-actual-audit.log) |

Expected guard wall/CPU kills are tests of stopping, not failed mathematical probes. All mathematical workers completed with exit0.

## Exact worker argv

### guard-normal

```sh
/opt/homebrew/opt/python@3.14/bin/python3.14 /Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research/docs/data/free_gap_20261026/run_single.py --worker 1 /Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research/docs/data/free_gap_20261026/guard_fixture.py normal
```

### guard-fork

```sh
/opt/homebrew/opt/python@3.14/bin/python3.14 /Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research/docs/data/free_gap_20261026/run_single.py --worker 1 /Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research/docs/data/free_gap_20261026/guard_fixture.py fork
```

### guard-exec

```sh
/opt/homebrew/opt/python@3.14/bin/python3.14 /Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research/docs/data/free_gap_20261026/run_single.py --worker 1 /Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research/docs/data/free_gap_20261026/guard_fixture.py exec
```

### guard-wall

```sh
/opt/homebrew/opt/python@3.14/bin/python3.14 /Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research/docs/data/free_gap_20261026/run_single.py --worker 1 /Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research/docs/data/free_gap_20261026/guard_fixture.py wall
```

### guard-cpu

```sh
/opt/homebrew/opt/python@3.14/bin/python3.14 /Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research/docs/data/free_gap_20261026/run_single.py --worker 1 /Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research/docs/data/free_gap_20261026/guard_fixture.py cpu
```

### free-gap-discovery

```sh
/opt/homebrew/opt/python@3.14/bin/python3.14 /Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research/docs/data/free_gap_20261026/run_single.py --worker 10 /Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research/docs/data/free_gap_20261026/free_gap_discovery.py
```

### free-gap-holdout

```sh
/opt/homebrew/opt/python@3.14/bin/python3.14 /Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research/docs/data/free_gap_20261026/run_single.py --worker 10 /Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research/docs/data/free_gap_20261026/free_gap_holdout.py
```

### a-run-discovery

```sh
/opt/homebrew/opt/python@3.14/bin/python3.14 /Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research/docs/data/free_gap_20261026/run_single.py --worker 10 /Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research/docs/data/free_gap_20261026/a_run_discovery.py
```

### a-run-holdout

```sh
/opt/homebrew/opt/python@3.14/bin/python3.14 /Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research/docs/data/free_gap_20261026/run_single.py --worker 10 /Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research/docs/data/free_gap_20261026/a_run_holdout.py
```

### two-run-discovery

```sh
/opt/homebrew/opt/python@3.14/bin/python3.14 /Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research/docs/data/free_gap_20261026/run_single.py --worker 10 /Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research/docs/data/free_gap_20261026/two_run_discovery.py
```

### two-run-holdout

```sh
/opt/homebrew/opt/python@3.14/bin/python3.14 /Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research/docs/data/free_gap_20261026/run_single.py --worker 10 /Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research/docs/data/free_gap_20261026/two_run_holdout.py
```

### run-budget-discovery

```sh
/opt/homebrew/opt/python@3.14/bin/python3.14 /Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research/docs/data/free_gap_20261026/run_single.py --worker 10 /Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research/docs/data/free_gap_20261026/run_budget_discovery.py
```

### run-budget-holdout

```sh
/opt/homebrew/opt/python@3.14/bin/python3.14 /Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research/docs/data/free_gap_20261026/run_single.py --worker 10 /Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research/docs/data/free_gap_20261026/run_budget_holdout.py
```

### old-ray-discovery

```sh
/opt/homebrew/opt/python@3.14/bin/python3.14 /Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research/docs/data/free_gap_20261026/run_single.py --worker 10 /Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research/docs/data/free_gap_20261026/old_ray_discovery.py
```

### old-ray-holdout

```sh
/opt/homebrew/opt/python@3.14/bin/python3.14 /Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research/docs/data/free_gap_20261026/run_single.py --worker 10 /Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research/docs/data/free_gap_20261026/old_ray_holdout.py
```

### old-tail-discovery

```sh
/opt/homebrew/opt/python@3.14/bin/python3.14 /Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research/docs/data/free_gap_20261026/run_single.py --worker 10 /Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research/docs/data/free_gap_20261026/old_tail_discovery.py
```

### old-tail-holdout

```sh
/opt/homebrew/opt/python@3.14/bin/python3.14 /Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research/docs/data/free_gap_20261026/run_single.py --worker 10 /Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research/docs/data/free_gap_20261026/old_tail_holdout.py
```

### old-budget-graph

```sh
/opt/homebrew/opt/python@3.14/bin/python3.14 /Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research/docs/data/free_gap_20261026/run_single.py --worker 15 /Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research/docs/data/free_gap_20261026/old_budget_graph.py
```

### old-budget-independent

```sh
/opt/homebrew/opt/python@3.14/bin/python3.14 /Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research/docs/data/free_gap_20261026/run_single.py --worker 15 /Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research/docs/data/free_gap_20261026/old_budget_independent.py
```

### three-run-discovery

```sh
/opt/homebrew/opt/python@3.14/bin/python3.14 /Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research/docs/data/free_gap_20261026/run_single.py --worker 10 /Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research/docs/data/free_gap_20261026/three_run_discovery.py
```

### three-run-holdout

```sh
/opt/homebrew/opt/python@3.14/bin/python3.14 /Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research/docs/data/free_gap_20261026/run_single.py --worker 10 /Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research/docs/data/free_gap_20261026/three_run_holdout.py
```

### three-source-discovery

```sh
/opt/homebrew/opt/python@3.14/bin/python3.14 /Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research/docs/data/free_gap_20261026/run_single.py --worker 5 /Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research/docs/data/free_gap_20261026/three_source_discovery.py
```

### three-source-holdout

```sh
/opt/homebrew/opt/python@3.14/bin/python3.14 /Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research/docs/data/free_gap_20261026/run_single.py --worker 5 /Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research/docs/data/free_gap_20261026/three_source_holdout.py
```

### three-source-repair

```sh
/opt/homebrew/opt/python@3.14/bin/python3.14 /Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research/docs/data/free_gap_20261026/run_single.py --worker 3 /Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research/docs/data/free_gap_20261026/three_source_discovery.py
```

### three-source-replay

```sh
/opt/homebrew/opt/python@3.14/bin/python3.14 /Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research/docs/data/free_gap_20261026/run_single.py --worker 2 /Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research/docs/data/free_gap_20261026/three_source_replay.py
```

### three-source-actual-audit

```sh
/opt/homebrew/opt/python@3.14/bin/python3.14 /Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research/docs/data/free_gap_20261026/run_single.py --worker 2 /Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research/docs/data/free_gap_20261026/three_source_replay.py
```

The argv above is the exact launched child argv, including the frozen CPU limit. To replay an amended source, select the retained bytes with the matching SHA from the table; do not silently run the current file under an earlier source hash. The public bounded launcher is `python3 run_single.py --tag <new-tag> --cpu <cap> --wall <cap> <matching-source>`.

## Lean validation attempts

These are validation, not computational mathematical discovery. Per-process60CPU/90wall with process-group8:00 deadline is not a cumulative tree cap. The recorded total is incomplete because initial unwrapped validation/build calls are not all measured. Intermediate failed tactic versions are not all retained; final active proof sources and every executed mathematical Python worker are retained.

| Tag | Actual start JST | Recorded CPU s | Exit | Log |
| --- | --- | --- | --- | --- |
| run-key-lean-2 | 06:17:26.176209+09:00 | 0.564529 | 1 | [log](run-key-lean-2.log) |
| run-key-lean-3 | 06:18:05.728099+09:00 | 0.548736 | 0 | [log](run-key-lean-3.log) |
| run-key-lean-4 | 06:18:49.276970+09:00 | 0.590066 | 1 | [log](run-key-lean-4.log) |
| run-key-lean-5 | 06:19:07.108146+09:00 | 0.569058 | 0 | [log](run-key-lean-5.log) |
| check-run-keys | 06:20:27.983602+09:00 | 7.545119 | 0 | [log](check-run-keys.log) |
| two-run-lean-1 | 06:28:43.320686+09:00 | 0.448682 | 1 | [log](two-run-lean-1.log) |
| two-run-lean-2 | 06:29:18.155776+09:00 | 0.560049 | 1 | [log](two-run-lean-2.log) |
| two-run-lean-3 | 06:29:34.047702+09:00 | 0.635995 | 0 | [log](two-run-lean-3.log) |
| two-run-lean-4 | 06:30:21.233114+09:00 | 1.068277 | 1 | [log](two-run-lean-4.log) |
| two-run-lean-5 | 06:30:40.984086+09:00 | 1.064495 | 0 | [log](two-run-lean-5.log) |
| two-run-lean-6 | 06:31:31.224929+09:00 | 1.149448 | 0 | [log](two-run-lean-6.log) |
| check-two-run | 06:35:55.636626+09:00 | 8.168934 | 0 | [log](check-two-run.log) |
| run-budget-lean-1 | 06:39:38.248201+09:00 | 0.569973 | 1 | [log](run-budget-lean-1.log) |
| run-budget-lean-2 | 06:39:57.856543+09:00 | 0.555826 | 0 | [log](run-budget-lean-2.log) |
| run-budget-lean-3 | 06:40:40.525550+09:00 | 0.720134 | 0 | [log](run-budget-lean-3.log) |
| check-run-budget | 06:46:15.521870+09:00 | 7.776515 | 0 | [log](check-run-budget.log) |
| block-old-lean-1 | 06:56:57.931253+09:00 | 0.360923 | 1 | [log](block-old-lean-1.log) |
| block-old-lean-2 | 06:57:16.210362+09:00 | 0.444345 | 0 | [log](block-old-lean-2.log) |
| block-old-lean-3 | 06:58:17.782495+09:00 | 0.720568 | 1 | [log](block-old-lean-3.log) |
| block-old-lean-4 | 06:58:38.923454+09:00 | 0.708665 | 0 | [log](block-old-lean-4.log) |
| block-old-lean-5 | 07:03:05.982408+09:00 | 0.793810 | 0 | [log](block-old-lean-5.log) |
| block-old-lean-6 | 07:04:34.768317+09:00 | 1.022859 | 1 | [log](block-old-lean-6.log) |
| block-old-lean-7 | 07:05:13.716496+09:00 | 0.925975 | 0 | [log](block-old-lean-7.log) |
| block-old-lean-8 | 07:07:03.409957+09:00 | 1.095027 | 0 | [log](block-old-lean-8.log) |
| check-block-old | 07:09:13.181112+09:00 | 9.249989 | 0 | [log](check-block-old.log) |
| one-run-lean-1 | 07:21:11.013158+09:00 | 1.438265 | 1 | [log](one-run-lean-1.log) |
| one-run-lean-2 | 07:21:24.302405+09:00 | 1.672091 | 1 | [log](one-run-lean-2.log) |
| one-run-lean-3 | 07:21:29.664261+09:00 | 1.401508 | 0 | [log](one-run-lean-3.log) |
| check-one-run | 07:22:20.476554+09:00 | 9.224056 | 0 | [log](check-one-run.log) |
| r3-projection-check | 07:25:46.813648+09:00 | 17.421937 | 0 | [log](r3-projection-check.log) |
| two-gap-lean-1 | 07:26:58.979614+09:00 | 19.351080 | 1 | [log](two-gap-lean-1.log) |
| two-gap-lean-2 | 07:27:32.234814+09:00 | 19.388534 | 1 | [log](two-gap-lean-2.log) |
| two-gap-lean-3 | 07:28:11.846973+09:00 | 19.362589 | 0 | [log](two-gap-lean-3.log) |
| check-two-gap | 07:29:16.816263+09:00 | 26.859945 | 0 | [log](check-two-gap.log) |
| three-source-lean | 07:35:43.730891+09:00 | 19.492967 | 0 | [log](three-source-lean.log) |
| check-final-math | 07:39:00.242742+09:00 | 27.578480 | 0 | [log](check-final-math.log) |

## Evidence routing

| Evidence | Main retained artifact | Separate evidence limitation |
| --- | --- | --- |
| E408 PROVED-LEAN | RunSupplyKeys + A_RUN_PROTOCOL / run-key logs | S count is not free count |
| E409 PROVED-LEAN | TwoRunSupply + TWO_RUN_PROTOCOL / two-run logs | Whole-history two-run shape; M,m>=1 for bound |
| E410 PROVED-LEAN | RunSupplyBudget + RUN_BUDGET_PROTOCOL | One A-only ray, no cross-S one-use assertion |
| E411 PROVED-LEAN | BlockOldRay + OLD_RAY/OLD_TAIL_PROTOCOL | Same old prefix, S>=3 for arbitrary tail |
| E412 COMPUTED | old-budget-certificate/independent JSON | Zero projected reduction, no actual-to-credit Lean simulation/initial kernel |
| E413/E414 PROVED-LEAN | BlockOldRay, one-/two-gap logs and G5 | Single/two A-run shape, original base retained |
| E415 REFUTED | three-source-replay, literal ledger, four-clock Lean check | Auxiliary local-count bound only; actual ledger is COMPUTED |
| E416 PROVED-PAPER | C1_RUN_BUDGET note | Three-run gluing/reduction not Lean, no human review |

[Full source preservation](final-source-manifest.json), [resources](final-resource-summary.json), [semantic audit](SEMANTIC_AUDIT.md), [consistency](final-consistency.json). Journal time is separate and never formed by adding CPU.
