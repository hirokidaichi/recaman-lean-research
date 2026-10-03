# Slot 01:30 falsification-gate report

## Pre-implementation freeze

- Bounded question: can an enforcing, fixed-range regression gate run the frozen real
  `baseline_q_w.py` computation and reject known errors with a nonzero exit status?
- Input range: all positive-sign-sum words at periods `p=1..11`; least-supply search
  `1 <= d <= p(p+1)`; complete U; literal all-subset Hall and tight-B enumeration.
  The gate launches the baseline as a subprocess with an explicit 30-second timeout.
- Acceptance: successful subprocess completion; the exact protocol marker; exactly eleven
  completed period rows; 1,872 words and Hall words; Q donors 52, tight B 104 = empty 52 +
  nonempty 52, violations 0; W short tight B 2,202, applicable w1 occurrences 32,
  violations 0; and independently recomputed fixed controls with nonempty B and exact
  neighborhoods/next symbols.
- Required rejection: the SS=2-dropped Q counterexample, tightness-dropped W counterexample,
  zero applicable targets, fixed offset 11 in place of the true oldest S, an injected
  violation, a failed child process, timeout, or incomplete output must all return nonzero.
- Stopping condition: one implementation repair is allowed after adversarial failure. A second
  failure stops this branch with a stop recommendation. No range extension, holdout, Lean,
  registry, frontier, proof-map, or mathematical-claim change is allowed in this slot.
- Evidence ceiling: a passing gate is only fixed-range `OBSERVED` regression evidence. It is
  not a proof of Q, W, Gate T6, or any orbit claim. Independent audit is required before use.

## Result

`OBSERVED`, pending independent audit. The fixed-range gate completed with exit 0. It ran the
frozen baseline rather than accepting a hand-written result payload, required all eleven period
records, recomputed detailed controls through the baseline's definitions, and enforced exact
nonzero applicability and zero violations. The following deliberately damaged executions were
all rejected with exit 2: dropped SS=2, dropped tightness, empty target, fixed oldest offset 11,
injected violation, missing period 11, and timeout.

This does not prove Q or W. Both remain `CONJECTURED`; Lean entry remains returned. No holdout,
range extension, Lean edit, registry edit, or mathematical claim was made.

## Correction addendum to slot 01:00

The slot 01:00 report's phrase that the p8/p10 controls printed their details was too strong.
Those baseline output rows printed U and aggregate counters, but did not directly print the
selected B, N(B), and next sign. The independent audit's supplemental assertions separately
verified those detail values. This gate now recomputes and asserts them directly: p8 Q uses
`B=[7]`, `N={4}`; p10 W uses `B=[4,7,9]`, `N={0,1,6}`, w1 member `u=7`, next sign A.

## Files

- `experiments/issue73_20260920/falsification_gate.py`: enforcing subprocess gate and fixed
  detailed controls.
- `experiments/issue73_20260920/test_falsification_gate.py`: real-run success test, six fault
  rejections, child-nonzero rejection, and timeout rejection.
- `docs/data/issue73_20260920/slot0130/falsification_gate.log`: raw baseline output plus gate
  acceptance line.
- `docs/data/issue73_20260920/slot0130/test_falsification_gate.log`: unit-test output.
- `docs/data/issue73_20260920/slot0130/reject_*.log`: raw rejection messages for six fault modes
  and explicit timeout.
- `docs/data/issue73_20260920/slot0130/SHA256SUMS`: frozen source/report/log hashes.

## Commands and exit status

```sh
python3 -m py_compile experiments/issue73_20260920/falsification_gate.py experiments/issue73_20260920/test_falsification_gate.py
# exit 0
python3 experiments/issue73_20260920/test_falsification_gate.py
# exit 0; four tests, including one real p=1..11 run
python3 experiments/issue73_20260920/falsification_gate.py --timeout 30 --emit-baseline
# exit 0
python3 experiments/issue73_20260920/falsification_gate.py --timeout 30 --simulate-fault FAULT
# exit 2 for each of: drop-ss2, drop-tightness, empty-target,
# wrong-oldest-offset, inject-violation, incomplete-output
python3 experiments/issue73_20260920/falsification_gate.py --timeout 0
# exit 2: explicit timeout rejection
```

HEAD is `08c08565c743f39350c9b959e1df7d30aa1cae5d`. Seed is unused; enumeration is exhaustive and
deterministic. The baseline source hash remains the frozen
`50b0e26f6a878e0c7ae229303026469a4f13c4fc0a21ee5b1ac591164145aea7`.

## Strongest evidence, failures, and next decision

Strongest evidence is only the reproducible `OBSERVED` fixed p=1..11 regression: 1,872 positive
words, 52 Q donors, 104 Q tight cases (52 empty and 52 nonempty), zero Q violations, 2,202 short
tight W sets, 32 applicable w1 occurrences, and zero W violations. The gate also rejects the real
p12 SS=3 weakened-Q counterexample and real p8 non-tight weakened-W counterexample.

The first implementation passed its initial tests. One predeclared repair was then used before
freeze to add explicit child-nonzero/timeout tests, make incomplete output remove a period row,
and preserve emitted raw baseline output. No second repair is available; another adversarial break
should stop this branch with a stop recommendation.

Remaining uncertainty: independent audit has not yet accepted this target version. The universal
Q/W statements, formal bridges, and Lean readiness remain unresolved. Next decision is independent
adversarial audit of the frozen hashes. Do not register evidence or proceed to Lean before that
audit.
