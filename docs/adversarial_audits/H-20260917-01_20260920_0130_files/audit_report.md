# H-20260917-01 slot 01:30 independent adversarial audit

## Conclusion first

**Procedural decision: returned. Stop recommendation applies only to this fixed-range gate
implementation branch.** The frozen ordinary CLI run reproduces the prior finite observation and
rejects the declared controls, failures, timeout, and a forged source. However, the output parser
accepts (a) more than eleven `PERIOD` records when an index is duplicated and (b) negative period
counters offset by another period. Both adversarial payloads reach `main()` and return 0. This
contradicts the frozen acceptance claim of "exactly eleven completed period rows" and permits an
internally impossible report to pass the output-validation contract.

This is not a counterexample to Q or W. Q and W remain `CONJECTURED`; the prior p=1..11 finite
result remains a limited `OBSERVED` regression; the first p=1..15 attempt remains incomplete; the
p=32,33 holdout remains unrun; and Lean entry remains returned. Do not register this gate version
as an accepted gate or use it to advance to Lean. The worker recorded that the single permitted
repair was already used before freeze, so the plan's stop recommendation is reached for this gate
branch, not for the mathematical research route.

## Target and roles

- Audit start: 2026-09-20 01:35:38 JST; report finalized after 01:41 JST.
- HEAD: `08c08565c743f39350c9b959e1df7d30aa1cae5d` (unchanged).
- Implementer: `/root/sol_20260920_gate0130`, GPT-5.6 Sol / xhigh.
- Independent adversarial auditor: `/root/sol_20260920_gate_audit0130`, GPT-5.6 Sol / xhigh.
- Frozen at 01:38:31 JST.
- Manifest SHA256: `308f9e7d5384c520538e7255a1e61e4ad0958370e6ca6178e78a455b8d6dc9cc`.
- Gate SHA256: `0c1e0da0666e6c3a574f12500c1c343fc99a2c36fcbe6f69c8d9d7f069e56b55`.
- Test SHA256: `ef84f29d892f24b3b3589e42dbfdd4c796bb9ef8c5bf5b786535df37281adac6`.
- Worker report SHA256: `1504c9c4f02abb1120f24945d0a4d6a2972a47ac5f8efb90ffdc0e4f61db64a0`.
- Baseline SHA256, pinned by the gate: `50b0e26f6a878e0c7ae229303026469a4f13c4fc0a21ee5b1ac591164145aea7`.
- Card hash supplied by the parent at audit start:
  `2f612148fc8eed38426f1cd76d1fd675fe4edc4b98a5a4639f915bf8997926ad`.

Research files were read-only. Auditor-created code and output are only under
`/tmp/recaman_gate_audit0130.Do7fNO/`.

## Exact accepted claim

The candidate purports to run the hash-pinned `baseline_q_w.py` at periods p=1..11, enumerating
every positive-sign-sum word and using the inclusive supply cutoff `1 <= d <= p(p+1)`, complete U,
all-subset Hall, and all tight subsets. Acceptance requires one exact protocol marker, exactly
eleven completed period rows, exact total counters (words/Hall words 1872; Q donors 52; Q tight
104 = 52 empty + 52 nonempty; Q violations 0; W short tight sets 2202; W applicable w1 instances
32; W violations 0), nonempty targets, fixed semantic controls, successful child completion, and
no timeout. The scope is finite regression only, not holdout or proof.

## Reproduction that passed

1. `shasum -a 256 -c docs/data/issue73_20260920/slot0130/SHA256SUMS`
   exited 0; all fourteen listed source/report/log files printed `OK`.
2. `python3 experiments/issue73_20260920/test_falsification_gate.py`
   exited 0: `Ran 4 tests in 5.520s`, `OK`.
3. `python3 experiments/issue73_20260920/falsification_gate.py --timeout 30`
   exited 0 with exactly
   `ACCEPT: fixed p=1..11 Q/W regression and all falsification controls passed`.
4. `python3 -u /tmp/recaman_gate_audit0130.Do7fNO/audit_attack.py`
   exited 0. A separately written enumerator reproduced exactly
   `{'words': 1872, 'hall_words': 1872, 'q_donors': 52, 'q_tight': 104,
   'q_nonempty': 52, 'q_violations': 0, 'w_tight': 2202,
   'w_occurrences': 32, 'w_violations': 0}`.

The gate is not merely accepting a hand-written total: the baseline source is SHA-pinned, a fake
child that printed the expected real output was rejected with exit 2 and
`REJECT: baseline hash mismatch: d2cb...57d2c`; an actual temporary child exiting 9 was rejected
with exit 2 and `REJECT: baseline exited 9`; and `--timeout 0` was rejected with exit 2 and
`REJECT: baseline timed out after 0s`.

The six declared fault modes were independently sent through `evaluate`: dropped SS=2, dropped
tightness, empty target, wrong oldest offset, injected violation, and incomplete output each raised
`GateFailure`. The saved worker rejection logs agree with these messages.

## Breaking attacks

### 1. Duplicate completed period is accepted

The parser assigns each row to `period_rows[int(parts[1])]`; a duplicate overwrites rather than
being counted. Appending a second, identical real `PERIOD 1` row leaves the key set 1..11 and all
sums unchanged. `evaluate` accepted it. With `run_baseline` mocked only at its subprocess boundary
to return this payload, the unmodified frozen `main([])` printed the ordinary `ACCEPT` line and
returned 0.

Thus the parser accepts twelve `PERIOD` records while the frozen report says it requires exactly
eleven. The pinned normal baseline does not generate the duplicate; this is a counterexample to the
parser/acceptance contract, not evidence that the ordinary frozen CLI currently emits duplicates.

### 2. Negative counts can be canceled and accepted

Starting from the real output, the auditor changed period 1 `words` to `-1` and increased period 2
`words` by the corresponding amount so the summed total stayed 1872. The parser checks only the
final exact sum; it does not require an exact row schema, integer types, or nonnegative counts.
`evaluate` accepted the payload, and the same subprocess-boundary mock made frozen `main([])` print
`ACCEPT` and return 0.

Again, the hash-pinned normal baseline does not produce negative counts. This demonstrates that the
gate does not reliably reject an injected internally impossible period report, so the advertised
enforcing output-validation boundary is incomplete.

### 3. Witness line content is not validated (lower severity)

Replacing the real `FIRST_Q_NONEMPTY ...` payload by `FIRST_Q_NONEMPTY garbage` is accepted because
only the prefix's existence is checked. The fixed p8/p10 controls are nevertheless recomputed from
the hash-pinned baseline functions, so this does not defeat those semantic assertions. It remains a
report-integrity gap to address in any future redesign, not the primary return reason.

## Independent semantic controls

The independent enumerator uses its own numeric-history representation and least-lag loop; it does
not import the baseline. It confirmed complete U, minimality by first hit, all-subset Hall, modular
phases, the specified B, and neighborhoods:

- E-240 p18 `AAAASSAAAASAAASASS`: sign sum 6; full U lags
  `(2:3, 7:11, 8:3, 11:7, 13:3)`; donor 7 window `ASSAAAASSAS`, SS=2,
  true-oldest offset 11/phase 14; B `(2,8,11,13)`, N `(4,5,10,17)`, tight and non-AAS.
  It is admitted as the intended negative control and is not a Q counterexample.
- Q p8 `SSAASAAA`: full U `(3:11,7:3)`, Hall; donor 3 has true-oldest phase 0;
  B `(7)`, N `(4)`, hence Q is applicable and satisfied.
- W p10 `SSAAAASAAA`: full U `(4:3,7:7,9:3)`, Hall; B=U,
  N `(0,1,6)`, w1 member 7, next symbol A. W is applicable and satisfied.
- Wrong-offset p15 `AAAASAAASASASSS`: donor 3 is d1 at lag 11; true oldest is offset
  10/phase 8, while offset 11 selects phase 7 whose bit is A.
- Weakened-Q p12 `AAAASAAASSSS`: donor 3 has lag 11, SS=3, true oldest phase 4;
  B `(2,5,7)`, N `(4,10,11)`, tight. Dropping SS=2 exposes a violation but does not refute Q.
- Weakened-W p8 `SSAAAASA`: full U `(4:3,7:7)`, Hall; B `(7)`,
  N `(0,1,6)`, next symbol S, and `|N|=3 != 1`. Dropping tightness exposes a violation but does
  not refute W.

The slot 01:30 correction addendum is accurate: the original p8/p10 output showed U and aggregate
counters but not the selected B, N(B), and next sign; the new gate asserts those details directly.

## Scope, dependencies, and unresolved obligations

- These finite checks do not prove Q or W and do not imply arbitrary p, arbitrary lag, Gate T6,
  standard-orbit reachability, or surjectivity.
- E-359 supplies only the stated periodic/Hall/tight short-lag reduction. The bridges from full U
  and minimal lag into E-359/E-348, and from phase congruence to integer-clock positions, remain
  obligations.
- E-351 `aas_after_w1_forced` already assumes the future A sign and membership/lag facts; using it
  to prove W would be circular.
- The card's one-at-a-time weakenings and periodic-boundary transfer remain incomplete.
- No Lean files changed. This slot prohibited Lean work, and therefore `report_vacuity.py`, Lean
  lint, and `./scripts/check.sh` were correctly not run. No new theorem, defined Prop, wrapper,
  arithmetic-only result, registry row, frontier entry, proof-map entry, or protected claim exists
  to audit here.

## Final procedural decision

- Frozen gate candidate: **returned**.
- Gate implementation branch: **stop recommended**, because the predeclared single repair was used
  before freeze and the frozen result has two further acceptance-contract counterexamples.
- Ordinary p=1..11 finite data: **limited pass / OBSERVED reproduction maintained**.
- Q/W mathematical status: **CONJECTURED, neither refuted nor proved**.
- Lean entry and evidence registration: **not allowed**.
- Any future gate is a new target version and requires a new independent audit; this report cannot
  be reused as approval.
