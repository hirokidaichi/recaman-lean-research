# Slot 01:00 worker report: Q/W baseline

## Conclusion first

`OBSERVED`. Independent adversarial audit accepted the finite `p=1..11` reproduction,
nonvacuity, and orientation controls. It left universal Q/W incomplete and returned automated
acceptance and Lean-entry readiness for correction. The exact finite definitions support a
non-vacuous, correctly oriented diagnostic for Q and local W on the completed recovery range;
no violation was found there. This is finite regression evidence, not a proof of Q or W.

The originally frozen exhaustive `p=1..15` run exceeded the 60-second slot limit before flushing
a completed-period record and was stopped with SIGINT. It is `INCOMPLETE`, not a pass. A separately
declared recovery run exhaustively completed `p=1..11`.

## Bounded question and acceptance

Question: do exact definitions and small regression cases support a non-vacuous, correctly
oriented falsifier for Q and local W, or reveal a concrete blocker/counterexample?

Frozen subprotocol before the first computation: enumerate every positive-sign-sum binary word for
`p=1..15`; the initial v1 implementation mistakenly searched the least P2 lag over
`1 <= d < p(p+1)`; construct the complete
supplied set U; verify Hall by all subsets; enumerate all tight B; test Q only for lag-11/SS=2 donors
and B-members of lag 3/7/11; test W only for tight B with lag 3/7 and actual w1 members. Separately
replay E-240 and the seven E-348 donor words. No p32/33 holdout was run.

After the timeout, the bound bug was found and a second subprotocol was declared with the correct
inclusive `1 <= d <= p(p+1)`, the same checks, and `p=1..11`. The reduced range is reported as
recovery regression only and does not convert the failed `p=1..15` run into a pass. The diagnostic
prints violation/applicability counters but exits 0 regardless of their values; therefore the
recorded counter values require inspection and are not an automated acceptance gate.

## Exact results

- E-240 replay: word `AAAASSAAAASAAASASS`, full `U=[2,7,8,11,13]`, Hall true, donor phase 7 has
  lag 11, word `ASSAAAASSAS`, SS=2, true oldest phase 14. The nonempty tight
  `B=[2,8,11,13]` has lags `[3,3,7,3]`, neighborhood `[4,5,10,17]`, contains the lag-7 word
  `SAAAASS`, and does not cover phase 14. Thus the known non-AAS tight set is reproduced. E-240 is a
  `PROVED-LEAN` certificate; the pure-AAS conjecture it certifies against is refuted.
  The pre-existing independent direct-summation script `verify_witnesses.py` reproduced the same
  donor, B, lags, neighborhood, tightness, and non-coverage in a separate run saved with this slot.
- Oldest orientation: true oldest offset is 10, while offset 11 is A, for d1, d2, d3, d6. A checker
  that unconditionally uses offset 11 is explicitly rejected for all four. Offsets for d4, d5, d7
  are 11 and contain S.
- Concrete periodic offset control: `p=15`, word `AAAASAAASASASSS`, donor phase 3 is d1 with least
  lag 11 and true oldest phase 8 (offset 10); the fixed-offset-11 phase is 7 and is A. Full U and
  Hall are used. There are four nonempty tight short B for this donor and none covers phase 8.
- Exhaustive `p=1..11`: 1,872 positive-sign-sum words, all 1,872 Hall-valid. Q applicability:
  52 donor occurrences, 104 tight B including the empty cases, 52 nonempty tight B, 0 violations.
  W applicability: 2,202 nonempty tight short B, 32 actual w1-member occurrences, 0 violations.
- Modulo/below-window witness for Q: `p=8`, word `SSAASAAA`, full U consists of phase 3 with least
  lag 11, word `ASSAAASAASS`, cover phases `{0,1,4}`, true oldest phase 0, and phase 7 with lag 3,
  word `AAS`, cover `{4}`. Hall holds. For donor 3, nonempty tight `B=[7]` has N(B)={4} and does not
  cover true oldest phase 0. This explicitly exercises repeated phases because 11>p.
- Nonempty W witness: `p=10`, word `SSAAAASAAA`, full U is phase 4 lag 3 (`AAS`, cover `{1}`), phase
  7 lag 7 (`SAAAASS`, cover `{0,1,6}`), phase 9 lag 3 (`AAS`, cover `{6}`). Hall holds and
  `B=[4,7,9]` is tight with neighborhood `{0,1,6}`. The w1 member is t=7 and e(t+1)=A.

No Q/W counterexample was found. The completed range is too small to establish either general
claim. Q does not establish general Gate T6. W does not assume a donor or Q, and the probe does not
use `aas_after_w1_forced` to derive its own future-A premise.

## Definitions and completeness

`past(word,u,d)` is newest-first at phases `(u-1),...,(u-d)` modulo p. P2 is exact mass 1 and
moment 0. Neighborhoods are sets of subtraction phases, so repeated clocks at p<d are identified
modulo p. `true_oldest` uses the largest offset containing S, then reduces its clock modulo p.
The lag scan uses the inclusive positive-period bound `d <= p(p+1)` from
`PeriodicSupplyBound.supply_lag_bound` and does not truncate U to short
lags. Hall is checked on full U by literal subset enumeration; Q/W B enumeration happens only after
that check.
The bridge from the card's positive `signSum` to positive backward period mass is
`ExactOrbitNonperiodicity.signSum_eq_period_mass`.

The direct checker works at phase level and therefore handles wrapping exactly. A future Lean proof
cannot apply E-348's integer-position coverage conclusion directly to phase membership when `p<11`:
phase equality supplies only a congruence, so an explicit periodic lift is required. Likewise, a
Nat expression such as the W sibling `u+2` needs a wrap bridge. These are identified formalization
obligations, not counterexamples to Q/W.

## Commands

```sh
date '+%Y-%m-%d %H:%M:%S %Z (%z)'
git rev-parse HEAD
git status --short
python3 -m py_compile experiments/issue73_20260920/baseline_q_w.py
python3 experiments/issue73_20260920/baseline_q_w.py | tee docs/data/issue73_20260920/baseline_q_w.txt
# interrupted after 60 seconds; exit 130
python3 -u experiments/issue73_20260920/baseline_q_w.py 11 | tee docs/data/issue73_20260920/baseline_q_w_p1_11.txt
python3 experiments/issue73_20260915/verify_witnesses.py | tee docs/data/issue73_20260920/existing_verify_witnesses.txt
sha256sum experiments/issue73_20260920/baseline_q_w.py docs/data/issue73_20260920/*
```

The main probe command itself prints the exact fixed E-240, p15 offset, p8 Q, and p10 W control
records before the exhaustive aggregate, so no omitted heredoc is required to reproduce them.

Source revision: `08c08565c743f39350c9b959e1df7d30aa1cae5d`. The probe and report are
uncommitted drafts. Exact file hashes are appended after the final freeze.

## Failures, uncertainty, next decision

The exhaustive Python subset implementation is too slow for `p=1..15` under this slot's 60-second
limit; its empty buffered output cannot identify the last completed internal case. This is a probe
performance blocker only, not mathematical evidence. No repair to Q or W was attempted.

Hypothesis-card status remains `CONJECTURED`. Strongest new evidence is the audit-accepted finite
`OBSERVED` regression only. Universal Q/W, an enforcing acceptance gate, and Lean entry remain
incomplete; the audit is not a full mandatory-gate pass. The next decision is to design and audit
an enforcing falsifier separately before any Lean work. Do not promote the card or register new
evidence from this slot. Do not run the p32/33 holdout, extend lag limits, or restart pure-AAS,
oldest-S-at-offset-11, or lag-15 routes.

## Audit disposition

The independent reviewer accepted finite reproduction/nonvacuity/orientation as `OBSERVED` and
returned universal Q/W as incomplete. The reviewer also returned the non-enforcing exit status and
Lean-entry readiness for correction. V1 documentary manifest
`f80203b7a55a1ce14770cbc661fb7233fe7afc7f2bc5b80737f5deda3f9875ae` is invalidated by
`V1_INVALIDATED.md`; only the v2 manifest is current.
