# Post-application verification

Checked at `2026-09-24 01:43:30 JST (+0900)` from repository root
`/Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research`.

The pre-postapply report/source identities are preserved in
`prehash/PRE_POSTAPPLY_REPORTS.sha256`. In particular, the accepted report was
`552994e5bf3ead16e7a8fa72f2e09f2742e50fae9c715bc7c2041c5636b89239`
and COMMANDS was
`42e3b6fcba4e263b1ee2c86a0f2055822a2615785bddb18c2d4b1d938c69d7b3`.

## Byte comparison

Each live file was compared with `cmp -l` against the independently accepted
full proposal. All five commands exited 0 and produced empty stdout/stderr:

```text
docs/RESEARCH_WEEKLY_REPORT_2026-09-24.md
  = docs/data/issue73_20260924/slot0130/proposed_weekly_report_full.md
docs/HYPOTHESIS_CARD_2026-09-20_DONOR_WITHOUT_MINIMALITY.md
  = docs/data/issue73_20260924/slot0130/proposed_h02_card_full.md
docs/HYPOTHESIS_CARD_2026-09-20_SHORT_PREFIX_REDUCTION.md
  = docs/data/issue73_20260924/slot0130/proposed_h03_card_full.md
docs/HYPOTHESIS_CARD_2026-09-20_DONOR_LENGTH_BOUNDARY.md
  = docs/data/issue73_20260924/slot0130/proposed_h04_card_full.md
docs/HYPOTHESIS_CARD_2026-09-20_MINIMAL_DONOR_PATTERNS.md
  = docs/data/issue73_20260924/slot0130/proposed_h05_card_full.md
```

Raw comparison files are `raw/postapply_{weekly,h02,h03,h04,h05}_cmp.*`.

Live SHA-256 values:

```text
1fe6da74789cb2b91b3a03a5200a0afab3da983daee203766ee706b5aba28c1d  docs/RESEARCH_WEEKLY_REPORT_2026-09-24.md
d57af9c124d02ff0f493b32d4952c106fb610392f2b80eadf6ab7e9488dd7192  docs/HYPOTHESIS_CARD_2026-09-20_DONOR_WITHOUT_MINIMALITY.md
4a3aa8c303ea3cb5f5987121964db9dbf06b5daa437f0a3b60fef51736f81b60  docs/HYPOTHESIS_CARD_2026-09-20_SHORT_PREFIX_REDUCTION.md
74c6785c9433a335c9abe0249ee9fe82f1f1ae0bc1573624900f817bbab2845a  docs/HYPOTHESIS_CARD_2026-09-20_DONOR_LENGTH_BOUNDARY.md
d3d44f220e420b8d6d2773e57beacb67bc396b21044dc235b2a329b8921103a1  docs/HYPOTHESIS_CARD_2026-09-20_MINIMAL_DONOR_PATTERNS.md
```

Status check remains H-02/H-03/H-05 `CONJECTURED`; H-04 `REFUTED` only for
the nonminimal length-15 extension, with the same route recorded `STOPPED`.

## Source and process state

The research sources are unchanged from the audited bytes:

```text
bb12f35acc8e48c584cead52d675e36b034afda22f0f28ecfd245031f70fee85  Recaman/ShortTightDonorAvoidance.lean
a9540f5f891198ec91eefd73f62f9e35d4e59f645936dc3a349504e529b325de  Recaman/SS2OldestPattern.lean
```

No `fixed_controls`, `report_vacuity`, `harness_gate`, `scripts/check.sh`, or
TargetAxioms Lean process remained at the check. The independent auditor made
no repository edit; the five live documentation writes were the parent's
application of the approved full proposals.

Post-application verdict: **合格 for the limited wording, with H-02/H-03/H-05
overall still 未完了 and H-04 scoped exactly as above.**
