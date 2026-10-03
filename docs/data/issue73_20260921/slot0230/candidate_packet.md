# H-20260921-01 candidate packet

## Conclusion first

`short_supply_donor_deletion` is a meaningful, nonvacuous deletion theorem only for the explicitly
restricted class in which **every member of `U`** is a distinct in-range current-A phase with a
minimal P2 window of lag 3, 7, or 11. It is not general T6 and says nothing about an unrestricted
complete all-lag supply set. The exact proof is a direct composition of registered Q
(`short_tight_avoids_ss2_donor`),
short Hall, and pre-existing generic tight/slack deletion lemmas. By the predeclared acceptance test,
it contributes no new mathematical input. Independent audit is pending; no registration or promotion
is proposed.

## Frozen target

- HEAD: `08c08565c743f39350c9b959e1df7d30aa1cae5d`
- dirty source SHA-256:
  `bb12f35acc8e48c584cead52d675e36b034afda22f0f28ecfd245031f70fee85`
- target: `Recaman.ShortTightDonorAvoidance.short_supply_donor_deletion`, source lines 363-391
- registry SHA-256 before packet:
  `012c7e42974931c115efc2e64d9a254deaeb58ff78ac440af713cdb1a497a076`
- exact signature: `raw/target_signature.log`
- hypothesis card: `docs/HYPOTHESIS_CARD_2026-09-21_SHORT_SUPPLY_DONOR_DELETION.md`

## Exact scope

The binders quantify arbitrary periodic `e`, positive `p`, nodup `U`, arbitrary `lag`, donor clock
`u0`, and arbitrary list sublist `B` of `U`. The restrictions are literal:

1. all `u in U` satisfy `u < p` and `e u = true`;
2. all `u in U` have `lag u` exactly 3, 7, or 11;
3. all corresponding windows are P2 and have no positive shorter P2 prefix;
4. `past e u0 11` is P2, minimal, and has exactly two adjacent SS pairs;
5. no completeness of `U`, `u0 in U`, positive drift, actual orbit, or full all-lag supply condition.

Expanded definitions are recorded in `statement_audit_draft.md`. No hypothesis is an unproved custom
`Prop`, and the conclusion is not a hypothesis.

## Dependency reduction

The proof at lines 377-391 performs only this chain:

```text
hBU + all-U assumptions
  -> corresponding B assumptions and B.Nodup
  -> short_window_hall: |B| <= |N(B)|
  -> case |N(B)| = |B|
       -> registered Q: trueOldestPhase not in N(B)
       -> deleted_hall_of_not_mem
     case |N(B)| != |B|
       -> Hall + disequality: |B| < |N(B)|
       -> deleted_hall_of_slack
```

Thus the theorem is not a wrapper in the syntactic gate sense, but its donor-specific content is
exactly Q. The final universal-sublist packaging introduces no new inequality, classification,
monotone quantity, or countermodel.

## Falsification and nonvacuity

Fixed known controls were replayed without declaring a new discovery or holdout range. The complete
replay source is `control_replay.py`; command metadata and unedited stdout are in
`raw/control_replay.command.log` and `raw/control_replay.stdout.log`. A clearly marked hand-edited
digest is `raw/control_examples.summary.log`.

- Tight nonempty witness: p8 `SSAASAAA`, donor `u0=3`, `U=B=[7]`, `N(B)={4}`,
  true-oldest phase 0. All exact U restrictions hold and deletion is nontrivial as a quantified
  operation, although the removed phase is absent by Q.
- Donor-containing removal witness: on the same p8 word, take the full short `U=[3,7]`. For
  `B=[3]` and `B=[3,7]`, `N(B)={0,1,4}`, deletion of true-oldest phase 0 actually changes it to
  `{1,4}`, and the Hall inequality remains true. These are slack cases and show that the theorem is
  not merely a no-op deletion theorem.
- Slack nonempty witness: p11 `AAAASASASSS`, donor `u0=3`, `U=B=[5]`,
  `N(B)={4,9,10}`, true-oldest phase 4, deleted neighborhood `{9,10}`. This exercises actual removal
  and the slack branch.
- E-240 control: p18 `AAAASSAAAASAAASASS`, donor 7, full minimal-supply U
  `{2,7,8,11,13}`, tight `B={2,8,11,13}`, true-oldest 14, `N(B)={4,5,10,17}`.
  The theorem applies and survives without relying on the refuted pure-AAS route.
- SS=3 weakening: p12 `AAAASAAASSSS`, donor candidate 3, `B={2,5,7}` is tight with
  `N(B)={4,10,11}` and oldest phase 4; deletion leaves 2 phases for 3 members. This violates the
  conclusion when `hss = 2` is dropped, while failing that exact hypothesis.
- Empty `B` is a valid boundary case. Duplicate U is excluded by `hUn`.
- The supplied p20 proper-U control has no minimal lag-11 SS=2 donor at any phase and therefore is
  correctly classified as a scope/nonapplicability check, not a witness.

## Interpretation guard

The theorem may be described as: "Hall survives deletion for every sublist of an all-short minimal
supply list." It may not be described as any of the following:

- deletion from an unrestricted complete full all-lag supply set;
- a theorem for U containing lag 15 or larger windows;
- general Gate T6;
- a positive-drift or actual-orbit theorem;
- a new mathematical input beyond Q;
- an E-070, E-067, or Recaman surjectivity advance.

## Preliminary disposition

Hold at `CONJECTURED` during independent review. The auditor should explicitly decide whether the
already Lean-checked exact corollary merits a final card label of `PROVED-LEAN` without any new
registry row. Even after semantic acceptance, any wording must call it a restricted corollary and
must not count Q-to-deletion composition as new mathematics. Parent authorization is required before
any registry, frontier, proof-map, Audit, or Lean change.
