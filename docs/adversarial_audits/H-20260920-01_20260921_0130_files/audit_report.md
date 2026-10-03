# Independent adversarial audit: 01:30 W/Q repair

## Conclusion first

- **Repair question: PASS (`合格`, scope-qualified).** The two repairable reasons for the 01:00
  return are now resolved by normal mechanisms without changing the frozen W/Q mathematical
  sources or statements: the root-closure gate is repaired by one ordinary root import, and the
  pre-registration statement packet covers all ten core declarations plus both owner-family
  constructors. A fresh independent `./scripts/check.sh` passes.
- **Promotion/registration: UNFINISHED (`未完了`).** No evidence ID or registry row exists, so no
  official `docs/statement_audits/E-NNN.md` for the new core can yet be generated or machine-checked.
  Both cards remain `CONJECTURED`; this audit authorizes no registry/frontier/proof-map update.
- **Historical defects remain historical.** The daytime formalization had no independent
  pre-formalization entry check, and the 01:00 checker did not preserve its first erroneous source
  and raw output. The present post-hoc audit does not claim to recreate either event.
- `short_supply_donor_deletion` and everything after it, `SS2OldestPattern`, the p32/33 holdout as
  independently certified evidence, general lag, general Gate T6, E-070/E-067, the actual orbit,
  and surjectivity remain outside this verdict.

## Identity, roles, and boundary

- Audit start: 2026-09-21 01:34:38 JST. Repair freeze reported at 01:45:46 JST.
- HEAD: `08c08565c743f39350c9b959e1df7d30aa1cae5d`.
- Auditor: `/root/sol_20260921_repair_audit0130`, independent of repair implementation.
- Repairer: `/root/sol_20260921_repair0130`.
- Final dirty descriptor at 01:46:57 JST: SHA-256
  `94681dd99b03e610b81264db7b52001db36f50b84fc34afd7925c887c3b76d00` over 26 sorted
  porcelain-status entries, hashing files and recursive untracked directory trees.
- Frozen mathematical source hashes:
  - ShortTight: `bb12f35acc8e48c584cead52d675e36b034afda22f0f28ecfd245031f70fee85`.
  - OwnerFamily: `0bc2293b5d67f7ef5865f7a3f67b2fbf10aeb76bfa92eac9a086cc893c5846f4`.
  - PeriodicOwnerFamily: `a90c8f2ac7e6b98dfda4a260434d2e44d3e35781c3212f6a04b7952e9ef6b4c0`.
- Final repair packet manifest: `docs/data/issue73_20260921/slot0130/SHA256SUMS`, SHA-256
  `2638d50a7bbec8609c1d10697379ed581caae2e2c214b432ec6bfa99e885b6ed`.

The bounded question was whether the full-check failure and missing statement material could be
repaired without changing W/Q mathematics. Acceptance required a normal root integration, green
full check, unchanged three source hashes, exact source quotations, expansion of defined premises,
two-way semantic comparison, nonempty/negative controls, and no promotion. Stop conditions were
source drift, gate weakening, counterexample, timeout, or the slot deadline.

## Exact reviewed claims

The exact punctuation-preserving signatures for all declarations are in
`docs/data/issue73_20260921/slot0130/core_signatures_verbatim.txt`; an independent line comparison
passed for all 82 quoted source lines.

Local W is exactly:

```lean
(e : Int → Bool) (mem : Int → Prop) (own : Int → Int) (lag : Int → Nat)
(hF : OwnerFamily e mem own lag) (t : Int) (ht : mem t)
(hw : past e t (lag t) = w1) : e (t + 1) = true
```

The final Q quantifies `e,p,B,lag,u0`; assumes `0<p`, periodicity, nodup/tight B, phase bounds,
current A, minimal P2 B-windows with lag in `{3,7,11}`, and a minimal length-11 P2 donor with
`ssCount=2`; it concludes exactly:

```lean
trueOldestPhase e p u0 11 ∉ neighborhood e p B lag
```

The ten core declarations are `shortOff_le_window`, `short_window_hall`,
`member_window_aas_or_w1`, `w1_owns_oldest`, `w1_future_aas_member`, `w1_next_addition`,
`tight_w1_next_addition`, `donor_cover_next_subtraction`, `short_tight_avoids_trueOldest`, and
`short_tight_avoids_ss2_donor`. The two audited constructors are `ownerFamily_of_minimal` and
`tight_owner_family`.

`OwnerFamily` was expanded to its four fields: member windows are among the 20 minimal P2 words of
lags 3/7/11; members are A clocks; functional `own` selects an S in each member's window; every S
in every member window is owned by some member. Future A, oldest ownership, avoidance, Hall, and
the conclusion are not fields. The four local W-chain lemmas are therefore conditional alone, but
`tight_owner_family` constructs the structure from concrete Hall/tightness data before periodic W
and Q use it.

## Adversarial attacks

1. **Hidden conclusion / contradiction / tautology.** Direct source inspection found no `H→H`,
   `x=x`, conclusion premise, contradictory premise, free-variable arithmetic-only result, user
   axiom, `sorry`, `admit`, or `native_decide`. `report_vacuity` flags 0/21. The harness classifies
   20/21 substantive; only periodic W is a syntactic wrapper.
2. **E-351 cycle.** The three frozen mathematical sources contain no `TightHallAugmentation`,
   `aas_after_w1_forced`, `w1_sibling_forced`, or `hall_forces_membership`. W uses E-357
   exclusions, E-353 paired-S rules, and the expanded owner-family fields.
3. **Hall and U.** `short_window_hall` proves the existing selector lies in each actual supplied
   window and injects every nodup short list into its own neighborhood. The final Q therefore
   legitimately uses `U=B`; it does not assume full-U completeness or Hall as avoidance.
4. **Minimum lag and scope.** Minimality is retained for every B window and the donor. No inference
   is made for lag at least 15, nonminimal arbitrary donors, SS at least 3, actual orbits, or general
   T6.
5. **True offset and phase/clock.** Independent recomputation gives donor offsets
   `[10,10,10,11,11,10,11]`; fixed offset 11 is A for d1/d2/d3/d6. The source uses
   `oldestOffset` and transports residue equality to a deliberately constructed absolute clock
   before deriving the A/S contradiction.
6. **Negative premises.** Removing `onto` or functional ownership permits a local w1 root followed
   by S. Removing tightness gives p8 `SSAAAASA`, B={7}, next S. Removing SS=2 gives p12
   `AAAASAAASSSS`, B={7}, N={4}, covering the donor oldest. These are weakening countermodels,
   not counterexamples to the frozen theorem.
7. **Nonempty controls.** The local family has members `{-3,0,2}`, words `{AAS,w1,AAS}`, owners
   `{-6,-7,-1}` and next A. p10 `SSAAAASAAA`, B={4,7,9} is tight; p20
   `SSAAAASAAAAAAAAASAAA` has full supply `{4,7,9,19}` and proper tight B={4,7,9}; p8
   `SSAASAAA` has donor phase 3 and tight B={7} avoiding true-oldest phase 0.
8. **Known regressions.** E-240 recomputes B={2,8,11,13}, N={4,5,10,17}, tight. The p15 false
   offset control has true phase 8 and fixed-11 phase 7/A. The p12 SS3 and p11 no-tight controls
   match their recorded neighborhoods.
9. **Existing E-359 audit drift.** The audit initially said `tight_no_lag_eleven` itself built the
   six owner-family obligations, while the current refactor places that proof in
   `tight_owner_family`. Under explicit expanded ownership the repairer synchronized only the
   proof-location, wrapper-classification, and dated provenance prose. The source, signatures,
   claim, registry row, and mathematics stayed unchanged. The official audit now correctly calls
   the caller a composition wrapper and the helper a nontrivial extraction of existing E-359
   content, not new research.

## Commands and exact outcomes

- Independent `bash scripts/check_module_architecture.sh`: exit 0; root reaches 389/389 modules;
  110 import contracts pass.
- Independent `./scripts/check.sh` after the final E-359 synchronization: exit 0; 392 jobs;
  2,572 declarations within `{propext, Classical.choice, Quot.sound}`; final line `All Lean builds
  and audits passed.`
- `python3 scripts/report_vacuity.py --all Recaman/ShortTightDonorAvoidance.lean`: exit 0,
  0/21 flagged.
- `python3 scripts/harness_gate.py --lint-module Recaman/ShortTightDonorAvoidance.lean`: exit 0,
  20/21 substantive.
- `lake env lean Recaman/ShortTightDonorAvoidance.lean`: exit 0.
- Exact signature comparison: exit 0, all 82 packet lines equal current source lines.
- Final repair manifest verification: exit 0, all files OK.
- Independent finite checker: no seed; eight fixed periodic controls; minimal-lag cutoff
  `p(p+1)`; seven donors; source revision and ShortTight hash embedded in output. Final v3 exits 0
  with `PASS: 8 finite controls; 7 donors; local placement tables`. This is regression/countermodel
  evidence, not a universal proof or new holdout.

The auditor's first checker run failed before evaluation because the p8 positive Q subset was
mistyped as phase 2, which is not a supplied phase (`KeyError: 2`). The v1 source and failing raw
log are preserved. Direct enumeration corrected B to `{7}`; v2 and the expanded local-family v3
pass. No theorem, hypothesis, range, or repository source changed during that correction.

## Remaining obligations and decision

The repairable current-state return items are closed: root closure, full check, complete
pre-registration semantic material, source identity, and the discovered E-359 documentation
sync all pass. What remains is not silently waived:

- reserve the actual evidence ID and final cited-symbol list, then generate and machine-check the
  official G5 file;
- obtain the parent's registration decision; until then keep both cards `CONJECTURED`;
- preserve the historical missing pre-formalization review and missing first checker artifacts;
- require a new audit after any mathematical source/dependency change;
- do not treat the root import as semantic certification of `SS2OldestPattern`.

**Final procedure verdict:** this bounded repair is `合格`; new core promotion is `未完了`;
excluded later claims remain `未完了`. No stop recommendation for the frozen core, but stop any
attempt to generalize it to all lag/T6/orbit without a new card and entry audit.
