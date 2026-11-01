# Weekly adversarial audit v1

## Scope and preliminary verdict

- Card IDs: H-20260917-01, H-20260920-01/02/03/04/05, H-20260921-01.
- Date/time: 2026-09-24 JST, start 02:03:58.
- HEAD: `08c08565c743f39350c9b959e1df7d30aa1cae5d` (dirty working tree).
- Lean sources: `ShortTightDonorAvoidance.lean` SHA-256
  `bb12f35acc8e48c584cead52d675e36b034afda22f0f28ecfd245031f70fee85`;
  `SS2OldestPattern.lean` SHA-256
  `a9540f5f891198ec91eefd73f62f9e35d4e59f645936dc3a349504e529b325de`.
- Bounded question: does a complete inventory support ending the scheduled week without expanding
  any REFUTED/STOPPED/PROVED claim, and does it state concrete future reopen gates?
- Acceptance: every weekly candidate is classified by exact scope, evidence and procedure; missing
  provenance and dependencies remain visible; the final stop is a schedule/portfolio decision rather
  than a false mathematical refutation.
- Stop: at 02:21 no new search or proof work; unreproduced/high-cost material remains incomplete.

Preliminary procedural verdict: **return for correction until the writer packet explicitly includes
the inventory and separates three kinds of stopping**: proved restricted results, specifically
refuted/stopped implementation routes, and conjectures left incomplete. No existing evidence label
should change in this slot.

## Exact candidate classification

1. **H-20260917-01 / H-20260920-01, E-360**: keep `PROVED-LEAN` only for the registered
   `short_tight_avoids_ss2_donor` and conditional local W (`w1_owns_oldest`,
   `w1_next_addition`). W assumes the four `OwnerFamily` fields; the periodic application constructs
   that family through the E-358/E-359 path. This is arbitrary positive period but only minimal
   member lags 3/7/11 and a minimal lag-11 SS2 donor. It is not arbitrary lag, all-lag U, actual orbit,
   E-070/E-067, or surjectivity.
2. **H-20260921-01**: keep `PROVED-LEAN` for `short_supply_donor_deletion` only when every member of
   U is an in-range current-A minimal P2 window of lag 3/7/11. It is a direct Q + short Hall + generic
   deletion corollary, no new E-row or new mathematical input.
3. **H-20260920-02**: keep `CONJECTURED`, overall procedure incomplete. The Lean candidate
   `short_tight_avoids_ss2_window` removes donor minimality/current-A only at fixed donor length 11
   while member windows remain minimal lag 3/7/11. Its limited semantic audit is not promotion.
4. **H-20260920-03**: keep `CONJECTURED`, overall procedure incomplete. The audited equality
   `tight_neighborhood_eq_of_p2_prefix` assumes m<=lag<=11, P2 at m, and lag-side tightness; it is
   broader than the original full-lag-P2/minimal-m strict question. No exact-premise strict/tight
   example is known. Downstream `short_p2_tight_avoids_ss2_window` and `short_p2_ss2_deletion`
   depend on H-02 and are not established weekly inputs.
5. **H-20260920-04**: keep `REFUTED` only for changing donor length 11 to a **nonminimal** length-15
   donor. The p16 literal has a proper P2 prefix of length 3, so it does not refute minimal lag 15,
   arbitrary lag, Gate T6, or an actual orbit. `STOPPED` applies only to this same nonminimal-length
   replacement route.
6. **H-20260920-05**: keep `CONJECTURED`, overall procedure incomplete. Limited semantic pass covers
   only `moment_ending_A_budget`, `moment_ending_AA_ss2`, and `ss2_intervening_prefix`. It does not
   cover paper sections 3-5, the remaining seven declarations in `SS2OldestPattern.lean`, their
   AAS/w1 and true-oldest composition, periodic lift, arbitrary-length donor avoidance/deletion, or
   a final theorem for the card.

## Unreviewed and incomplete evidence inventory

### Computation

- p32/p33 seed-2026091801, 2,000 accepted words per period: used finite evidence, same-author second
  implementation, not an independently certified holdout and not reusable as fresh holdout.
- lag-max-19 four shards: only the four terminal `excluded 409/409, consistent closure 0, cap hit 0`
  lines were observed. Revision, partition completeness/disjointness, generator conditions and raw
  execution provenance remain unaudited. They are not a general-lag exclusion.
- H-04 old 32768/85/46 census, second w1 witness, and minimum-period/minimum-lag claims remain outside
  the independent literal audit.
- H-05 discovery/holdout donor-pattern census (lengths 11/15/19 and 23/27/31) remains finite evidence;
  it does not prove the all-length statement. The prior bounded word checker supports only the three
  local declarations after its limited audit.
- H-03 p1..12/p15 counts have no exact-premise strict/full-P2/tight witness. Zero target instances is
  neither a proof of nonexistence nor a counterexample.
- H-02's three fixed-shortOff charge collisions are exploratory `OBSERVED`; the selector itself was
  not independently recomputed. This refutes only that shortcut if reproduced, not owner-family
  avoidance.
- 9/20 broken falsification-gate implementation and the proper-U probe with zero w1 antecedents are
  stopped/unfinished diagnostics, not counterexamples to Q/W.

### Paper and Lean

- H-02 exact Lean candidate has a limited semantic pass but cannot be registered from this week's
  procedure because the required independent preformalization entrance audit was absent.
- H-03 equality has a limited semantic pass; the intended strict subdomain/nonvacuity and the two
  H-02-dependent avoidance/deletion theorems remain unestablished.
- H-05 paper sections 3-5 and all downstream source declarations after the three audited local lemmas
  remain unreviewed. The source contains no final theorem expressing the whole card.
- No official H-05 G5 statement audit or explicit `Recaman/Audit.lean` prints exist for the local
  three declarations. Root import and successful full build do not replace those steps.
- No bridge exists from finite periodic sign words to the actual Recaman orbit, nor from short-only U
  to a complete all-lag supply set, nor from G2 to general Gate T6.

### Historical procedure debt

- Daytime H-01 through H-05 formalization began without the now-required independent entrance check.
  Later semantic audits do not retroactively repair that chronology.
- The 9/21 initial independent checker source/raw was not preserved before correction; later
  reconstruction/replay does not make it original provenance.
- H-02's first two failed checker runs lack their exact execution-time source/hash.
- H-05's first helper-checker and Lean-diagnostic executions lack persisted pre-run hashes; later
  hash/replay is only a reproducibility check.
- These historical defects do not invalidate the registered, later independently audited E-360
  mathematics, but they bar using the affected later candidates as fully compliant new results.

## Dependency obligations and attacks

- Expand `OwnerFamily`: `window`, `addA`, `own_mem`, `onto` are genuine assumptions. Never report W
  as periodicity alone. Removing `onto` has a weakened-model counterexample.
- E-351 already assumes next A and future phase/lag membership in its relevant conclusion; using it
  to prove W's next A would be circular. The audited E-360 proof does not do this.
- H-03 downstream avoidance/deletion consumes H-02, whose overall status is incomplete. A Lean build
  cannot turn that dependency into an established research input.
- H-05 needs the exact word-to-stream decomposition, all AAS/w1 placements, true-oldest coordinate
  handling, and periodic owner-family lift before any arbitrary-length donor statement.
- General-lag work must preserve owner offset kx versus true-oldest offset r and delta=r-kx. The p16
  counterexample has true offset 15/phase 0; offset 11/phase 4 is not substitutable.
- Full all-lag U and all-short U are different objects. General Gate T6 also retains the known p<=11
  bottleneck for donor-containing subsets unless a new bridge replaces it.
- E-240, E-069/E-133, E-345 and E-351 remain boundary guards, not positive inputs for the missing
  arbitrary-lag theorem.

## Stop and reopen decision under attack

The week should end on schedule and no new search should start in the remaining slot. This is a
**schedule/portfolio stop recommendation**, not a `REFUTED` or global `STOPPED` label for H-02,
H-03, H-05, minimal lag 15, arbitrary lag, or actual-orbit work. Those stay `CONJECTURED` or open.
The only mathematical-route STOPPED judgment added by the week's evidence is the already scoped
nonminimal-length-15 replacement (plus the earlier broken gate implementation branch).

Future reopening must not be phrased merely as "new independent input". Require a separately
authorized bounded card, frozen before computation/formalization, with one of these exact targets:

- periodic arbitrary-length **minimal** SS2 donor: complete the H-05 AAS/w1/true-oldest and periodic
  composition without using H-02/H-03 as established, then obtain an independent entrance pass;
- member lag >=15/general lag: state a concrete owner-offset/delta constraint or countermodel that
  survives E-240/E-069/E-345 and the p16 nonminimal control; do not reopen by extending a census;
- actual Recaman orbit: a separate card proving orbit provenance for the needed periodic/local
  hypotheses; no inference from periodic words alone.

Each reopened card must have nonzero exact-premise examples, weakened-history controls, fresh or
explicitly consumed data classification, pre-run source hashes, exact argv/cwd/timeout/exit/raw
streams, and independent preformalization review. A later clean rerun may create a new prospective
result but may not rewrite this week's missing history.

## v1 conclusion

The evidence supports closing the scheduled week without extending the search. It does **not**
support refuting or stopping the entire general-lag program. The writer packet must preserve all
classifications above and enumerate the evidence/procedure debt before this audit can pass.
