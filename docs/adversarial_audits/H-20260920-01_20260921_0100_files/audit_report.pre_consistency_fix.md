# Independent adversarial audit: core short W/Q

## Conclusion first

- **Overall procedural decision: RETURN (`差戻し`).** Do not register or promote the frozen
  candidate yet. `./scripts/check.sh` is not green (`EXIT_CODE=1` because the explicitly
  unreviewed `Recaman/SS2OldestPattern.lean` is outside the `Recaman` root closure), and the
  repository has only a proposer-authored draft statement audit, not a complete G5 audit for all
  cited core symbols. The daytime implementation was written without the plan's independent
  pre-formalization entry check; this post-hoc audit does not rewrite that history as compliant.
- **Narrow mathematical/source decision for the frozen core only: PASS (`合格`).** For the exact
  SHA-256 files below, through `short_tight_avoids_ss2_donor`, I found no counterexample, hidden
  conclusion, inconsistent premise, E-351 cycle, false offset-11 substitution, or phase/absolute
  clock conflation. Direct module compilation, vacuity lint, semantic dependency inspection, and
  independent local/periodic controls pass.
- The p=32/33 holdout, theorems beginning with `short_supply_donor_deletion`, and
  `SS2OldestPattern` are **UNFINISHED (`未完了`) in this audit**. They are not used to justify the
  narrow core decision.

Thus the candidate's local semantics are not being rejected, but promotion is returned until a
fresh full check and a complete official statement audit succeed on the unchanged source. Any
source/dependency change requires re-audit.

## Identity and boundary

- Cards: `H-20260917-01` (short tight donor avoidance Q), `H-20260920-01` (local owner future W).
- Audit date: 2026-09-21 JST; start clock independently read as `01:08:06 JST`.
- Auditor: `/root/sol_20260921_adversary0100`, independent adversarial Sol; no implementation or
  candidate repair performed.
- Git HEAD: `08c08565c743f39350c9b959e1df7d30aa1cae5d`; dirty working tree, so HEAD alone is not the
  target identity.
- Frozen source hashes:
  - `bb12f35acc8e48c584cead52d675e36b034afda22f0f28ecfd245031f70fee85`
    `Recaman/ShortTightDonorAvoidance.lean`
  - `0bc2293b5d67f7ef5865f7a3f67b2fbf10aeb76bfa92eac9a086cc893c5846f4`
    `Recaman/OwnerFamilyLagEleven.lean`
  - `a90c8f2ac7e6b98dfda4a260434d2e44d3e35781c3212f6a04b7952e9ef6b4c0`
    `Recaman/PeriodicOwnerFamilyLagEleven.lean`
- Reviewed boundary: `ShortTightDonorAvoidance.lean` lines 1-358, plus the exact dependencies
  needed for `ownerFamily_of_minimal` and `tight_owner_family` and existing E-348/E-350/E-353/
  E-357/E-358 primitives.
- Explicitly excluded: line 360 onward (`short_supply_donor_deletion`, nonminimal donor/prefix/
  length-15 branches), all of `Recaman/SS2OldestPattern.lean`, and certification of the used
  p=32/33 holdout.
- Auditor-created files are confined to this `/tmp` directory. Repository files were read only.

## Bounded question and acceptance

Question: does the frozen core state and prove local W and the short tight-donor avoidance Q,
using an actually constructed owner family and without assuming future A or avoidance?

Acceptance: exact binders and definitions agree in both directions with the cards; all core
theorems are inspected individually; `OwnerFamily` fields are expanded; E-351 circularity,
U/Hall/minimal-lag use, true offset, periodic lifting, nonempty cases, and weakened models are
attacked; direct Lean/vacuity/lint/full-check evidence is compared. Stop at a source change,
counterexample, timeout, or the slot deadline.

## Exact central statements

Local W is:

```lean
(e : Int -> Bool) (mem : Int -> Prop) (own : Int -> Int) (lag : Int -> Nat)
(hF : OwnerFamily e mem own lag) (t : Int) (ht : mem t)
(hw : past e t (lag t) = w1) : e (t + 1) = true
```

`OwnerFamily` expands to exactly four fields: each member window is in the 20 minimal P2 words of
lags 3/7/11; each member clock is A; the function `own` assigns each member one S in its window;
and every S in every member window is the `own` value of some member. Future A, oldest ownership,
donor avoidance, Hall, or the conclusion is not a field.

The final reviewed Q universally quantifies `e,p,B,lag,u0`, assumes `0<p`, periodicity, nodup B,
`|N(B)|=|B|`, every B member is a phase below p/current A/minimal P2 of lag 3/7/11, and the donor
window at u0 is minimal P2 of length 11 with SS-count 2. It concludes verbatim:

```lean
trueOldestPhase e p u0 11 ∉ neighborhood e p B lag
```

It is stronger than the original card in dropping full-U, positive-mass, donor-membership, and
Hall-on-U premises: `short_window_hall` constructs Hall on every sublist of B from the existing
short injection after proving its selected S lies inside the actual supplied window. The formal
conclusion is not weakened. Conversely it says nothing about lag >=15 members, general Gate T6,
all-lag capacity, the actual Recaman orbit, or surjectivity.

## Individual core results

| Candidate | Adversarial result | Essential content / limitation |
|---|---|---|
| `shortOff_le_window` | core PASS | For P2 lag `d<=11`, proves `1<=shortOff<=d`; consumes the actual past window. Not free arithmetic. |
| `short_window_hall` | core PASS | Injects every nodup short list into its own `neighborhood`; no Hall premise or full U. |
| `member_window_aas_or_w1` | core PASS, conditional local lemma | Uses E-357 to remove lag 11 and w2 from expanded `OwnerFamily`; does not assume pure AAS. |
| `w1_owns_oldest` | core PASS, conditional local lemma | `onto` supplies an owner of the paired old S; AAS is excluded and a w1 owner is forced to be the root. |
| `w1_future_aas_member` | core PASS, conditional local lemma | Exhausts the owner of the newest S; yields the actual member at `t+2`, lag 3/AAS, and its owned clock. |
| `w1_next_addition` | core PASS, derived wrapper | Reads A at `t+1` from the forced AAS window; it does not call E-351. |
| `tight_w1_next_addition` | core PASS as faithful wrapper | Lint correctly calls it a wrapper; `tight_owner_family` discharges `OwnerFamily` from Hall+tightness. Not a separate substantive result. |
| `donor_cover_next_subtraction` | core PASS | The only compatible donor/w1 placements are d1/d2/d4 and each forces S at `t+1`; uses true offset 10/11. |
| `short_tight_avoids_trueOldest` | core PASS | Lifts a phase cover to the correct absolute clock; AAS is excluded by E-350, w1 by A/S contradiction. Hall remains explicit. |
| `short_tight_avoids_ss2_donor` | core PASS | Classifies a minimal length-11 SS2 donor into the seven words and independently supplies Hall on B. This is the reviewed Q. |
| `ownerFamily_of_minimal` | refactor PASS, not new research | Extracts the existing constructor from semantic minimal-P2/ownership assumptions; conclusion is the structure being built, not a frontier result. |
| `tight_owner_family` | refactor PASS, not new research | Extracts the prior E-359 construction from `tight_owner_map`; registered E-359 theorem signatures remain unchanged. |

The proposer draft statement audit omits separate entries for several cited core symbols
(`member_window_aas_or_w1`, `w1_future_aas_member`, `tight_w1_next_addition`,
`donor_cover_next_subtraction`, and the two extracted constructors). This report audits them, but
it is not an `E-NNN` G5 file and cannot substitute for the required official audit at promotion.

## Attacks and outcomes

1. **Hidden conclusion / contradiction / wrapper attack.** Expanded `OwnerFamily`; no future-A,
   oldest-owning, or avoidance field exists. No candidate is `H->H`, `x=x`, a bare free-variable
   arithmetic result, or based on a user axiom. Only periodic W is a wrapper and is described as
   such. `report_vacuity` flags 0/21.
2. **E-351 cycle.** Searched the reviewed files for `TightHallAugmentation`,
   `aas_after_w1_forced`, `w1_sibling_forced`, and `hall_forces_membership`: no occurrence. Local
   W uses E-353 plus E-357 exclusions and `OwnerFamily.onto`, not the desired future sign.
3. **Owner-family realizability.** `tight_owner_family` obtains a genuine functional matching from
   E-358 `tight_owner_map`, then lifts it by residues to integer clocks. `ownerFamily_of_minimal`
   verifies minimal-word membership rather than assuming `OwnerFamily` in the periodic theorem.
4. **Hall/U attack.** The final Q uses `U=B` only after `short_window_hall` constructs Hall for
   every sublist. The short selector's image is explicitly shown to be an S at a 1-based offset
   no larger than the actual lag. Full-U completeness is therefore genuinely unnecessary here;
   this is not Hall smuggled in as avoidance.
5. **Minimum lag attack.** B windows retain P2 and no proper positive P2 prefix. The donor retains
   length-11 P2 and the same minimality. The theorem does not infer statements for arbitrary
   long/nonminimal donors.
6. **True oldest / false offset 11.** Independently recomputed donor offsets as
   `[10,10,10,11,11,10,11]`; d1/d2/d3/d6 have A at fixed offset 11. The source uses
   `oldestOffset`/`trueOldestPhase`, never a fixed 11 endpoint.
7. **Phase versus absolute clock.** In Q, a phase cover gives residue equality; the proof defines
   the lift `t=s+1+i`, proves `phase p t=b`, transfers the actual window/sign by periodicity, and
   then obtains the exact equality `t-1-i=s`. The contradiction is at one absolute clock. No
   equality of residues is silently treated as integer equality.
8. **Local placement falsification.** With root w1 at clock 0, independent enumeration finds only
   w1(0, offset7) can own the old S at -7. At newest S -1 the bit-compatible candidates are
   AAS(2,3), w1(0,1), and w2(6,7). E-357 is therefore essential: w2 is not excluded by root bits.
   After its exclusion, function-valued ownership rejects root reuse and the other w1 placements
   clash, forcing AAS at 2.
9. **Donor overlap falsification.** Across all 7 donors and all w1 S offsets, exactly d1 at
   `(t,k)=(-9,1)`, d2 at `(-9,1)`, d4 at `(-10,1)` are compatible, and each has S at `t+1`.
10. **Weakened models.** Removing `onto` admits singleton root `{0}`, `own(0)=-7`, next S.
    Replacing functional `own` by a multi-valued relation lets the root consume all three S clocks,
    again with next S. Removing tightness gives p8 `SSAAAASA`, B={7}, w1 with next S and
    `N={0,1,6}`. Removing SS=2 gives p12 `AAAASAAASSSS`, donor 3 and tight B={2,5,7}, covering the
    donor oldest phase. These refute weakenings, not the frozen theorem.
11. **Nonvacuity / known controls.** p10 `SSAAAASAAA`, B={4,7,9} is a tight w1 triple. p20
    `SSAAAASAAAAAAAAASAAA` has full supply {4,7,9,19} and proper tight B={4,7,9}. p8 `SSAASAAA`
    gives nonempty donor/tight Q. E-240 p18 retains the non-AAS tight set and does not cover the
    true oldest phase. p15 `AAAASAAASASASSS` has donor phase3, true offset10/phase8, while false
    offset11/phase7 is A.
12. **Scope attacks.** No inference was made from finite data to all periods, from periodic words
    to the actual orbit, from this short Q to general G2/T6, or from core Q to deletion/capacity.

## Commands and evidence

Auditor commands (all bounded; full stdout/stderr in this directory):

```text
date '+%Y-%m-%d %H:%M:%S %Z (%z)'
git rev-parse HEAD; git status --short; shasum -a 256 <three target files>
python3 scripts/report_vacuity.py --all Recaman/ShortTightDonorAvoidance.lean
python3 scripts/harness_gate.py --lint-module Recaman/ShortTightDonorAvoidance.lean
timeout 55s lake env lean Recaman/ShortTightDonorAvoidance.lean
timeout 20s python3 independent_checker.py
```

Exact results:

- `report_vacuity.raw.log`: 0/21 flagged, exit 0.
- `harness_lint.raw.log`: 20/21 substantive, periodic W wrapper only, exit 0.
- `lean_module.raw.log`: exit 0, SHA-256
  `1ca4a13146b2891c0e462123ac0cb848f92e6221f18b870a1b78c232d1956c35`.
- Frozen reproduction `core_lake_build.raw.log`: `timeout 180 lake build
  Recaman.ShortTightDonorAvoidance`, build completed successfully (110 jobs), exit 0, SHA-256
  `6c83f36836ea7cfed638ed74e9ba032109460737651eecbf98147b8e2966899b`.
- `independent_checker.py`: SHA-256
  `978bdb42ed0ea8be213be97057cbacf0ce56dc65836c7f1a3d90d9873dca6cc8`.
- `independent_checker.raw.log`: PASS, exit 0, SHA-256
  `525c1034648754582589420871fc17b33d45d037f87a1f0a5207c7dae7c0794f`.
- Frozen producer `check.raw.log`: `./scripts/check.sh` exit 1 with exact message
  `module is outside the Recaman root closure: Recaman.SS2OldestPattern`; SHA-256
  `168548eaab2c6d420c8c34170a436b6ebd4d98c4b9314105052eac181756c74d`.
- Frozen p<=11 replay (not independent proof): 1,872 positive-mass words, 52 nonempty Q cases,
  32 W occurrences, zero reported violations. It is regression/OBSERVED only.

One auditor-checker development assertion initially mixed the full-U E-240 neighborhood with the
required known tight-B control and also omitted phase 10. It was corrected to the exact control
`B={2,8,11,13}`, `N={4,5,10,17}`, tight=true before the frozen successful run. This was not a
candidate counterexample and no repository or candidate source changed.

**Reproducibility limitation:** the initial failing checker log was overwritten by the later
successful run, and the pre-correction checker source was not retained as a file. Its observed
source hash was `7864702e5d93d0500c1b8879c1eea38a942f1a9cd84201e00cd37f655123718f`
and the failure was an `AssertionError` at that E-240 expected-neighborhood assertion, but these
conversation-captured facts are not a preserved raw artifact. Only the final checker source and
successful raw output are independently reproducible from this directory.

## Remaining obligations and decision

- Run a fresh successful `./scripts/check.sh` after the separately owned root-closure problem is
  resolved; do not weaken or bypass the gate.
- Generate the official G5 statement audit for the eventual registry ID, quoting every cited core
  signature and expanding both constructor/refactor premises. The proposer draft is not enough.
- Record explicitly that the daytime candidate lacked an independent pre-formalization entry
  inspection. This post-hoc review validates only the frozen semantics; it cannot be described as
  an audit performed before implementation.
- Do not use the p32/33 holdout as independently certified here. It is already used and its second
  algorithm came from the same author/session.
- Keep `short_supply_donor_deletion` and everything after it, including nonminimal/prefix/
  length-15 claims and `SS2OldestPattern`, outside this verdict.
- No new registry row, evidence-label change, proof-map/frontier update, or commit is authorized by
  this audit. Card status remains unchanged pending the returned obligations.

**Final scope-qualified verdict:** frozen core mathematical W/Q source: `合格`; repository
promotion procedure: `差戻し`; excluded candidates and holdout certification: `未完了`.
