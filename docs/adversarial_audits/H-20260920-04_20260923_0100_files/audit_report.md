# H-20260920-04 independent adversarial audit, 2026-09-23 01:00 JST

## Conclusion and scope

**Procedural verdict: 合格, limited to one frozen period-16 literal and the decision to stop the nonminimal length-15 donor replacement.** The literal `SAAASSSASASASAAA` meets every premise of that replacement and negates true-oldest avoidance and deletion Hall for `B=[3]`. The universal replacement is `REFUTED`; continuing that exact route is `STOPPED`. This does not certify the entire H-04 card. Its old 32768/85/46 census, second w1 example, and any minimum-period or minimum-lag assertion remain unreviewed. The lag-11 results, a minimal length-15 donor question, general Gate T6, E-070/E-067, and actual Recaman orbits remain outside scope.

The card already displayed `REFUTED` from a same-session pass. That historical label was not independent approval. The daytime pre-formalization independent entry check was missing. This later review does not retroactively provide it. No new registry row or proof-map promotion is authorized by this report alone; the parent must compare this record with the frozen packet. Any later source, definition, card-claim, or dependency change needs a new audit.

Reviewer: independent Sol `/root/sol_20260923_boundary_audit0100`, separate from writer `/root/sol_20260923_boundary0100`. Repository research files were read only. All new checker code, raw output, and this record are under `/tmp/recaman-audit-20260923-0100-sol/`.

## Frozen target and exact claim

Repository HEAD: `08c08565c743f39350c9b959e1df7d30aa1cae5d`. Target source `Recaman/ShortTightDonorAvoidance.lean` SHA-256 `bb12f35acc8e48c584cead52d675e36b034afda22f0f28ecfd245031f70fee85`, copied in full as `target_source.lean`. Current H-04 card SHA-256 `682e3f62b5c172dac60bbc3c8085cd67b4b33215048112e70756d04956a7c4d4`, copied as `target_card_current.md`; the pre-append card SHA-256 `21a41d3f06948dd97cfabbcb1df880e0a86679694c79cf3aa2cb1dd85840668e` is `target_card.md`. Frozen writer packet `candidate_packet.md` SHA-256 `d8b4f8292d7430d9ac7afd71720fcc545e25d3a835646a03d510b61d58284d11`; its 28-file manifest SHA-256 `5f296363d547d3c94ec14f3e6178465326beed47b65e834246bdfbc85e811a0d`, checked with `shasum -a 256 -c` (exit 0, all OK). The card appendix draft is separately frozen as `card_append_DRAFT_frozen.md`.

Exact proposed universal claim: for any `e : Int -> Bool`, `p>0`, periodic `e`, nodup in-range current-A list `B`, each member with a P2 window of length at most 11 (no member minimality needed), and `|N(B)|=|B|`, every length-15 P2 donor with overlapping `ssCount=2`, without donor minimality, has its true oldest S phase outside `N(B)`. The associated deletion claim says `|B| <= |N(B) \\ {trueOldestPhase}|`. The donor need not be current A and positive period mass/full U/Hall are not premises. The period-16 witness satisfies those three extra conditions anyway. H-04 changes the donor length in H-03's intended donor-avoidance consequence from 11 to 15; it does not challenge H-03's separate minimal-prefix neighborhood equality. The informal dependency chain would need a new length-15 donor-cover restriction; the AAS singleton collision below refutes that edge.

Verbatim target Lean signature, from source lines 651-661 (the certificate is a concrete conjunction, not a proof of the false universal statement):

```lean
theorem nonminimal_donor_length15_counterexample :
    (∀ t : Int, donorLength15Stream (t + 16) = donorLength15Stream t) ∧
    Recaman.ShortPeriodicSupply.signSum donorLength15Stream 0 16 = 2 ∧
    donorLength15Stream 15 = true ∧ P2 (past donorLength15Stream 15 15) ∧
    Recaman.OneSSMultiplicity.ssCount (past donorLength15Stream 15 15) = 2 ∧
    P2 (past donorLength15Stream 15 3) ∧
    donorLength15Stream 3 = true ∧ past donorLength15Stream 3 3 = aas ∧
    neighborhood donorLength15Stream 16 [3] (fun _ => 3) = [0] ∧
    phase 16 (15 - (oldestOffset (past donorLength15Stream 15 15) : Int)) = 0 ∧
    Recaman.TwoSSTightDisjoint.deletedNeighborhood donorLength15Stream 16 [3]
      (fun _ => 3) (phase 16 (15 - (oldestOffset (past donorLength15Stream 15 15) : Int))) = [] := by
```

The source definition `donorLength15Stream` is the 16-bit literal. `P2` expands to `mass=1 ∧ moment=0`; `past` reads newest-first `e(t-1),...,e(t-d)`; `ssCount` counts overlapping `SS` pairs; `oldestOffset` is the largest 1-based S position; `trueOldestPhase` uses the endpoint at that offset; `neighborhood` filters actual S phases covered by member windows; `deletedNeighborhood` filters that phase out. These were read directly in `LeadingRunSupply.lean`, `OneSSMultiplicity.lean`, `LagSevenDonorCoverage.lean`, `TrueOldestGateT6.lean`, `LowSSPeriodicSupply.lean`, `TwoSSTightDisjoint.lean`, and `LagElevenPeriodic.lean`. The signature has no hidden defined-Prop hypothesis, conclusion-equivalent assumption, `H -> H`, or free-variable arithmetic substitute. Its proof uses `decide` on a fixed stream plus a periodicity argument, which is appropriate for one finite witness, not a new general theorem.

The certificate does not itself state `B.Nodup`, member minimality, or full-U Hall. Those are separately recomputed below. Conversely, it does explicitly state real periodic signs, donor P2/SS2, `N(B)=[0]`, true-oldest phase 0, and deleted neighborhood `[]`. The implication from these equalities to a failed inequality is arithmetic `1 <= 0`, with a nonempty antecedent. E-360's registered signature still requires a minimal length-11 donor; this witness has a proper P2 prefix and does not refute it.

## Independent falsification

`independent_literal_check.py` imports no repository checker and was written from the literal and source definitions. It checked all 14 positive proper donor prefixes, all B conditions, periodic modulo behavior including the phase-0 boundary, actual S coverage, all positive lags through inclusive 272 for each current-A phase, and Hall for all 16 subsets of the resulting full U. Its complete raw JSON is `independent_literal_check.stdout`; stderr is empty. Summary of exact results:

| Obligation | Recomputed result |
|---|---|
| Period/current signs | `p=16`, period mass `2`; donor `u0=15` is A; `B=[3]` is nodup, in range, current A, and excludes donor. |
| Donor word | `past e 15 15 = AASASASASSSAAAS`; `(mass,moment)=(1,0)`, overlapping SS count `2`. |
| Nonminimality | Exactly one proper P2 prefix, length `3`; minimal-donor strengthening excludes this witness. |
| B realization | `past e 3 3=AAS`, P2 and minimal; `N(B)=[0]`, `|N|=|B|=1`; local Hall on both subsets. |
| True oldest | Largest S offset `15`; `(15-15) mod 16=0`, an actual S and member of `N(B)`. Avoidance is false. |
| Deletion | `N(B)\\{0}=[]`; `1 <= 0` is false. |
| Extra full-U control | Nine current-A phases examined; four supplied: `U=[1,3,11,15]`, least lags `{1:11,3:3,11:39,15:3}`; all `16/16` subsets satisfy Hall. |

The full-U scan was over lags `1..272`, not an unbounded search. Its completeness for this positive-mass periodic word uses existing E-181 `Recaman.PeriodicSupplyBound.supply_lag_bound`: a P2 supplier at any positive lag exists iff one exists by `p*(p+1)`. The checker directly obtains backward `periodMass=2`, and `LeadingRunSupply.past_p2_iff` equates the two P2 formulations. Full U/Hall remains `COMPUTED` for this one word, augmented by an existing Lean finite-bound theorem; it is not a conjunct of `nonminimal_donor_length15_counterexample` and not an all-period Hall result. No random seed or fresh holdout was used; this is a known literal, not discovery or a census.

Negative controls: replacing true-oldest offset 15 with fixed offset 11 gives phase 4, so `4 ∉ N(B)` and deleting 4 leaves `[0]` with Hall true. That changed conclusion misses this counterexample; it cannot stand in for true-oldest avoidance. Adding donor minimality excludes the literal because prefix 3 is P2. Removing a putative ambient-Hall premise cannot rescue the claim, since this literal satisfies full-U Hall. `B=[]` would make avoidance trivial; the tested `B=[3]` is nonempty and tight. The donor's oldest bit crosses the period boundary at phase 0, so the modulo check exercises that boundary.

`known_controls.py` independently recomputed three frozen regressions: E-240's period-18 tight `B={2,8,11,13}` has a lag-7 member, `N=[4,5,10,17]`, and donor oldest phase 14 still avoided; E-069's period-12 phases 7 and 11 have least lags 11 and 3 but share oldest phase 8; E-345's period-12 SS=3 donor has oldest phase 4 covered by its tight B. Complete raw JSON is `known_controls.stdout`. E-180 is the separate `slack >= collision count` counterexample, not an SS-deletion counterexample. None of these controls is reclassified as the present SS=2 nonminimal length-15 witness. E-351's future-AAS lemma and W/Q are not premises of the literal certificate, so no circular E-351 argument is used. The E-360 Q/W claim is unchanged and its G5 audit was compared to source; this audit neither upgrades nor reopens it.

## Commands and raw evidence

The two runners were invoked as `python3 -u /tmp/recaman-audit-20260923-0100-sol/run_local.py` and `python3 -u /tmp/recaman-audit-20260923-0100-sol/run_gates.py`. All commands below had cwd `/Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research`. Exact argv, start/elapsed seconds, timeout, exit, and raw-stream hashes are in `local_commands.json` and `gate_commands.json`; the corresponding named `*.stdout`/`*.stderr` files contain complete unedited streams. These are raw evidence files, while this report's tables are summaries.

| Exact command | Timeout | Exit | Raw stdout/stderr |
|---|---:|---:|---|
| `python3 -u /tmp/recaman-audit-20260923-0100-sol/independent_literal_check.py` | 30 s | 0 | `independent_literal_check.stdout/.stderr` |
| `python3 -u /tmp/recaman-audit-20260923-0100-sol/known_controls.py` | 30 s | 0 | `known_controls.stdout/.stderr` |
| `lake env lean /tmp/recaman-audit-20260923-0100-sol/axiom_check.lean` | 60 s | 0 | `axiom_check.stdout/.stderr`; target axioms `[propext, Quot.sound]` |
| `python3 scripts/report_vacuity.py --all Recaman/ShortTightDonorAvoidance.lean` | 45 s | 0 | `vacuity.stdout/.stderr`; `0/21` flagged |
| `python3 scripts/harness_gate.py --lint-module Recaman/ShortTightDonorAvoidance.lean` | 45 s | 0 | `lint.stdout/.stderr`; target substantive, module `20/21` |
| `python3 scripts/harness_gate.py --check-registry` | 45 s | 0 | `statement_audit_registry.stdout/.stderr`; G1-G5 existing rows pass |
| `./scripts/check.sh` | 480 s | 0 | `full_check.stdout/.stderr`; 392 jobs, 2572 audited declarations, allowed axioms |

The writer's separate final-run logs are preserved in the frozen slot0100 packet, including `statement_audit.stdout` showing exact source/E-360 G5 signature matches, `target_build.stdout` (110 jobs), and `symbol.stdout`. I directly compared the target signature above with the source and independently ran `#check`/`#print axioms`. Harness outputs are heuristic and were not treated as a semantic proof. No new Lean file or repository research file was written by this reviewer.

## Remaining obligations and next decision

The stop decision applies only to a length-15 **nonminimal** SS=2 donor extension of short-tight true-oldest avoidance/deletion. It does not establish a minimal length-15 classification, length optimality, the second w1 example, the old 32768/85/46 enumeration, arbitrary-lag owner exclusion, or full Gate T6. Those require their own frozen statements and independent evidence if pursued. The old census and second literal remain historical self-reported observations in the card, not audited conclusions of this record.

I compared the writer's complete proposed card `docs/data/issue73_20260923/slot0100/proposed_card_final.md` byte version SHA-256 `1b76b58c606fa31358860b859e136d28827d66bd3c46830a13a99a7a4e08fd8e`, copied as `proposed_card_final_frozen.md`, against the current H-04 card. It clarifies donor exclusion versus coverage of the oldest S, labels the earlier computation same-session, limits independent review to p16, preserves the old counts and second example as unreviewed history, records the missing pre-formalization entry check, and adds no registry row. This **exact proposed version is approved for parent application after parent comparison of this report and raw streams**. Its prospective text says the parent comparison happened; it must not be applied before that comparison. Any different applied byte version or mathematical-source change requires re-audit.

The next research decision is to stop this precise nonminimal length-15 replacement and select a new bounded question only with a separately fixed entry test. Re-running stopped OS/pure-AAS/large lag-15 certificate searches is not warranted by this result.
