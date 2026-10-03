# H-20260920-05 local intervening-prefix adversarial audit

## Conclusion first

**Bounded mathematical/semantic verdict: 合格**, limited exactly to
`moment_ending_A_budget`, `moment_ending_AA_ss2`, and
`ss2_intervening_prefix` at target SHA-256
`a9540f5f891198ec91eefd73f62f9e35d4e59f645936dc3a349504e529b325de`.
The signatures match paper sections 1-2 and the card's 15:21 word lemma. They
are inhabited, non-circular, length-independent Bool-word results; the strict
prefix condition is substantive.

**Overall H-20260920-05 procedural verdict: 未完了.** H-05 stays
`CONJECTURED`. The daytime formalization lacked the required independent
preformalization entry review, and this retrospective audit does not repair
that history. Paper sections 3-5, the downstream source declarations, stream
and periodic transport, arbitrary-length donor avoidance/deletion, H-02/H-03,
general lag, Gate T6, actual orbits, and surjectivity are not accepted here.
There is no evidence-label promotion and no registry/frontier/proof-map/Audit
change authorized by this report.

The writer packet initially needed documentation-only correction: it called a
future-AAS dependency an H-02 input and did not preserve pre-run hashes for the
writer-created literal checker/Lean diagnostic. The corrected packet says that
`w1_future_aas_member` is the existing E-360 OwnerFamily/W-dependent
consequence, preserves the first-run provenance gap, and records a later
prehashed byte-identical replay. Corrected candidate SHA-256:
`32877623e5287564b05b6960d876a309691fe7d23d256f8d5fc17c8c9ccccc21`.

## Identity and scope

- Card: `H-20260920-05`; source card status `CONJECTURED`.
- Auditor: `/root/sol_20260923_intervening_audit0230`, independent from writer
  `/root/sol_20260923_intervening0230`; no sub-agent was started.
- Started `2026-09-23 02:33:43 JST`; report drafted `2026-09-23 02:39 JST`.
- HEAD: `08c08565c743f39350c9b959e1df7d30aa1cae5d`.
- Repository was dirty at start. Target module was untracked; `Recaman.lean`,
  `Recaman/Audit.lean`, registry/frontier/proof-map, and other research files
  already had changes. Auditor made no repository write, stage, or commit.
- Audit work was confined to `/tmp/recaman-audit-20260923-0230-sol/`.
- Frozen source hashes: target `a9540f5f...`, original experiment
  `1ae348ab...`, card `a85e406c...`, paper `e6d9c4df...`.
- Stopping condition: do not extend the declared finite ranges; finish all
  computation before 02:50 JST. Satisfied.

## Verbatim statements

```lean
theorem moment_ending_A_budget (w : List Bool) (q : Nat)
    (hss : ssCount (w ++ [true]) ≤ q) :
    (q : Int) + 1 ≤ moment (w ++ [true]) + q * (w ++ [true]).length
```

```lean
theorem moment_ending_AA_ss2 (w : List Bool)
    (hss : ssCount (w ++ [true, true]) ≤ 2) :
    5 ≤ moment (w ++ [true, true]) + (w ++ [true, true]).length
```

```lean
theorem ss2_intervening_prefix (w : List Bool)
    (hm : mass (w ++ [true]) = 0)
    (hM : moment (w ++ [true]) + (w ++ [true]).length ≤ 0)
    (hss : ssCount (w ++ [true]) ≤ 2) :
    ∃ u v : List Bool, w ++ [true] = (u ++ [false]) ++ v ∧
      P2 (u ++ [false]) ∧ v ≠ []
```

Definitions were unfolded directly: `true=A`, `false=S`, words are
newest-first, `mass` is the sign sum, `moment` is the 1-based weighted sign
sum, `ssCount` counts overlapping adjacent SS pairs, and
`P2 z := mass z = 1 ∧ moment z = 0`. Thus `u++[S]` is an S-ended P2 prefix
and `v != []` says it is proper. Every finite A-ended word is `w++[A]`, so the
paper/card word statement and Lean theorem agree in both directions.

## Adversarial attacks

1. **Inhabitation and boundary.** Independent exhaustive enumeration found 8
   full-premise words through length 18, not zero: 3 with
   `moment+length=0`, 5 with strict negative value. Equality example
   `AASASASASSSA` has mass 0, moment -12, SS 2, and strict P2 prefix `AAS`;
   strict example `AASASASASASSSA` has moment+length -1 and the same prefix.
2. **Conclusion strictness.** Independent enumeration recorded nonempty suffix
   lengths (9 and 11 in those examples). The proof constructs suffixes by
   appending `SA` or `SSA`; `v != []` is not an assumed field or a tautology.
3. **Premise deletion.** All four weakenings have independently recomputed
   counterexamples satisfying every remaining premise and negating the
   conclusion: drop ending-A `AAASSS` (mass 0, M+n=-3, SS2); drop mass-zero
   `SASASSSA` (mass -2, M+n=0, SS2); drop moment bound `SA` (mass0, M+n=3,
   SS0); drop SS bound `AAASSSSA` (mass0, M+n=0, SS3). These are weakened-model
   counterexamples, not counterexamples to the target.
4. **E-130 control.** `AAASSSASASA` was independently recomputed as mass 1,
   moment 0, SS2, with no strict S-ended P2 prefix. It fails the new mass-zero
   premise (and has M+n=11), so E-130 remains a valid refutation of general
   SS2 prefix normalization. The target does not revive that stopped route.
5. **Vacuity/circularity.** No hypothesis is the conclusion or an unproved
   defined Prop. `P2` occurs only in the conclusion and unfolds to concrete
   mass/moment equalities. There is no `H -> H`, `x=x`, OwnerFamily field,
   stream/orbit assumption, or free-arithmetic-only result. The target has no
   `sorry`, `admit`, `native_decide`, or user axiom.
6. **Proof substance and termination.** Both inequalities structurally induct
   over Bool lists and use the older `mass_ending_A` suffix bound. The prefix
   theorem case-splits terminal `AA`/`SA` and recursively calls itself only on
   a shorter list; Lean accepts the explicit `termination_by w.length` proof.
   The terminal SSA/SSSA branches use older, acyclic
   `lowSS_A_nonpositive_prefix`/`zero_SS_nonpositive_prefix` lemmas. It is not
   an intro/exact wrapper or bare arithmetic theorem.
7. **Paper correspondence.** The general inequality is exactly
   `q+1 <= moment(X)+q|X|`; the AA/SS2 inequality is exactly
   `5 <= moment(X)+|X|`. The source sometimes retains a weaker nonpositive
   bound after algebra where the prose observes `<= -3`; this does not weaken
   the theorem signature or invalidate the case chain.
8. **Known stopped branches.** E-069/E-133 oldest-S injection, E-240 pure-AAS,
   and E-345 SS>=3 deletion are neither assumed nor concluded. H-04's
   nonminimal lag-15 counterexample and false offset-11 reading are outside the
   full premises and are not relabeled. No OS, pure-AAS, brute lag-15, or new
   global claim was introduced.
9. **Not applicable but checked.** Period boundaries, phase identification,
   minimal lag, current-A stream clocks, and orbit history are absent from the
   three local word signatures. They become obligations only downstream; their
   absence is not read as a proof about periodic words or orbits.

## Computation evidence

All sources used by the independent auditor were hashed before execution and
retained. Every command used `timeout 120`; every exit was 0; stderr was empty;
seed was `None` because all searches were exhaustive.

- Original checker replay, discovery: all binary words length 1..18, 8 premise
  cases, 0 assertion failures. Output SHA `2a6a1564...`, byte-identical to the
  frozen discovery JSONL.
- Original checker replay, known holdout: length 20 checked 8 and length 24
  checked 16, 0 failures. Output SHA `e0589e5c...`, byte-identical to the frozen
  JSONL. This is a reproduction of used data, not a new holdout.
- Independent generator: all ending-A, mass-zero, exactly-SS2 candidates were
  composed independently from positive S-runs and A gaps. Candidate pools were
  1,620 at length 20 and 3,630 at length 24; the `<=0` filter selected 8 and 16;
  all had a strict S-ended P2 prefix.
- Independent all-word counts through 18 reproduced writer totals exactly:
  target equality 3, strict negative 5; q-budget checks 434,721 for
  `q=actualSS..4`; AA/SS2 checks 45,976; failures 0. All four negative controls
  above were recomputed with conclusion `false`.
- A smaller independent inequality run through length 12 checked 11,517
  q-budget and 1,361 AA instances with failures 0; this is corroboration only.

No claimed total outside through-18 and lengths 20/24 was independently rerun.
The earlier H-05 donor-pattern ranges 11/15/19 and 23/27/31, H-02/H-03 data,
p32/33, and H-04 census were read only or outside scope and remain uncompleted
by this audit. No enumeration extension was attempted.

## Lean and harness evidence

- `timeout 120 lake env lean Recaman/SS2OldestPattern.lean`: exit 0.
- Explicit temporary `#check`/`#print axioms` for the three targets: exit 0;
  only `propext`, `Classical.choice`, and `Quot.sound` as applicable.
- `timeout 120 python3 scripts/report_vacuity.py --all ...`: exit 0,
  0/13 flagged.
- `timeout 120 python3 scripts/harness_gate.py --lint-module ...`: exit 0,
  13/13 substantive.
- `timeout 120 ./scripts/check.sh`: exit 0, 392 jobs; root reaches 389/389
  library modules; 2,572 printed declarations within allowed core axioms.

Scope qualification: modified `Recaman.lean` imports `SS2OldestPattern`, so the
whole build compiles the target. `Recaman/Audit.lean` contains no target
`#print axioms`, and registry E-360 explicitly leaves this module to a separate
audit. Therefore the whole-build axiom report does not itself audit these
declarations; the temporary explicit `#print axioms` does. No registered row
or statement-audit file exists for this candidate.

## Exact commands

```text
sha256sum ...target/card/paper/experiment...                 # before runs
timeout 120 python3 experiments/issue73_20260920/ss2_intervening_prefix.py --mode discovery
timeout 120 python3 experiments/issue73_20260920/ss2_intervening_prefix.py --mode holdout
sha256sum /tmp/.../independent_check.py >> PRE_RUN_SHA256SUMS
timeout 120 python3 /tmp/.../independent_check.py
sha256sum /tmp/.../inequality_check.py >> PRE_RUN_SHA256SUMS
timeout 120 python3 /tmp/.../inequality_check.py
sha256sum /tmp/.../full_counts_check.py >> PRE_RUN_SHA256SUMS
timeout 120 python3 /tmp/.../full_counts_check.py
sha256sum /tmp/.../TargetAxioms.lean >> PRE_RUN_SHA256SUMS
timeout 120 lake env lean /tmp/.../TargetAxioms.lean
timeout 120 python3 scripts/report_vacuity.py --all Recaman/SS2OldestPattern.lean
timeout 120 python3 scripts/harness_gate.py --lint-module Recaman/SS2OldestPattern.lean
timeout 120 lake env lean Recaman/SS2OldestPattern.lean
timeout 120 ./scripts/check.sh
```

Raw stdout/stderr and literal exit files are beside this report. The first
independent combined checker took longer than expected because its independent
composition enumerator was intentionally generic, but it completed with exit 0
inside the 120-second cutoff; there was no timed-out or deleted failed source.

## Dependency obligations and next decision

Not audited as results: `p2_append_A_tail_data`,
`ss2_aas_oldest_has_prefix`, `ss2_no_w1_oldest`, `oldestOffset_le_length`,
`oldestOffset_split`, `ssCount_append_replicate_A`, `past_oldest_split`,
`oldest_cover_clock_lt`, and `past_oldest_cover_decomposition`; the three w1
placements; E-360's W-dependent future-AAS consequence; H-03 prefix reduction;
periodic lift; tight-set avoidance; deletion; full supply; general lag; actual
orbit. `OwnerFamily` remains exactly the four fields `window/addA/own_mem/onto`;
none is silently discharged here. E-351 must not be used circularly to prove W.

Next decision: archive this bounded audit and stop. It supports the meaning of
the three local declarations, but H-05 remains `CONJECTURED` and procedurally
`未完了`. Do not register or promote the whole H-05 claim. Any future use of the
downstream chain needs a fresh bounded card and independent entry review before
formalization, plus its own statement/semantic audit afterward.
