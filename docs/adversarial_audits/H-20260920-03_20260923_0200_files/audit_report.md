# H-20260920-03 independent audit, 2026-09-23 02:00 JST

## Conclusion and scope

**Mathematical verdict: limited semantic pass for the existing equality; strict nonidentity content under the original card is unverified. Overall procedural verdict: 未完了.** Keep H-03 `CONJECTURED`; do not register or promote it, or treat its downstream avoidance/deletion claims as established. This is not `REFUTED`, a universal emptiness result, or a new `STOPPED` branch. The missing independent preformalization entrance check from 2026-09-20 cannot be retroactively performed. The original finite protocol contains zero tight assignments with a nonminimal full-P2 window, despite positive nonminimal and tight counts separately. The earlier H-02 audit likewise ended overall 未完了 and cannot serve as a certified premise here.

One bounded question was audited: does the card's tight prefix reduction have an inhabited strict case under *all original premises*, and what does the current Lean theorem actually say? Acceptance required the exact semantic map, finite entrance count, controls, source/Lean diagnostics, and historical procedure; stop this slot at the frozen p1..12/p15 protocol without a strict exact-premise witness. There was no Lean or research-source edit by this auditor. The parent owns the repo audit and card application.

## Versions and exact objects

- HEAD: `08c08565c743f39350c9b959e1df7d30aa1cae5d` (dirty worktree; no stage/commit by auditor). Frozen target `Recaman/ShortTightDonorAvoidance.lean`: `bb12f35acc8e48c584cead52d675e36b034afda22f0f28ecfd245031f70fee85`. Original H-03 card: `3ad887aff9cf89b84471de4a8f85b62cb8abe5d411455e3c085e8e0cb1771b16`. Original daytime experiment: `95eb3fb1f49c20087fea345ec1404461ddebc8f0bf0751d9e2c1f41e44830a61`.
- Writer frozen packet: `candidate_packet.md` `2b9ea53dadc6f65a701e532e7c5486959683ba46c1ed0ca640ef9fe72c4635d6`; final proposed full card `8064b182c7f6e39a9571b06d0b43bc682d4c7cafae263722c4c8531aff8bd5ec`; `statement_audit.md` `c2876d3af82802610d837b901a0b79e62eb67e386d97cb00af4f1caf1d5984cd`. Writer `SHA256SUMS` `69c756ee6da3492821e3533498b3fd305d3ee1428c1239961a3cb72aaad5b0a1`, 25/25 entries verified directly. The earlier pending-verdict card `10d10a5b0ed39e4bc4d5266f28fd177e52b72d62d3e960ffc103205d0b81b98f` and manifest `54166ef99cf35f0a9990acfca81a3a83c6358333296579e1194d8a3099f8b257` remain preserved. The revised proposed card accurately records this limited semantic pass and overall 未完了 and is approved as a record, not as research promotion. The actual original card remained unchanged at review time.

`P2(w)` is `mass w = 1 ∧ moment w = 0`, with mass the sign sum and moment the offset-weighted sign sum. `past e t d` lists `e(t-1),...,e(t-d)`. `neighborhood e p B lag` filters the subtraction phases in `0..p-1` by actual modular coverage from those windows. Periodic `e` is an arbitrary integer-indexed Bool stream, not a Recaman orbit. `B` is nodup, in-range, and current A; no full U, positive drift, or donor is required for the equality. Periodicity, current-A, P2 prefix, and lag bound feed the established short injection/Hall lemma. The `OwnerFamily` fields and W theorem are not premises of the equality.

The literal equality signature at target lines 572-579 is:

```lean
theorem tight_neighborhood_eq_of_p2_prefix (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (B : List Nat) (m lag : Nat → Nat) (hBn : B.Nodup)
    (hBp : ∀ b ∈ B, b < p) (hBA : ∀ b ∈ B, e (b : Int) = true)
    (hle : ∀ b ∈ B, m b ≤ lag b) (hbound : ∀ b ∈ B, lag b ≤ 11)
    (hP : ∀ b ∈ B, P2 (past e (b : Int) (m b)))
    (htight : (neighborhood e p B lag).length = B.length) :
    neighborhood e p B m = neighborhood e p B lag := by
```

There is no `P2(past ... (lag b))` and no leastness of `m` in that signature. `exists_minimal_p2_prefix` (lines 533-546) takes full-window P2 and returns an `m≤d` with P2 and no shorter positive P2 prefix. `neighborhood_prefix_sublist` (lines 550-569) uses only `m≤lag` and actual coverage, without P2 or periodicity. Thus **original card -> Lean theorem** is valid after selecting least prefixes; **a direct Lean instance -> original card instance** is invalid in general. The actual proof invokes `short_window_hall` on `m` to obtain `|B|≤|N_m|`, then inclusion `N_m ⊆ N_lag` and tightness `|N_lag|=|B|` force list equality. It neither assumes its conclusion nor merely proves `x=x`; it is also a direct finite-cardinality consequence of established Hall plus the new inclusion. Harness `SUBSTANTIVE` is a syntactic result, not a finding that strict full-P2 shortening is inhabited.

## Independent finite falsification and controls

The frozen independent checker `independent_prefix_check.py` (pre-run SHA `b35c09ec1b8bb345a6abafe515a23832f52c13f4e4d761afe1bfcdaae39bd236`) separately implements weighted P2, backward windows, modular subtraction neighborhoods, all A-phase sublists and alternative lag assignments, least positive prefix, and all length-11 P2/SS2 donor clocks. It asserts each original premise before checking equality, avoidance, and deletion. For p1..12 (8,190 cycles total): 1,141 nonminimal assignments, 0 tight nonminimal, 1,108 changed nontight neighborhoods, and 609 tight donor checks. For p15: 32,768 cycles, 62,545 assignments, 8,115 nonminimal, 39,340 tight, **0 tight nonminimal**, 7,995 changed nontight, 4,590 tight donor checks, and 10,890 deletion checks. No assertion failed. The p15 counts and cycle digest exactly match the old JSONL; the old discovery totals also match. This is independent reproduction of **already consumed** discovery/holdout, not a new holdout or proof of universal emptiness. The original script's final `PASS` asserts only positive totals for nonminimal assignments, changed nontight neighborhoods, and donor checks. It does not demand `tight_nonminimal>0`.

Positive and negative controls were checked independently, including the writer's literals:

- Exact-card nonempty identity: p4 `AAAS`, `B=[2]`, `m=lag=3`, current A, `past=AAS` P2, `N=[3]`, and `|N|=|B|=1`. So the *whole implication* is inhabited, while its strict `m<lag` subdomain was not exercised in the frozen ranges.
- Broader Lean strict/tight: same p4 `AAAS`, `B=[2]`, `m=3`, `lag=4`, `past4=AASA`, P2 at 3 true and P2 at 4 false, `N_m=N_lag=[3]`. It meets the Lean signature and proves that signature has nonidentity instances, but fails the original full-window P2 premise. My rotated p4 `SAAA`, `B=[3]` instance was also directly evaluated by Lean: past3 `[true,true,false]`, past4 `[true,true,false,true]`, P2 true/false, and neighborhoods `[0]`/`[0]`.
- Remove tightness: p9 `ASAAASASS`, `B=[4]`, `m=3`, `lag=7`; both windows P2, `N_m=[1]`, `N_lag=[1,7,8]`, so equality fails. My p15 nontight control gives the same failure with `B=[6]`, `m=3`, `lag=7`, `N_m=[3]`, `N_lag=[2,3,14]`.
- Remove P2 at `m`: on p4 `SAAA`, `B=[3]`, choose `m=0`, `lag=4`; all other Lean equality premises including tightness hold, but `N_m=[]` and `N_lag=[0]`. This tests that the Hall-producing P2 premise is material. `B=[]` is trivial and was not used as a nonvacuity witness.

The writer's `prefix_semantics.py` and raw output were read directly; its p1..12 singleton counts are 5,786 strict/tight broader-source instances, 5,630 exact-card tight identity instances, 945 exact-card strict/nontight instances, and 0 exact-card strict/tight singleton instances. The original all-sublist experiment is stronger for the last finite entrance count. I independently recalculated the writer p4 and p9 literals with the frozen checker and read the byte-identical replay logs. All finite claims are `COMPUTED` at their stated scopes. No finite zero was converted into an infinite theorem.

I started an unplanned extension to p13/14/16/17 before the parent narrowed the audit back to the declared ranges; it completed, but is quarantined as exploratory raw and **not** used for acceptance, holdout, novelty, or general emptiness. A subsequent p18/19 command was interrupted on the parent's instruction (exit 130) before any period result, and its source and partial stdout/stderr remain intact. No failed source was overwritten. No range extension supports the verdict.

## Dependencies, rejected leaps, and gates

`short_window_hall` uses the existing short selector and its injectivity on short supplied phases; it does not assume full-U Hall or use the refuted global oldest-S injection E-069. The equality chain has no H-02 or circular E-351 premise. The later `short_p2_tight_avoids_ss2_window` calls the H-02 theorem `short_tight_avoids_ss2_window` after reduction, and `short_p2_ss2_deletion` calls that transport in its tight branch. The H-02 01:30 audit recorded a limited semantic pass but total procedural 未完了; those later claims are dependency inventory, not certified new consequences in this audit. `w1_future_aas_member` remains an existing E-360 W dependency. E-240 refutes pure-AAS forcing, E-345 is the SS>=3 deletion countercontrol, E-180 concerns collision-slack-linear, and H-04's p16 lag15 true-oldest example is outside `lag≤11`; no fixed offset11 was substituted. Nothing here proves full-U capacity, general Hall/Gate T6, all lag, actual-orbit behavior, or surjectivity.

Direct diagnostics: `report_vacuity.py --all` exit 0, 0/21 flagged; `harness_gate.py --lint-module` exit 0, 20/21 substantive; `./scripts/check.sh` exit 0, 392 jobs and 2,572 declarations within `{propext, Classical.choice, Quot.sound}`; temp `#check`/`#print axioms` exit 0 and those same ordinary axioms for the equality. No `sorry`, `admit`, `native_decide`, or user axiom appears in the target. These gates establish Lean acceptance and dependency hygiene within their limits, not original strict-case nonvacuity. No new E-row statement audit was made or claimed; the writer's `statement_audit.md` is a candidate semantic audit, while E-360 registers earlier target lines only.

## Commands, raw evidence, and next decision

Auditor cwd was the repository root. Raw stdout/stderr are in `runs/`; original frozen sources are in `frozen/`. All completed commands had exit 0 unless noted. Exact bounded commands include:

```sh
gtimeout 90s python3 -u /tmp/recaman-audit-20260923-0200-sol/independent_prefix_check.py --periods 1 2 3 4 5 6 7 8 9 10 11 12 15
gtimeout 10s python3 -u /tmp/recaman-audit-20260923-0200-sol/prefix_controls.py
gtimeout 60s lake env lean /tmp/recaman-audit-20260923-0200-sol/prefix_literal_eval.lean
gtimeout 90s lake env lean /tmp/recaman-audit-20260923-0200-sol/prefix_diagnostic.lean
gtimeout 90s python3 scripts/report_vacuity.py --all Recaman/ShortTightDonorAvoidance.lean
gtimeout 90s python3 scripts/harness_gate.py --lint-module Recaman/ShortTightDonorAvoidance.lean
gtimeout 180s ./scripts/check.sh
```

There was no random sampling (seed: none), cap hit, or error in the frozen-scope checker. The old source revision and each exact period/cycle digest are in raw JSONL. Independent sources and literal diagnostics have pre-run hashes and were not modified after their successful runs. Writer packet/source/raw and its manifest were independently read and verified. The original card and Lean target matched the frozen hashes during audit.

Remaining uncertainty: a strict full-P2/tight assignment under the exact original premises may exist at another period, or it may be universally impossible; neither is decided. The mathematical equality is supported by Lean's actual theorem, but whether strict reduction is a new usable input under the original card is not established. Recommendation: retain H-03 `CONJECTURED`, record the limited pass and procedural 未完了, do not present the old `PASS` as a nonvacuous strict test, and do not promote the downstream H-02-dependent claims. Resume this *specific* question only with an independently audited exact-premise strict/tight witness or a distinct proof that such a witness cannot exist; do not relabel a broader Lean instance as a card witness. No cap extension or new global route is authorized by this audit.
