# H-20260920-03, 2026-09-23 02:00 candidate packet

## Conclusion first

The exact card is inhabited, but the claimed strict full-P2 prefix reduction
has no tight witness in its predeclared finite ranges. The existing Lean
equality theorem is valid for a broader domain: it drops full-window P2 and
minimality of the chosen prefix. A strict tight instance of that broader
theorem exists at p4, but its full lag4 window is **not P2** and therefore
does not establish strict nonvacuity of the original card. The source proof
is a direct composition of existing short Hall, prefix inclusion, and equal
finite lengths. H-03 stays `CONJECTURED`; overall procedural judgment remains
pending independent audit, with the historical preformalization entry gap
unrepaired. No new research route or registration is proposed.

## Frozen question, acceptance, stop

Question: For exactly the card's P2 full windows and least P2 prefixes,
does tightness yield a meaningful nonidentity equality, and does the Lean
source express that claim? Acceptance requires a verbatim statement audit,
full-P2 strict/tight example or an explicit gap, positive controls and
countercontrols, frozen replay, Lean gates, and independent Sol review.
Stop this slot if no strict exact-premise witness is found in already
declared ranges; do not infer universal absence or extend the range for
novelty. The proof statement is not repaired or weakened.

HEAD `08c08565c743f39350c9b959e1df7d30aa1cae5d`.
Target Lean SHA-256 `bb12f35acc8e48c584cead52d675e36b034afda22f0f28ecfd245031f70fee85`.
Original card SHA-256 `3ad887aff9cf89b84471de4a8f85b62cb8abe5d411455e3c085e8e0cb1771b16`.
Exact frozen source/card/experiment are local snapshots; the original
dirty files remain untouched.

## Three distinct domains

1. Exact card, nonempty identity: period4 `AAAS`, `B=[2]`,
   `m(2)=lag(2)=3`, `past=AAS` (P2), `N=[3]`, `|N|=|B|=1`.
   This shows the entire implication is not empty. It does not exercise
   a shorter prefix.
2. Exact card, strict `m<lag`, tight: original p1..12 census and p15
   historical holdout enumerate 1,141 and 8,115 nonminimal assignments,
   respectively, but `tight_nonminimal=0` in both. Our independent singleton
   p1..12 control likewise finds zero. Thus the strict subdomain is
   unexercised in these finite ranges. Its global satisfiability is unknown.
3. Broader Lean source, strict and tight: period4 `AAAS`, `B=[2]`,
   `m=3`, `lag=4`, `past3=AAS`, `past4=AASA`, `N_m=N_lag=[3]`.
   `P2(past4)=false`. This proves the source's strict domain is inhabited,
   but it is not a witness for domain 2. Source minimality of m is absent,
   though m happens to be least in this example.

The period9 `ASAAASASS`, `B=[4]`, `m=3`, `lag=7` is an exact full-P2
strict *nontight* control: `past3=AAS`, `past7=AASASSA`,
`N_m=[1]`, `N_lag=[1,7,8]`. It shows tightness carries the equality.
The original experiment's `PASS` requires positive total counts for
nonminimal assignments, changed nontight neighborhoods, and donor checks.
It does **not** require `tight_nonminimal>0`; its pass status is not an
acceptance of original strict-case nonvacuity.

## Statement and dependencies

The verbatim source signatures, both directions of the semantic map, and
the dependency analysis are in `statement_audit.md`. The source theorem
requires `m<=lag<=11`, P2 at m, and tightness, but not P2 at lag or
minimality of m. The original card implies its premises by
`exists_minimal_p2_prefix`; source examples without P2 at lag cannot run
backwards as original examples. `neighborhood_prefix_sublist` uses only
window inclusion. `short_window_hall` on m, inclusion, and tight finite
length yield equality. There is no H-02 premise in this chain.

`short_p2_tight_avoids_ss2_window` later uses the equality to call
`short_tight_avoids_ss2_window`; `short_p2_ss2_deletion` uses the result
in its tight branch. H-02 has a limited semantic pass and an overall
procedural **未完了** verdict from 01:30, so those downstream claims are
an inventory only. E-360's W dependency `w1_future_aas_member` is existing,
not a new H-03 input. This packet makes no established inference from H-02.

## Evidence and controls

The original experiment replay is byte-identical to the daytime discovery
and p15 holdout JSONL, including 32,768 p15 cycles, 62,545 assignments,
8,115 nonminimal assignments, 39,340 tight assignments,
0 tight/nonminimal assignments, 4,590 tight donor checks,
10,890 deletion checks, and 7,995 nontight changed neighborhoods.
All counters are finite signword computations. They neither prove the
unbounded theorem nor say anything about actual Recaman orbit realization.
The p15 holdout is already used and is not new evidence by being replayed.

The same replay keeps the E-345 SS>=3 deletion counterexample. E-240
refutes pure-AAS forcing; this equality does not force pure AAS. E-069
refutes global oldest-S injection; the short Hall proof uses an existing
short selector, not that global map. E-180 refutes collision-slack-linear
and is unrelated. H-04's nonminimal lag15 counterexample remains outside
the short-window bound and warns against fixed offset11 for true oldest S.
None is a counterexample to the exact equality.

`report_vacuity.py --all` found 0/21 flagged; module lint found 20/21
substantive; `./scripts/check.sh` passed 392 jobs and the 2,572-declaration
axiom audit. Kernel `#check` and `#print axioms` on the three direct lemmas
are in `signature.stdout`. These gates do not resolve the strict-case
nonvacuity or historical entry procedure.

## Failure, uncertainty, decision

There were no failed commands used as positive evidence. The finite zero
strict/tight count is a failed *acceptance condition* in the original card,
not a counterexample to equality and not a proof that such assignments
never exist. No exact-premise strict tight witness is asserted. The
independent auditor must decide whether this is a procedural 差戻し or
未完了; neither should be confused with `REFUTED` or a global STOPPED claim.
The old daytime formalization lacked an independent preformalization
entry check; this later audit cannot be retroactive.

The recommendation is to keep H-03 `CONJECTURED` and stop presenting the
strict full-P2 reduction as an exercised new mathematical input. The next
decision is whether an independently audited, exact-premise strict/tight
realization exists or whether a separate proof rules that domain out.
No cap extension, new Lean module, or route repair belongs to this slot.

Changed files: only the `slot0200/` packet and `proposed_card_final.md`.
The latter is a proposed full-card version for the parent to apply only
after independent review. No actual card, registry, frontier, proof map,
root, Audit, gate, or protected claim was edited; no stage/commit occurred.
Exact commands, pre-run hashes, timeouts, exits, and raw streams are in
`commands.md`; `SHA256SUMS` verifies packet contents.

Planned parent audit: `docs/adversarial_audits/H-20260920-03_20260923_0200.md`.
Daily handoff: `docs/RESEARCH_HANDOFF_2026-09-23_SOL.md`.
