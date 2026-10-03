# H-20260917-01: 2026-09-20 02:30 closeout inventory adversarial audit

## Conclusion

**Procedure: PASS**, for the corrected target only. The inventory is consistent with the preserved
records and it is appropriate to close tonight without promoting any evidence. This pass covers
record consistency and the decision to stop tonight only; it is **not mathematical progress** and
does not establish Q, W, or `W_partial`.

The first target (`17e03d95...`) was returned because its unqualified phrase
`pure-AAS/geometric route` could expand E-343 beyond its recorded scope. The corrected target limits
that stop to E-343's E-297--E-317 geometric/pure-AAS branch and explicitly does not stop geometric
methods in general. The corrected target hash is `2c10fbf84e25f36db9c18ed5bed71227df022e10c87228f8839a93fc0a767cd2`.

## Target and exact claim

- Card: `H-20260917-01`.
- Audit time: start `2026-09-20 02:33:11 JST`; finalization before the 02:46 cutoff.
- HEAD: `08c08565c743f39350c9b959e1df7d30aa1cae5d`.
- Implementer: `/root/sol_20260920_close0230`; independent auditor:
  `/root/sol_20260920_close_audit0230`; parent: `/root`.
- Target: `docs/data/issue73_20260920/slot0230/closeout_inventory.md` at the hash above.
- Claim audited: every candidate, failed version, and unresolved obligation from the 01:00,
  01:30, and 02:00 slots is classified consistently with its source evidence, and none is used as
  an established premise when closing tonight.

## Attacks and source checks

All six preserved manifests verified with exit 0: daily data 7 entries, slot0130 13, slot0200 6,
01:00 audit 6, 01:30 audit 3, and 02:00 audit 5. Direct hashes match the inventory for the baseline,
gate, v2 probe, three audit records, and all manifest objects. The baseline/gate/v2 source was read;
raw outputs and addenda were compared with the inventory. This slot did not rerun the mathematical
enumerations and does not pretend to have independently recomputed the three earlier audits.

The following adversarial distinctions survive intact:

1. 01:00: p=1..11 gives only finite `OBSERVED` evidence (1,872 positive words, Q donor 52,
   Q nonempty 52, W antecedent 32, violations 0). The original p=1..15 run was exclusive-bound,
   interrupted with exit 130 and empty stdout; the inclusive p=1..11 recovery does not replace it.
2. 01:30: the gate accepts duplicate PERIOD rows, negative-count cancellation, and a garbage Q
   witness under mocked subprocess output. That rejects the gate implementation, not the normal
   pinned baseline and not Q/W.
3. 02:00: v1 mixed the conclusion negation into the antecedent and its source body is not preserved.
   V2 exits 0 with `EXHAUSTED_ZERO`, but the accepted target is empty. Independent census found
   proper U=3314 (including empty U), partial tight B=1166, partial W antecedent=0; all 32 full-U
   antecedents had B=full Supp. These are diagnostics, not support for W.
4. The p12 SS-relaxed Q counterexample and p8 tightness-relaxed W counterexample remain weakened
   controls, not counterexamples to original Q/W. p8 Q and p10 W remain finite non-vacuity controls.
5. Source signatures confirm E-351 assumes future A/U membership/lag 3; using it to prove W would
   be circular. E-359 remains conditional on Hall, short minimal windows, and periodic transfer.
   E-240 refutes pure-AAS forcing only. No hidden-Prop, H->H, x=x, free-arithmetic, wrapper, or
   conclusion-as-hypothesis claim was promoted by this closeout.

## Remaining uncertainty and stop boundary

General Q/W remain `CONJECTURED`; `W_partial` is unclassified; the p=32,33 holdout and individual
weakening checks remain undone. Integer-clock/phase transfer, complete-U/minimum-lag premises for
E-359, and Hall preservation for donor-containing subsets remain unresolved. Finite-to-all-period,
periodic-word-to-orbit, and G2-to-general-Gate-T6 transitions remain prohibited.

The stopped objects are the 01:30 gate implementation, the 02:00 partial-U experiment after its one
repair, the already stopped E-343 E-297--E-317 branch, old OS/MD pre-assumption, and brute-force lag-15
certificate formalization. Q/W and the mathematical route as a whole are not marked `STOPPED`.

## Final decision

The corrected closeout inventory **passes**. Close the night with no evidence promotion, no Lean
entry, no registry/frontier/proof-map change, and no reuse of the defective gate. Reopening the
partial-U experiment requires a nonempty proper-U tight-w1 instance or a separately frozen question
with a non-vacuous acceptance contract. The full command/output record is in `command_log.txt`.
