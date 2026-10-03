# E-360 registration draft scope

- First exact clock sample: 2026-09-21 02:06:35 JST
- Three-symbol revision clock sample: 2026-09-21 02:11:34 JST
- Three-symbol draft freeze sample: 2026-09-21 02:13:41 JST
- HEAD: `08c08565c743f39350c9b959e1df7d30aa1cae5d`
- Bounded question: can the independently audited, frozen W/Q core be represented by one exact
  new registry row and its official-form G5 audit, without importing any unreviewed theorem or
  enlarging the mathematical claim? The initial two-symbol metadata draft was rejected because it
  omitted the `own t = t - 7` half of W; this is a citation correction, not a mathematical repair.
- Acceptance test:
  1. the proposed ID is exactly one above the current maximum (`E-360` after `E-359`);
  2. the row cites the minimum three symbols needed to register both exact W conclusions and Q;
  3. the G5 draft quotes all three cited signatures verbatim and answers all three checks;
  4. the full 10-theorem core and two existing constructors remain traceable to the frozen
     pre-registration packet;
  5. isolated-copy G1-G5, protected-claim, lint, vacuity, statement-signature, and full checks pass;
  6. a separately owned semantic auditor approves this exact row and G5 before any live ledger edit.
- Stopping condition: stop without applying if a frozen source hash changes, any gate fails, the
  independent auditor rejects or requests mathematical repair, or the 02:25 JST worker deadline is
  reached. No mathematical repair, new Lean theorem, new search, or holdout run is allowed here.

## Frozen source boundary

| Source | SHA-256 | Included boundary |
|---|---|---|
| `Recaman/ShortTightDonorAvoidance.lean` | `bb12f35acc8e48c584cead52d675e36b034afda22f0f28ecfd245031f70fee85` | lines 1--358, through `short_tight_avoids_ss2_donor` |
| `Recaman/OwnerFamilyLagEleven.lean` | `0bc2293b5d67f7ef5865f7a3f67b2fbf10aeb76bfa92eac9a086cc893c5846f4` | existing `OwnerFamily` and `ownerFamily_of_minimal` dependency |
| `Recaman/PeriodicOwnerFamilyLagEleven.lean` | `a90c8f2ac7e6b98dfda4a260434d2e44d3e35781c3212f6a04b7952e9ef6b4c0` | existing `tight_owner_family` dependency |

The proposed audit symbols are exactly:

1. `Recaman.ShortTightDonorAvoidance.w1_owns_oldest`
2. `Recaman.ShortTightDonorAvoidance.w1_next_addition`
3. `Recaman.ShortTightDonorAvoidance.short_tight_avoids_ss2_donor`

The first two are the exact conditional local W (`own t = t - 7` and next A) and explicitly retain
the defined `OwnerFamily` premise. The third is the strongest audited concrete Q: arbitrary positive period, no period upper bound,
nodup/tight/current-A/minimal-P2 B windows with lag in `{3,7,11}`, and a minimal lag-11 SS=2 donor.
It concludes only that the donor's true-oldest-S phase is outside `neighborhood e p B lag`.

Excluded: lines 360 onward, `SS2OldestPattern`, p32/33 as independently certified evidence,
arbitrary lag, general Gate T6, E-070/E-067, actual-orbit claims, and Recamán-sequence surjectivity. The extracted
constructors are existing E-357/E-359 proof structure and are not counted as new results.
