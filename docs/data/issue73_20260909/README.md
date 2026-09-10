# Issue 73: September 9 research evidence

This bundle preserves two separate runs: the earlier catalytic-lookahead
refutation and the later one-hour leading-run / sharp-window research.

## Earlier run: bounded catalytic lookahead

F_1 and its only allowed repair F_2 are `REFUTED` on 11-sign windows.
This experiment is `STOPPED`; E-067/E-070 remain `CONJECTURED`.
The [hypothesis card](../../HYPOTHESIS_CARD_2026-09-09_CATALYTIC_LOOKAHEAD.md)
contains the exact quantifiers, the predeclared ranges, and the full handoff.

Base revision: `8dfbfb8f15eb2ff3d84629385cde99cd9f2bc9aa`.
New scripts were working-tree files when executed. [SHA256SUMS](SHA256SUMS)
freezes source and output identity; each output also prints the script hash.

## Reproduction

Run from repository root and redirect new runs to `/tmp`, preserving this bundle.

```sh
PYTHONDONTWRITEBYTECODE=1 python3 experiments/issue73_20260909/catalytic_lookahead.py --k 1
PYTHONDONTWRITEBYTECODE=1 python3 experiments/issue73_20260909/catalytic_lookahead.py --k 2
PYTHONDONTWRITEBYTECODE=1 python3 experiments/issue73_20260909/verify_catalytic_witnesses.py
shasum -a 256 -c docs/data/issue73_20260909/SHA256SUMS
```

| Frozen output | Exact result |
|---|---|
| [catalytic_k1.txt](catalytic_k1.txt) | L=3,7 have zero failures; L=11 has 21 failing S edges; witness R_1: 1→3 |
| [catalytic_k2.txt](catalytic_k2.txt) | L=3,7 have zero failures; L=11 has 10 failing S edges; witness R_2: 0→2 |
| [independent_verify.txt](independent_verify.txt) | All 156 / 1,884 representatives per window independently enumerated; exact upper bounds and witnesses agree |

All A edges pass; the all-L A inequality has the paper prepend-A argument.
The failed inequalities are S edges, which must satisfy R_k(after)≤R_k(before)+1.
Conditional holdout L=15,19 was not run. This is not a new lag-capacity table
and gives no periodic capacity counterexample. That earlier run changed no Lean source.

## One-hour run: leading runs, sharp windows, and non-nested resets

The [handoff](../../ONE_HOUR_RESEARCH_2026-09-09.md) records the exact claims
and scope. Hypothesis cards H-03..H-07 were written before their falsifiers.
The proposed non-nested counterfamily is an analytic proposal, not a blinded
discovery claim. All scripts print HEAD and their own source hash.

| Output | Protocol and result |
|---|---|
| [leading_run_supply.txt](leading_run_supply.txt) | H-03: all P2 windows through d=19 and sharp-family prefixes m=3..128; no violations |
| [sharp_partitions.txt](sharp_partitions.txt) | H-04: two independently generated complete sets agree at m=1..24 |
| [nested_supply_gap.txt](nested_supply_gap.txt) | H-05: exact tail enumeration; zero-contact cells explicitly retained |
| [sharp_capacity_extension.txt](sharp_capacity_extension.txt) | H-06: L=11/15, all sharp words through m=24; only lag-3 contact, no protected-S collision |
| [nonnested_lag_drop.txt](nonnested_lag_drop.txt) | H-07: minimal-lag drop family at r=2..64, every prefix checked |
| [nonnested_periodic_verify.txt](nonnested_periodic_verify.txt) | H-07 audit: separate modular-time implementation, positive period sum 3, same minimal lags |
| [lag_drop_scope_control.txt](lag_drop_scope_control.txt) | H-07 r=2 only: existing all-lag formula agrees with direct replay; 5 supplied A≤11 S |
| [one_hour_check.txt](one_hour_check.txt) | Full Lean build and 1,265-declaration permitted-axiom audit passed |
| [final_metadata_check.txt](final_metadata_check.txt) | Final registry/import-contract checks after documentation updates |
| [semantic_audit.md](semantic_audit.md) / [semantic_statements.txt](semantic_statements.txt) | Signature-to-prose audit; old short injection assumed, new sharp injection proved |

Reproduction from repository root (redirect new outputs to `/tmp`):

```sh
PYTHONDONTWRITEBYTECODE=1 python3 experiments/issue73_20260909/leading_run_supply.py
PYTHONDONTWRITEBYTECODE=1 python3 experiments/issue73_20260909/sharp_partitions.py
PYTHONDONTWRITEBYTECODE=1 python3 experiments/issue73_20260909/nested_supply_gap.py
PYTHONDONTWRITEBYTECODE=1 python3 experiments/issue73_20260909/sharp_capacity_extension.py
PYTHONDONTWRITEBYTECODE=1 python3 experiments/issue73_20260909/nonnested_lag_drop.py
PYTHONDONTWRITEBYTECODE=1 python3 experiments/issue73_20260909/verify_nonnested_periodic.py
PYTHONDONTWRITEBYTECODE=1 python3 experiments/issue73_20260909/verify_lag_drop_scope.py
./scripts/check.sh
bash scripts/check_research_registry.sh
bash scripts/check_module_architecture.sh
shasum -a 256 -c docs/data/issue73_20260909/SHA256SUMS
```

The universal mathematical claims use Lean or the complete recorded paper
proofs, never extrapolation from these finite ranges. The manifest also
freezes the two new Lean modules and their import/audit integration.
