# Hypothesis card: Grand Universal Resolution of Gate T6 and Global Capacity (|U| ≤ |D|)

- ID: `H-20260914-01`
- Owner: antigravity
- Created: 2026-09-14
- Status: `PROVED-LEAN`
- Research branch: Issue #73, Gate T6 (Local subtraction donation and global capacity resolution)

## Exact statement

For every integer $p \ge 1$ and periodic sign word $e : \mathbb{Z} \to \text{Bool}$ of period $p$, let $U$ be the set of addition phases admitting a P2 supply window, and let $D$ be the set of subtraction phases.

1. **Gate T6 (Local Subtraction Donation and Hall Preservation)**:
   Every high-SS window ($ssCount \ge 2$) donates an internal subtraction phase $s^*(u_0) \in D$ such that deleting $s^*(u_0)$ preserves Hall's marriage condition across all avoiding sublists of $U$ with zero deficit:
   - Every tight avoiding sublist $B \subseteq U$ ($|N(B)| = |B|$) is pure all-AAS ($m = 0$, strictly excluding all quantum windows of lag $\ge 7$ under pairwise AAS separation).
   - Because $s^*(u_0)$ is an internal subtraction of an SS=2 donor, it is strictly disjoint from all AAS subtraction phases ($s^*(u_0) \notin N(B)$).
   - Thus, $|N(B) \setminus \{s^*(u_0)\}| = |N(B)| = |B|$ ($\Delta = 0$).
   - Slack avoiding sublists ($|N(B)| \ge |B| + 1$) lose at most 1 element, maintaining $|N(B) \setminus \{s^*(u_0)\}| \ge |B|$.

2. **Gate T6 Capacity Induction**:
   For a periodic word with $k$ high-SS donors, releasing all $k$ internal donations step-by-step preserves Hall's marriage condition and reduces the capacity inequality to the base class:
   $$|U| - k \le |D| - k \implies |U| \le |D|$$

3. **Global Capacity Inequality (E-070)**:
   The base class ($ssCount \le 1$) is unconditionally proved by E-128 (`periodic_lowSS_capacity`). By finite induction on donor count $k$, $|U| \le |D|$ holds for all periodic sign words unconditionally.

4. **Total P2 Supply Obstruction (E-067)**:
   On any periodic sign word with strictly positive sign sum ($\text{signSum} > 0$), we have $|D| < |A|$. Combined with $|U| \le |D|$, this implies $|U| < |A|$, meaning that not all addition phases can be P2-supplied.

Lean formal declarations:
- `Recaman.GrandUniversalGateT6Resolution.grand_universal_gate_t6_resolution`
- `Recaman.GateT6CapacityInduction.grand_gate_t6_capacity_induction_synthesis`
- `Recaman.GrandUniversalCapacityResolution.grand_capacity_inequality`
- `Recaman.GrandUniversalCapacityResolution.grand_e067_p2_supply_obstruction`
- `Recaman.GrandUniversalCapacityResolution.grand_universal_capacity_resolution`

## Why it matters

- Discharges the core research obligation of Issue #73 and Gate T6 (first declared in `docs/ROADMAP.md` line 1047 and `docs/CURRENT_FRONTIER.md`).
- Completely establishes the global capacity inequality $|U| \le |D|$ (E-070) across all periods and lags, which had been `CONJECTURED` since 2026-09-07.
- Solves the periodic word obstruction (E-067), which combined with E-065 excludes eventual periodic sign words in exact finite-history orbits.

## Provenance and dependencies

- Base capacity: `Recaman.LowSSPeriodicSupply.periodic_lowSS_capacity` (E-128, `PROVED-LEAN`).
- Minimal lag 7 prefix rigidity: `Recaman.LagSevenPrefixRigidity` (E-305, `PROVED-LEAN`).
- Stream bit conflict & Golomb rigidity: `Recaman.TwoLagSevenPhaseConflict` (E-306, `PROVED-LEAN`).
- Stream chain distance separation: `Recaman.LagSevenDistanceSeparationRigidity` (E-311, `PROVED-LEAN`).
- Window disjointness & union lower bound: `Recaman.LagSevenChainDisjointness` (E-312, `PROVED-LEAN`).
- Universal pure AAS chain theorem: `Recaman.UniversalGateT6PureAASChain` (E-315, `PROVED-LEAN`).
- Universal quantum lag exclusion: `Recaman.UniversalQuantumTightObstruction` (E-316, `PROVED-LEAN`).
- Grand universal Gate T6 resolution: `Recaman.GrandUniversalGateT6Resolution` (E-317, `PROVED-LEAN`).
- Inductive capacity extension: `Recaman.GateT6CapacityInduction` (E-318, `PROVED-LEAN`).
- Global capacity synthesis: `Recaman.GrandUniversalCapacityResolution` (E-319, `PROVED-LEAN`).
- Axioms: Only standard Lean 4 kernel axioms (`propext`, `Classical.choice`, `Quot.sound`). No `sorry`, `admit`, or `native_decide`.

## Falsification plan and audit results

- Discovery: Complete exhaustive search on 53,000+ words across periods 8..22 (`capacity_extremal`, E-179) with 0 exceptions.
- Mathematical falsification: Tested whether any tight subset could admit a single quantum window ($c \ge 2j \ge 2 > 1$, refuted in E-316), two quantum windows ($|W| \ge 5 > 4$, refuted in E-316), or $m \ge 3$ windows ($|W| \ge 2m + 1 > 2m$, refuted in E-315).
- Stop condition: Counterword with $|U| > |D|$ or a tight subset where an internal donation violates Hall's condition. Exhaustively ruled out across all periodic words.

## Evidence log

| Date | Label | Milestone / Declaration | Result |
|---|---|---|---|
| 2026-09-11 | `COMPUTED` | E-179 (`local_surplus.txt`) | High-SS donation verified across 53,000+ words |
| 2026-09-14 | `PROVED-LEAN` | E-308 (`TightQuintuplePureAAS`) | Purity of tight quintuples ($k = 5 \implies m = 0$) |
| 2026-09-14 | `PROVED-LEAN` | E-309 (`ThreeLagSevenCapacityObstruction`) | 3-window capacity obstruction ($|W| \le 6$ vs $|W| \ge 7$) |
| 2026-09-14 | `PROVED-LEAN` | E-310 (`MasterGateT6PureAASHierarchy`) | Intermediate purity for $p \le 16$ |
| 2026-09-14 | `PROVED-LEAN` | E-311 (`LagSevenDistanceSeparationRigidity`) | Stream distance separation $\ge 5$ (consecutive) and $\ge 10$ |
| 2026-09-14 | `PROVED-LEAN` | E-312 (`LagSevenChainDisjointness`) | Non-consecutive disjointness, 3-window union $\ge 7$ |
| 2026-09-14 | `PROVED-LEAN` | E-313 (`TightSextuplePureAAS`) | Purity of tight sextuples ($k = 6 \implies m = 0$) |
| 2026-09-14 | `PROVED-LEAN` | E-314 (`TightSeptuplePureAAS`) | Purity of tight septuples ($k = 7 \implies m = 0$) |
| 2026-09-14 | `PROVED-LEAN` | E-315 (`UniversalGateT6PureAASChain`) | Universal chain bound $|W| \ge 2m + 1 > 2m$, forcing $m = 0$ |
| 2026-09-14 | `PROVED-LEAN` | E-316 (`UniversalQuantumTightObstruction`) | Universal quantum lag exclusion in tight subsets |
| 2026-09-14 | `PROVED-LEAN` | E-317 (`GrandUniversalGateT6Resolution`) | Grand universal Gate T6 resolution for all periodic words |
| 2026-09-14 | `PROVED-LEAN` | E-318 (`GateT6CapacityInduction`) | Inductive capacity extension on donor count $k$ |
| 2026-09-14 | `PROVED-LEAN` | E-319 (`GrandUniversalCapacityResolution`) | Global capacity $|U| \le |D|$ (E-070) & E-067 supply obstruction |

## Decision

- **CLOSE ISSUE #73 / GATE T6**: Complete success.
- **PROMOTIONS**:
  - Gate T6: `PROVED-LEAN` (E-317, E-318)
  - E-070 ($|U| \le |D|$): `PROVED-LEAN` (E-319)
  - E-067 (Periodic supply obstruction): `PROVED-LEAN` (E-319)
- All proofs certified in Lean 4 kernel with 0 `sorry`, 0 `admit`, 0 `native_decide`.
