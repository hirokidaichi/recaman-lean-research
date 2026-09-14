# Hypothesis card: Grand Synthesis of Exact Recamán Orbit Non-Periodicity

- ID: `H-20260914-02`
- Owner: antigravity
- Created: 2026-09-14
- Status: `PROVED-LEAN`
- Research branch: Exact Orbit Non-Periodicity Synthesis (E-065 finite seed supply + E-067 universal capacity obstruction)

## Exact statement

No exact Recamán orbit (from any initial state $s \in \text{State}$ and base clock $b \le N$, or the canonical orbit starting from $a_0 = 0$) can enter an eventually periodic sign pattern under either of the following regimes:
1. Every addition phase in the periodic tail admits a P2 supply window with $ssCount \le 1$.
2. The periodic tail admits a high-SS donor reduction via Gate T6 capacity induction.

Mathematically:
1. **Period Mass to Sign Sum Bridge**:
   For any periodic sign word $e : \mathbb{Z} \to \text{Bool}$ with period $p > 0$:
   $$\text{signSum}(e, 0, p) = \text{mass}(\text{past}(e, 0, p))$$
   Consequently, $\text{mass}(\text{past}(e, 0, p)) \ge 1 \implies \text{signSum}(e, 0, p) > 0$.

2. **Supply Obstruction under Positive Sign Sum**:
   If $\text{signSum}(e, 0, p) > 0$, then $|D| < |A|$. If every addition phase is P2-supplied with $ssCount \le 1$, base capacity gives $|A| \le |D|$, yielding $|A| \le |D| < |A|$, a contradiction (`False`).
   Similarly, under Gate T6 donor reduction with $k$ high-SS donors, $|A| - k \le |D| - k \implies |A| \le |D| < |A|$, yielding a contradiction (`False`).

3. **Seeded Exact Orbit Non-Periodicity**:
   Let $b \le N$ and $s \in \text{State}$. If the sign sequence $\text{absoluteSign}(b, s, n)$ is eventually periodic with period $p > 0$ starting at $N$, then its extension $e$ satisfies $\text{mass}(\text{past}(e, 0, p)) \ge 1$ by `seeded_eventual_supply` (E-065 / E-120), hence $\text{signSum}(e, 0, p) > 0$.
   Therefore, the orbit cannot have all addition phases P2-supplied with low-SS, nor can it satisfy Gate T6 capacity induction.

4. **Canonical Recamán Orbit Non-Periodicity**:
   The canonical Recamán sequence $A(n)$ (starting from $a_0 = 0$, $b = 0$, $s = \text{initial}$) has $\text{canonicalSign}(n) = \text{absoluteSign}(0, \text{initial}, n)$.
   Thus, $A(n)$ cannot enter an eventually periodic sign pattern with low-SS supply or under Gate T6 capacity induction.

Lean formal declarations:
- `Recaman.ExactOrbitNonperiodicity.mass_past_add_eq_signSum`
- `Recaman.ExactOrbitNonperiodicity.signSum_eq_period_mass`
- `Recaman.ExactOrbitNonperiodicity.pos_signSum_of_pos_period_mass`
- `Recaman.ExactOrbitNonperiodicity.low_ss_periodic_obstruction`
- `Recaman.ExactOrbitNonperiodicity.grand_capacity_supply_obstruction`
- `Recaman.ExactOrbitNonperiodicity.seeded_orbit_not_eventual_low_ss_periodic`
- `Recaman.ExactOrbitNonperiodicity.seeded_orbit_not_eventual_periodic_of_capacity_induction`
- `Recaman.ExactOrbitNonperiodicity.canonical_orbit_not_eventual_low_ss_periodic`
- `Recaman.ExactOrbitNonperiodicity.canonical_orbit_not_eventual_periodic_of_capacity_induction`

## Why it matters

- Connects the finite-history exact orbit analysis (`FiniteSeedPeriodicSupply`, E-065 / E-120) with the global word-level capacity obstruction (`GrandUniversalCapacityResolution`, E-067 / E-319).
- Discharges Theme 1 of the post-Issue #73 roadmap: synthesizing word-level periodic obstructions into exact-orbit non-periodicity theorems.
- Provides Lean 4 machine-checked impossibility theorems for eventual periodicity of Recamán orbits without `sorry`, `admit`, or `native_decide`.

## Provenance and dependencies

- Exact orbit positive supply: `Recaman.FiniteSeedPeriodicSupply.seeded_eventual_supply` (E-065 / E-120, `PROVED-LEAN`).
- Canonical seed sign bridge: `Recaman.CanonicalSSFreeSupply.canonical_seed_sign` (`PROVED-LEAN`).
- Backward period mass constancy: `Recaman.ParitySupply.period_mass_constant` (`PROVED-LEAN`).
- Base capacity inequality: `Recaman.GrandUniversalCapacityResolution.low_ss_base_capacity` (E-319, `PROVED-LEAN`).
- Gate T6 inductive donor reduction: `Recaman.GrandUniversalCapacityResolution.inductive_donor_reduction` (E-319, `PROVED-LEAN`).
- Positive sign sum inequality: `Recaman.GrandUniversalCapacityResolution.positive_sum_subtraction_lt_addition` (E-319, `PROVED-LEAN`).
- Grand E-067 obstruction: `Recaman.GrandUniversalCapacityResolution.grand_e067_p2_supply_obstruction` (E-319, `PROVED-LEAN`).
- Axioms: Only standard Lean 4 kernel axioms (`propext`, `Classical.choice`, `Quot.sound`). 0 axioms added.

## Falsification plan and audit results

- Boundary cases: Checked $n = 0$ base cases and single-step induction in `mass_past_add_eq_signSum`.
- Exact orbit consistency: Validated that `absoluteSign 0 initial n = canonicalSign n` aligns definitions between `FiniteSeedPeriodicSupply` and `CanonicalSSFreeSupply`.
- Full Lean check: `./scripts/check.sh` builds all 450 jobs and passes kernel axiom audit with 3010 declarations.

## Decision

- Status: `PROVED-LEAN`
- Milestone: Registered as **E-320**.
