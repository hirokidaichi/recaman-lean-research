# Next-epoch triage (2026-09-11)

Eighteen candidate research units were generated from six independent panels and screened
by three adversarial lenses each — collision with the no-go list, active counterexample
search, and honesty of payoff. Fifteen were killed. This document records the kills,
because a killed unit that is not recorded gets re-proposed next round.

It is not the status source of truth; [`CURRENT_FRONTIER.md`](CURRENT_FRONTIER.md) is.

## Verdict

**The declared gate T6 / E-179 outranks everything that survived.** Five separate kill
verdicts, written independently and without coordination, named T6 as "the unit that is
actually open". The three survivors are compositions of theorems already in the kernel:
all three would very likely compile, and none would change what is provable about E-067,
E-070, T4 or surjectivity. They are a cheap honest floor for a round, not its target.

If a round has capacity for one unit, it should be T6 at `ssCount = 2`, not a composition.

## Killed, with the collision that killed each

| Unit | Killed by |
|---|---|
| Per-A-run offset capacity `\|U_K\| ≤ (max 2 (K+1) + 1)·\|D\|` | No implication chain: a constant `>1` never yields `U ≠ A` from a positive sign sum, and two of its three payoff claims misread the repo |
| Minimality restores injectivity at `ssCount ≤ 2`? | Restatement of a stopped selector branch; E-178's gate ("selector探索は終了") is exactly this |
| Free-word S-density inequality (D-free) | Core is a tautology; the non-vacuous part duplicates E-176/E-177/E-178 |
| Localize the two proved capacity theorems to density form | Both propositions are direct instantiations of already-`PROVED-LEAN` artifacts |
| Residual joint-Hall for isolated-singleton SS=2 | E-108 with the defect statistic renamed; E-108's restart condition is unmet |
| E-067 for cyclically SS-free periods | Tier 1 is `LowSSPeriodicSupply.positive_period_requires_two_SS` (E-128) in a strictly stronger form |
| N\*: E-070 restated on free words + adversarial search | The free-word statement is *equivalent* to E-070, not a larger object; the claimed generality is false |
| Lean bridge: `net ≤ 0` → periodic capacity | Same equivalence; restates E-175's exhaustion and E-070 itself |
| Tight-seam pumping | Exact duplicate of E-182, same branch slug, at a smaller horizon |
| Level/wrap dictionary (arcs as a functional of the sign word) | Claim (i) is E-038 `PROVED-LEAN` twice over; the rest are one-line corollaries |
| Eventual periodicity forces linear arc density | Redundant with E-038; consumes rather than supplies the input the stopped arc branch is gated on |
| Arc reach of supply SS-priced (joint census) | Killed with E-119 + E-038; gated out by the E-066/E-081/E-129 finite-evidence rule |
| FW: free-word supply inequality | Same equivalence as N\* |
| Tail-region supply automaton provable by `decide` | Implication chain broken at step zero; E-122 gives word-level content a decisive counterexample |
| Tail-excursion census: is `(mass, moment)` dominated by `ssCount`? | Acceptance criterion is the horizon-extension shape this branch has already been burned by |

Two of these were killed as duplicates of **E-182**, which this epoch produced hours
earlier — the screening read the committed registry, so the triage is against the current
frontier and not a stale one.

## Survivors, with their scope limits

Ranked by (decisiveness × probability of a clean result) / cost. Each carries a scope line
that must travel with it into any registry row; a row landing without its scope line is
worse than no row, because later rounds read the registry as ground truth.

1. **Wrap-vs-SS accounting.** For a periodic word with period mass `S ≥ 1` and any P2 lag
   `d = qp + r`: `q·S ≤ ssCount (past e t r) + 2`. Sharpens E-181's scan cutoff from
   `p(p+1)` to `p(ssCount+2)/S + p`, and equality is attained (542 cases at `p ≤ 12`).
   **Scope:** unconditionally the bound stays `Θ(p²)` — max minimal-lag / p is
   0.75, 2.14, 4.27, 4.23, 6.33 at `p = 4, 7, 11, 13, 15`, so there is no universal `C`
   with min lag `< C·p`. It is linear in `p` only for words with bounded sub-period SS
   content, where E-113 already gives `d < 2p`. No p-independent lag cap, no capacity
   consequence. It is tooling for E-181, not a new frontier row, unless its `K = 1`
   instantiation lands.
2. **S-side dual of E-067.** A null window anchored at an S is exactly "this S phase has a
   P2 supplier", so NoNullWindow is `supplied ⊆ A`, the dual of E-067's `A ⊆ supplied`.
   Transporting `NoDoubleAdditionRun` and `LoopClosingSubtraction` discharges the NoSAAS
   premise that `SSFreePeriodicSupply` still carries.
   **Scope:** this is hypothesis strengthening, not target reduction. Its central measured
   finding is negative: NoNullWindow prunes **0** of the tight words at every period 8..18,
   and by E-177 the tight set is where everything still open in E-070 lives.
3. **Endpoint fiber at `ssCount ≥ 2` on both sides — gated.** Step 0 is an exhaustive
   search for two S-ended witnesses on a common endpoint residue *both* carrying
   `ssCount ≥ 2`. Every fiber-2 example on record pairs a high-SS window with a clean
   sibling E-128 already owns. If no such collision exists in range, write no Lean.
   **Scope:** its central measured finding is also negative — the constant never binds;
   `max |U|/|D|` is exactly 1.0000 for all `p ≤ 18` even with `ssCount` unrestricted.

## The recorded failure mode

Quoted from the ranking pass, because it is the part most likely to be ignored:

> The honest downside is that this epoch can succeed completely and move the frontier zero
> distance. […] If this epoch consumes the full round, T6 goes another epoch unattempted,
> and the honest ledger entry is: we spent a round on three certain lemmas because the one
> uncertain thing that matters was harder to start.

Registry inflation is the dominant risk, not falsity. None of the three may be mined later
as "capacity proved for all ssCount", "E-067 target class reduced", or "linear-in-p lag
bound". None of those is true.
