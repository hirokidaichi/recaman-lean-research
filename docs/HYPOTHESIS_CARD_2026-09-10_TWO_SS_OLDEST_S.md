# Hypothesis card: oldest-S charge for two-SS minimum windows

- ID: `H-20260910-30`
- Owner: Grok, sequential proposer / falsifier / formalizer / auditor
- Created: 2026-09-10, 3-hour continuation after E-128/E-130/E-131
- Status: original oldest-S joint charge `REFUTED` (E-133); replacement leading-run sibling `PROVED-LEAN` (E-132); orbit split `COMPUTED` (E-134)
- Research branch: periodic P2 supply capacity (issue #73), SS≥2 allocation
- Base HEAD: current `main` plus the audited 2026-09-10 working tree

## Exact statement

Newest-first words, `A=+1`, `S=-1`. `P2(w)` means `mass(w)=1` and
`moment(w)=0`. `ssCount` counts adjacent SS edges, including overlaps.
A window `past e t d` is the signs at `t-1,...,t-d`. The current sign is
`e(t)`, outside the word. The oldest sign time is `t-d`.

For a two-sided stream `e` and a current-A time `t` whose **minimum** P2
lag `d` satisfies `ssCount(past e t d)=2`, write `σ(t)` for the oldest S
time in that window: the largest `q` in `[t-d, t)` with `e(q)=S`. Equivalently,
the last S letter in the newest-first word.

Proposed stream theorem, no periodicity required:

1. `σ(t)` exists and `e(σ(t))=S`.
2. If `t<u` are two such sources, then `σ(t)≠σ(u)`.
3. `σ(t)` is never the E-128 S-ended prefix endpoint of a current-A source
   whose some P2 window has `ssCount≤1`.

Periodic corollary: in every period `p`, the number of A phases whose
minimum P2 witness has at most two SS is at most the number of S phases.

No lag bound, NoSAAS, positive period mass, or canonical reachability is
assumed for (1)–(2). Claim (3) is the joint budget with E-128.

The canonical control `AAASSSASASA` at sign time 114 must be included:
minimum lag 11, SS 2, endpoint A at 103, oldest S at 104.

## Why it would matter

E-128 injects every SS≤1 P2 source into an S endpoint. E-130 refutes
extending the *same* S-ended prefix normalization to SS=2; the boundary
window ends A. E-131 gives a multiplicity budget inside one endpoint
group, not an allocation across groups. An injective oldest-S map for
minimum SS=2 windows would add the 7 short canonical exceptions and the
52,350 SS=2 finite-P2 sources through 10^7, without a new offset table.
It is not E-070: SS≥3 remains.

This is stronger than a local gap identity. It is not an equivalent
reformulation of coverage.

## Provenance and dependencies

- Definitions: `mass`, `moment`, `P2`, `ssCount`, `past` from
  `LeadingRunSupply` / `OneSSMultiplicity` / `LowSSEndpoint`.
- Lean theorems: `lowSS_S_prefix`, `endpoint_injective`,
  `periodic_lowSS_capacity`, `repeated_endpoint_budget`,
  `CanonicalLowSSBoundary.no_S_ended_prefix`.
- Unverified: that minimum SS=2 forbids sharing the oldest S, and that
  this S is disjoint from the low-SS endpoint image.
- Not reused: centered charges (E-112), constant SS budgets (E-122),
  lag tables (E-088), prefix normalization at SS=2 (E-130).

Weakest new lemma: two minimum SS=2 P2 windows cannot share their oldest
S. Joint disjointness with E-128 is a second, independent lemma.

## Falsification plan

- Small words: all binary P2 words of length 3..23 with SS=2; classify
  minimum vs not, end A vs S, overlapping SSS vs two separate SS, NoSAAS,
  trailing A-run, oldest-S offset. Discovery lengths 3..15, holdout 16..23.
- Weakened history: all binary periods 1..16 discovery, 17..20 holdout,
  all mass signs, SAAS allowed. For every A phase with a finite P2, take
  the minimum lag up to 4p and test oldest-S injectivity and disjointness
  from the low-SS S-ended prefix map.
- Canonical control: sign time 114 must receive a defined S charge.
- Frozen orbit: standard 10^7 replay, exact prefix-key minimum P2, all
  SS=2 minimum sources.
- One repair: if oldest-S collides, one justified restriction (minimum
  vs arbitrary witness, or overlapping-SSS vs two separate SS) is
  allowed. A second collision stops the charge.
- Stop: if four named charges (oldest S, newest S, first S of the first
  SS pair, last S after stripping trailing A's — the last coincides with
  oldest S) all fail, and no replacement common-history moment/SS
  identity survives the step-115 word, stop. Do not add offsets or lag
  types.

## Evidence log

| Date | Label | Revision / command | Result |
|---|---|---|---|
| 2026-09-10 | `CONJECTURED` | this card | statement frozen before enumeration |
| 2026-09-10 | `REFUTED` | `python3 experiments/issue73_20260910/two_ss/classify_and_charge.py` | oldest-S collides at period 16 (`AAASSSASASA` with `SASASAASAAAASSSASAS`); first-SS from period 13; newest-S has 0 self-collisions through period 18 |
| 2026-09-10 | `REFUTED` | `python3 experiments/issue73_20260910/two_ss/newest_s_audit.py` | newest-S hits E-128 at the canonical control itself: sign 114 SS=2 and sign 113 lag-3 share S at 110 |
| 2026-09-10 | `PROVED-LEAN` | `Recaman/TwoSSLeadingSibling.lean` | min P2 of lag>3 cannot start AAS; leading A-run a≥3 forces clean sibling at t-(a-2); canonical 114/113 is an instance |
| 2026-09-10 | `COMPUTED` | `experiments/issue73_20260910/two_ss/orbit_ss2_leading.cpp` through 10^7 | SS=2: 52,357; one-per-run 0; companion 148 with sibling 148/148; isolated a=0: 52,198; a=1: 11; a=2: 0 |

## Semantic audit

- Informal statement implies formal statement: the charge is a sign time
  in the actual window, not a residue class or a chosen lag table.
- Formal statement implies intended consequence: injectivity into S
  phases gives `|U≤2|≤|D|` after periodic lifting, jointly with E-128
  only if (3) holds. Do not add this to the old U≤11 count.
- Counterfactual that should make it false: two minimum SS=2 windows
  whose oldest S letters occupy the same integer time.
- Vacuity: a theorem that assumes the windows already end S has failed,
  because the boundary example ends A.
- Provenance: minimum-lag, not an arbitrary P2 witness. E-131's sharp
  family is non-minimum and must not be reported as a counterexample.

## Decision

- Original H-30 oldest-S joint charge: `REFUTED`. The four named charges
  are stopped. Do not repair offsets.
- Replacement inequality E-132 is `PROVED-LEAN` and treats step 115 as an
  instance: the SS=2 window is a companion of a clean lag-3 source in the
  same A-run. This is a common-history identity, not a capacity injection.
- Orbit census partitions SS=2 into companions (already sharing a run with
  low-SS) and isolated a=0 windows (99.7%). One-per-run is `COMPUTED`, not
  a theorem.
- Continue only with an explicit allocation for isolated a=0, or a proof of
  one-per-run. E-067/E-070 remain open.
