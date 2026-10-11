# Hypothesis card: separate SS runs in a NoSAAS oldest-S collision

- ID: `H-20261011-01`
- Source: `codex/research-plan-20261003`, research result E-370 as reported in `docs/RESEARCH_PLAN_2026-10-06_SS2_REMAINING.md` (commit `167d07df424b85217010935934bd583d8995af23`)
- Created: 2026-10-11
- Roles: proposer/falsifier and independent direct-clock replay in separate scripts; no Lean formalizer or independent human auditor
- Status: `REFUTED` (the assertion that the separated class is empty); existence family `PROVED-PAPER` subject to independent audit; finite witness `COMPUTED`
- Branch: NoSAAS minimal P2 SS2 donor collision

## Exact bounded question and stopping rule

Is it impossible for any positive-mass, `p`-periodic binary stream `e : ℤ → {A,S}` with no cyclic chronological `SAAS` to have two distinct current-A phases whose **first positive P2 lag** windows have exactly two SS edges in different runs and the same true-oldest S phase? P2 means newest-first sign mass 1 and moment `Σ j sign(j) = 0`. The two SS edges are separate when their starting indices differ by at least 2.

Acceptance: one explicit period word with exact current, first P2 lags, SS locations, oldest-S phase, positive mass, and cyclic NoSAAS checked independently. Stop as soon as such a word is found; do not infer failure of the endpoint inequality or Hall from existence. If no example appeared for `d_A∈{11,15,19,23}`, stop bounded enumeration and retain the existential question as `CONJECTURED`; no upper-bound escalation.

## Witness

Let `C=AAASSASSASASAS` (newest-first, length 14), `X=(AS)^14 A` (length 29), and for each integer `n≥2` define the ascending period word `P_n=reverse(X C) A^n`, repeated on ℤ. Its declared period is `p=43+n` and period sign mass is `n+1>0`. The `n=2` word is

`SASASASSASSAAAASASASASASASASASASASASASASASAAA` (`p=45`).

Its current-A donor at clock 14 has window `W_A=C A`, first P2 lag 15; its current-A donor at clock 43 has window `W_S=X C`, first P2 lag 43. Both have SS count 2. The two SS edges of `C` start at newest-first indices 3 and 6 (zero-based), giving separate chronological runs. Both donors' true-oldest S is clock 0 modulo `p` (the A-ended window's oldest slot at clock −1 is A). The donors are phase-distinct for `p≥45`.

`mass(C)=0`, `moment(C)=−15`, `mass(X)=1`, `moment(X)=15`, so both full windows are P2. Direct prefix scan finds exactly one P2 prefix in each window, at lengths 15 and 43 respectively. These prefix facts do not depend on `n` because both windows are identical for every `n≥2`. The prefix of `P_n` is `reverse(X C)` and its final A-run is `n+1≥3`; the other A-runs between S are singleton or length 4 at the `reverse(C)`/`reverse(X)` seam. Thus no cyclic `SAAS` occurs, including the closing seam. This gives a paper family for every period parameter `p≥45`; it does not assert that each is the least period.

Exact mass-one prefix moment check (all other prefixes have mass different from 1): for `C A`, prefix lengths `1,5,7,9,11,13,15` have moments `1,−3,−4,−3,−2,−1,0`. For `X C`, all mass-one prefixes inside `X` have lengths `2k+1`, `k=0,…,14`, and moment `k+1`; the remaining mass-one prefixes have lengths `37,39,41,43` and moments `3,2,1,0`. Hence no shorter P2 window exists. This finite calculation plus the explicit cyclic run check is the all-`n` argument; the script is a second check.

## Computation and source

Run from the repository root after copying the two accompanying scripts into `experiments/`:

```sh
python3 experiments/separated_ss_probe.py 11 15 19 23
python3 experiments/separated_ss_verify.py > docs/data/ss2_separated_20261011/direct_replay.jsonl
```

The first script enumerates `C` at each selected donor lag subject to mass/moment, exactly two nonadjacent SS edges, first P2 prefix, the two existing paper-classified `X` shapes, and cyclic NoSAAS after padding. It stops when it finds the first witness for each lag; **the displayed counters before each witness are partial search counters and are not an exhaustive census**. At `d=11`, all 252 mass-balanced cores are tried and then filtered by the moment condition and no minimal separated collision appears in this particular `X` construction. At `d=15`, it finds the witness above. The second script independently scans the periodic clock, recalculates donor P2 prefixes and SS count, cyclic NoSAAS, and every current-A, S-ended, SS≤1 P2 endpoint through `p(p+1)` for `n=2,3,7`.

For `n=2`: donor prefix hits are `[15]` and `[43]`, their oldest phases are both 0, period mass is 3, cyclic NoSAAS is true. All lowSS endpoints from the direct finite bound are `[9,10,23,29,35,41]`; the donor union has 21 S phases and 15 are outside this endpoint set. The `p(p+1)` scan applies to positive-mass period words as established in the prior repository protocol. These finite counts are `COMPUTED`, not a proof of all-period endpoint exclusion or Hall.

## Semantic audit and decision

This example is an abstract periodic sign stream, **not** a known Recamán orbit. `NoSAAS` is checked around the cyclic seam. A current phase is checked to be A; both lags are the first P2 lags, and the common S is the true oldest rather than a selected internal phase. The two SS edges are in separate runs, so E-370's SSS theorem cannot be cited for it. Existence does not refute the strong endpoint inequality: in the concrete `p=45` witness it has ample excluded phases. It does refute deleting the separated branch as empty.

Next bounded question: identify a second S phase that **every** eligible lowSS endpoint misses for all separate-run collision pairs, or produce an exact counterexample to that stronger assertion. Start with chronological first SS-run start and require all-lag endpoint checks. A failure of the stronger assertion does not itself refute Hall. Preserve E-370's hypothesis and do not relabel E-001, E-067, or E-070.
