# Hypothesis card: sharp threshold for bounded-excess supply multiplicity

- ID: `H-20260910-02`
- Owner: Codex; four research roles sequentially
- Created: 2026-09-10 JST
- Status: `PROVED-LEAN` (E-097)
- Base HEAD: `8dfbfb8f15eb2ff3d84629385cde99cd9f2bc9aa`; E-096 is a checked working-tree dependency.

## Exact bounded question

For integers R≥0, m≥3, k≥1 and a sign stream e with A steps at t,...,t+k−1,
suppose P2 supplies exist with

```text
4m−1 ≤ d ≤ 4m−1+4R,
4(m+k)−1 ≤ d₂ ≤ 4(m+k)−1+4R.
```

Must m≤R(R+1)? Equivalently, after run index m≥R(R+1)+1, at most one
supplied time in an A run can have a lag within4R of the sharp bound.
The statements quantify over any P2 lags, not just minima. The run index
can be the exact preceding A-run length; the arithmetic implication does
not itself need a first-S assumption. No global capacity is assumed.

Claim of optimality: for every R≥2, at m=R(R+1), take old word sharpFamily(m)
and new word `A old S^(2R+1) A S A^(2R)`. The old and new minimum lags are
4m−1 and4m+4R+3 across k=1, so both belong to the band. Thus the threshold
cannot be reduced to m≥R(R+1) for all R.

## Dependency chain and weakest new lemma

E-096 gives Δ(Δ−4k)≥4k(d−1). Set x=Δ−4k. The two band assumptions imply
−4R≤x≤4R. Thus

```text
4k(4m−2) ≤ 4kx+x² ≤ 16kR+16R² ≤ 16k(R²+R).
```

Since k≥1 and m is integral, m≤R(R+1). This is an all-R multiplicity
consequence, not a new lag table. For the boundary family, the appended
tail has mass−1 and moment4R(R+1)−2, giving P2. Minimality follows from
the leading-run lower bound and E-096, or from the complete prefix argument
to be recorded before claiming it.

## Frozen falsifier / acceptance / stop

- Arbitrary sign windows; no freshness, actual orbit, or positive period sum.
- Enumerate all P2 words of maximum lag D=11,15,19 (discovery) and23,27 (holdout).
- For k=1..4 inspect both orientations: a new P2 prefix after prepending A^k,
  and old P2 prefixes after deleting k leading A signs from a new full P2 word.
- For every pair with leading run m≥3, derive the smallest band R containing
  both lags and test m≤R(R+1). Repeated contacts across scans are not distinct phases.
- Boundary family: R=2..8 discovery, R=9..64 holdout; inspect all prefixes.
- R=0,1 are included in the inequality tests; no optimality family at m<3 is claimed.
- No repair. Stop on a pair above the proposed threshold or a failed family member.
- Acceptance: all-R paper/Lean implication and exact boundary witnesses,
  or a counterexample. Merely passing finite windows is insufficient.

## Evidence and decision

`PROVED-LEAN`: `Recaman/BoundedExcessSupply.lean` proves the all-R implication
and the all-R≥2 optimality family, including both minimum lags. The arithmetic
lemma is stronger than the application: m,d,d₂ may be arbitrary integers;
only R≥0, k≥1, the two bands and the signed gap are required.

The boundary minimality argument is now complete: a shorter new P2 prefix
must have lag d≥4m+3 by its m+1 leading As and hence contains the old sharp
window. Write z=d−4m. A prefix shorter than the displayed witness has
3≤z≤4R+2. The nested gap requires (z+1)(z−3)≥16m−8, whereas
(z+1)(z−3)≤(4R+3)(4R−1)=16m−8R−3<16m−8 for R≥2.
The old word is minimal by E-090. The family has gap slack8, not equality.

`COMPUTED`: command
`python3 -u experiments/issue73_20260910/bounded_excess_multiplicity.py`
with exact output in `docs/data/issue73_20260910/bounded_excess_multiplicity.txt`.
All P2 word counts at D=11,15,19,23,27 were29,263,2724,30554,361677.
Eligible overlap contacts were0,0,0,41,956; zero violations. Thus the small
discovery lengths contain no eligible contacts and are not positive evidence
for the pair bound. Both orientations appear in holdout. Boundary family
R=2..64 passes full prefix checks; R=64 has m4160, minimum lags16639→16899.
The family checks support but do not replace the all-parameter Lean proof.

Audit: `./scripts/check.sh` passed with1,279 declarations; exact log
`docs/data/issue73_20260910/check02_bounded_excess.txt`.
Seven new declarations included in `Recaman/Audit.lean`; no extra axioms.
An initial import-contract row used filesystem paths instead of module names;
the audit rejected it and it was corrected before the successful run.

Decision: accept this structural lemma. Do not reinstate lag monotonicity
or claim E-070. Next bounded question is whether nonsharp windows retain
enough S positions to extend a pre-existing short supply charge.
