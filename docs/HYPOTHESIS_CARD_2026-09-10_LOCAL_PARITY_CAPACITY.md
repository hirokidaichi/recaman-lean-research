# Hypothesis card: local parity windows and compatibility with all short supply

- ID: `H-20260910-09`
- Owner: Codex, four roles sequentially
- Created: 2026-09-10 JST
- Status: `PROVED-LEAN` (both gates); finite census is `COMPUTED`
- Base HEAD: `8dfbfb8f15eb2ff3d84629385cde99cd9f2bc9aa`

## Exact bounded question

Drop the global fixed-parity premise. Call a P2 witness (t,d) locally
parity-clean when every positive even backward offset i≤d is A. Are all
such witnesses still classified by d=8k+3 and the one-exception pattern,
and does q=t−(d+3)/2 give an injective S charge for their supplied phases
in every periodic stream?

Further gate: let U be ALL lag≤11 supplied A phases with the existing
phi7/phi11 charge, and Q be locally parity-clean supplied A phases with
lag≥19. Must the two images be disjoint, giving |U|+|Q|≤D without any
global parity or long-A-run assumption?

## Informal dependency chain

The local window can be extended outside itself to a globally fixed-A
parity stream. Applying H-08's exact classification gives the same local
odd-offset A/S pattern. Equal charges align the two parity origins, so
the exceptional-A/sign contradiction still proves injection.

For k≥2 (lag≥19), the charge q lies4k positions after the oldest window
position and4k+2 before the newest. Any short source charged to q by the
old map has offset j∈[3,11], so its whole11-sign past lies inside
[q−8,q+10], contained in the long clean window. Hence its P2 witness
is also parity-clean in the appropriate orientation. On clean short words,
the old map must equal the half-lag map (offset3 for lag3, offset7 for
lag11). The local injection then excludes a collision with a long witness.
This last compatibility step must be checked, not assumed from the old map.

## Falsifier / acceptance / stopping condition

- Exhaust all binary periods3..12 discovery,13..18 holdout, without sign-sum
  restriction. Compute every short witness and every local-clean witness.
- Local-clean witnesses have d<2p: otherwise a repeated period either repeats
  the unique variable-parity A (p even), or places an S in both parities
  (p odd). All-A words cannot be P2. This cutoff argument must be audited.
- Check all clean charges for S/injectivity, and all long-clean charges
  against the exact phi7/phi11 image, including U∩Q and wrapping windows.
- Structured long clean windows with SS/arbitrary short-pattern buffers:
  k2..8 discovery,9..64 holdout; one/three blocks, both cycle origins.
- Acceptance: all-period Lean local classification/capacity, then compatible
  short-map extension. If compatibility fails, retain only the proved local
  theorem and stop that extension; no new lag table repair.
- A standard finite-orbit coverage check is a separate diagnostic, not proof.

## Evidence and audit

- `PROVED-LEAN`: `LocalParitySupply.local_P2_iff` proves both directions of
  the exact pattern; `clean_is_minimum` and `clean_lag_unique` ensure the
  witness is the minimum among all P2 lags and the only clean one.
- `PROVED-LEAN`: `LocalParityPeriodic.periodic_clean_capacity` counts every
  selected locally clean supply phase, for arbitrary period and either
  parity origin. It constructs the S injection without assuming one.
- `PROVED-LEAN`: `ShortLocalParityCapacity.short_plus_clean_capacity` adds
  ALL lag≤11 supplied A phases to arbitrary long-clean Q (lag≥19).
  `global_short_offset` checks compatibility with the existing phi7/phi11;
  `line_images_ne` proves the full-window containment argument.
- `COMPUTED`: `python3 experiments/issue73_20260910/local_parity_capacity.py`
  passed every binary period3..18 and the declared structured k2..64 cases.
  Exact output: `docs/data/issue73_20260910/local_parity_capacity.txt`.
- `COMPUTED`: H-07b's frozen standard-prefix census counts 921,983 phases
  in U≤11 ∪ clean, out of 1,315,896 finite-history P2 A phases through10^7
  steps (70.0650355%). The first range is discovery and the two later ranges
  are holdout for this newly declared statistic; these are one deterministic
  trajectory, not independent samples. All actual hybrid charges were S and
  distinct. Finite-prefix P2 absence does not imply absence of an actual
  Recamán blocker.
- `./scripts/check.sh`: PASS, 1,384 audited declarations, allowed axioms only.
  Log: `docs/data/issue73_20260910/check09_local_parity_capacity.txt`.

## Failed attempts / limits / decision

No mathematical counterexample to either declared gate was found. Intermediate
Lean elaboration required explicit cast normalization and addition associativity;
no weakened statement was substituted. The finite-search d<2p cutoff currently
has the stated paper argument; the all-lag Lean theorem itself has no cutoff.
The fixed half-lag rule still fails on unrestricted P2 windows (the existing
SSSAAAA negative control). This theorem therefore does not prove E-070.
The remaining 393,913 finite-history supplied A phases in the measured prefix
are outside the combined class. Next decision: characterize the parity defects
of those windows before trying to extend the injection; no lag-by-lag table.

