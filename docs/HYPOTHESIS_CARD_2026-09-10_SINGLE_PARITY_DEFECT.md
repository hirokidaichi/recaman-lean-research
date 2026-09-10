# Hypothesis card: a single parity defect after freezing the clean injection

- ID: `H-20260910-10`
- Created: 2026-09-10 JST, after H-09's 1,384-declaration audit
- Owner: Codex, proposer/falsifier/formalizer/auditor sequentially
- Status: finite gate `COMPUTED`; general matching `CONJECTURED`; fixed-defect expansion `STOPPED`
- Base HEAD: `8dfbfb8f15eb2ff3d84629385cde99cd9f2bc9aa`

## Exact bounded question

For a P2 window w of length d, let b be the number of S at positive even
backward offsets. Clean means b=0. First quantify b on the still-uncovered
minimum finite-history P2 windows of the standard prefix.

The new combinatorial candidate fixes the complete H-09 short/clean
injection. For every supplied A phase whose minimum P2 window has b=1 and
d≥15, keep as its domain ALL S phases in that minimum window that the old
injection has not used. Do these residual domains always have a matching?
This is a restricted extension of an infinite-lag class, not a new lag table.
The matching is the conclusion, never a premise.

## Dependency chain and weakest useful lemma

Mass balance forces b+1 A at odd offsets. If d=4r+3, their odd positions
2x_i+1 and the even-S positions 2y_i satisfy
`r = 2*(sum x_i - sum y_i) + b`.
For b=1 there are exactly two odd A and one even S, and d≡7 mod8.
The useful new lemma would be Hall for the residual domains after freezing
the known infinite clean injection. A count identity alone is diagnostic,
not a claimed advance to full capacity.

## Predeclared falsifier and acceptance

- Exhaust binary periodic words p3..12 discovery, p13..18 holdout, all sign
  sums. Scan up to4p (and through11 for the old short class), stopping once
  the even-S count exceeds1. This covers every b≤1 minimum witness: for
  even p, any even-offset S repeats within p; for odd p it repeats within2p.
  An absent even-offset S gives b=0 throughout, already handled by H-09.
- Independently check failed matchings by enumerating Hall subsets for small
  Q. Print the full chronological word, minimum lags, old image and domains.
- Structured b1 windows with d15..79 discovery and d87..519 holdout, with
  arbitrary surrounding SS/short-pattern buffers; stop immediately on a
  reproducible counterexample. Do not repair a failed frozen-map gate by
  changing offsets or adding a type table in this card.
- Standard orbit diagnostic reuses H-07's exact prefix-key P2 method through
  10^7 steps; ranges1..10^5 discovery,10^5+1..10^6 and10^6+1..10^7 holdout for
  the newly declared defect statistic. These ranges are one trajectory.
- Acceptance: complete general argument and Lean certificate, OR a fully
  audited explicit failure of this residual matching. If finite tests pass
  but no invariant emerges within this bounded cycle, label the candidate
  `CONJECTURED`, stop expansion of the census, and record the missing step.

## Repository search / distinctions

E-069 oldest-S, E-083 kappa descent, E-085 following-gap, and E-088 uniform
offset selectors remain stopped. This card does not revive their maps. It
tests full residual domains with the newly proved infinite clean map fixed.
A failure refutes that extension strategy, not E-070 or unrestricted Hall.

## Evidence / decision

`COMPUTED`: the declared exhaustive p3..18 and512 structured cases pass.
Command: `PYTHONDONTWRITEBYTECODE=1 python3 experiments/issue73_20260910/single_defect_matching.py`.
Exact output: `docs/data/issue73_20260910/single_defect_matching.txt`, with
source and imported charge-table hashes. No Hall counterexample was found;
this finite result is not a matching theorem.

`COMPUTED`: `orbit_defect_census.cpp` (compile command, revision, source hash,
compiler version and exact output in `docs/data/issue73_20260910/orbit_defect_census.txt`)
counts42,572 one-defect supplied A phases, of which42,453 are new beyond
U≤11 ∪ clean. This is10.777% of the393,913 residual phases and3.226% of all
finite-history P2 supplied A phases. Most residual windows have many such
parity defects:259,481 have over1,000 even-offset S. These are counts on the
same standard trajectory, not probabilistic estimates for the infinite orbit.

`PROVED-PAPER` diagnostic identity: start with the alternating lengthd=4r+3
word whose odd offsets are S and even offsets are A. Its mass is−1 and its
moment is−(d+1)/2. Flipping b even positions2y from A to S and a odd
positions2x+1 from S to A changes mass by2(a−b), so P2 forces a=b+1.
Moment zero then gives r=2(sum x−sum y)+b, including the parity test used in
the exact census. This identity alone does not settle Hall and was not
formalized as a frontier advance.

The one-defect shape has two exceptional odd As and one even S. Across
translated supply windows, the exceptional positions and the available
residual S domains change together. No proved interval ordering or Hall
inequality has emerged from this shape; the density identity does not imply
one. Therefore the general matching claim remains `CONJECTURED` and the
fixed-small-defect expansion is `STOPPED` for this session. No offset-table
repair or larger-period-only scan is authorized by this card.

Next bounded question: count adjacent SS rather than parity-position defects.
A long alternating stretch after a parity change contributes many even-S
positions but may have only one SS transition. The already proved exclusion
of internal SAAS in the canonical orbit may connect SS-free P2 windows to
the clean class. Reopen fixed-b Hall only with a new inter-window invariant,
not because the finite matching tests passed.

