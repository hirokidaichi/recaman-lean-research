# Hypothesis card: lag-11 SS=2 donor without minimality

- ID: `H-20260920-02`
- Owner: daytime research, same-session proposer / falsifier / formalizer / auditor
- Created: 2026-09-20 15:02 JST
- Status: `CONJECTURED`
- Research branch: working-tree continuation of H-20260920-01; no registry promotion

## Exact statement

For every `e : Int → Bool`, period `p > 0` with `e (x+p)=e x`, nodup list
`B : List Nat` of phases `< p` with `e b = A`, and lag function assigning each
member a minimal P2 window of length 3, 7 or 11, suppose `|N(B)|=|B|`.
For every integer donor clock `u0`, if `past e u0 11` has mass 1, moment 0,
and overlapping SS count 2, its oldest S phase is not in `N(B)`.
Donor minimality, donor current sign, donor exclusion from B, positive period
mass, ambient Hall and an upper bound on p are NOT premises of this question.
The short-member minimality restriction remains explicit.

Smallest new lemma: for any `OwnerFamily e mem own lag`, if member t has
window w1=SAAAASS, then `mem (t+2)`, `lag (t+2)=3`, its window is AAS,
and `own (t+2)=t-1`. This strengthens H-01's next A to an actual future member.

## Why it would matter

It removes a donor-side assumption from short tight-set avoidance. This is
still restricted to length-11 donors and member lags at most 11. It does not
settle all-lag Hall, general Gate T6 or the Recamán orbit question.

## Provenance and dependencies

- E-357 excludes lag-11 and w2 members of OwnerFamily; E-359 supplies the
  periodic tight-set lift.
- H-01 candidate proves w1 owns t-7 and forces next sign A, and derives Hall
  from the existing short injection with its local image bound.
- Discovery already used: H-01 negative controls p=1..12 found no violation
  after dropping donor minimality. It is NOT fresh holdout evidence here.
- No unproved mathematical hypothesis beyond the displayed object premises.
- Portfolio and E-350, E-351, E-353, E-356..359 checked: pure-AAS classification
  was refuted; non-AAS tight triples are retained, not ruled out. E-351 needs
  next A and ambient inclusion; the proposed line theorem needs neither.

## Falsification plan

- Enumerate all 2^11 words independently by mass/moment/SS count. Check all
  compatible AAS/w1/w2 cover placements at the actual oldest S.
- Check all permitted coverers against the forced future AAS member; keep
  w2 in the raw overlap table and remove it only using E-357.
- Translation/boundary: donor clocks -101,-1,0,1,101; periods 1..12 include
  wrapping and repeated phases. Test zero and negative period mass.
- Weakened-history controls: remove onto or single-valued ownership; confirm
  the forced future-member conclusion can then fail.
- Frozen holdout: all binary cycles of periods 13 and 14, all mass signs,
  all nonempty tight subsets of their least P2 supplies of length <=11;
  donors are ALL lag-11 P2 SS=2 windows, including nonminimal donors.
  Use short windows only; do not use a full-supply bound at nonpositive mass.
  Do not use old p32/33 samples as fresh holdout.
- Acceptance: exact local table has no surviving AAS/w1 ownership completion,
  nonminimal donor instances and nonempty B are actually exercised; Lean
  statement matches the displayed quantifiers; full repository audit passes.
- Stop: one genuine counterexample refutes the broad claim. At most one
  implementation correction is allowed if independently diagnosed; do not
  repair the mathematical claim by reintroducing donor minimality silently.
- Wall-clock boundary: stop new exploration early enough to hand off at16:30.

## Informal dependency chain (before implementation)

Tightness + short injection => periodic OwnerFamily. E-357 => members AAS/w1.
w1 must own its paired oldest S t-7. Its newest S t-1 has an owner; AAS gives
t+2, while w1 at t cannot own two S and other w1 placements conflict in bits.
Thus the owner is the AAS member t+2. Of the 12 length-11 P2 SS=2 words,
7 are old minimal donors and 5 are nonminimal. New compatible w1 covers in
two nonminimal words force e(t+2)=A where the donor has S. Verify this finite
classification before Lean implementation; it is currently a conjecture.

## Evidence log

`COMPUTED`: source and card frozen in `daytime/PRE_DONOR_MINIMALITY_SHA256SUMS`.
Commands: `python3 -u experiments/issue73_20260920/donor_without_minimality.py --mode local`
and `--mode holdout`. Original outputs saved as `daytime/donor_without_minimality_*.jsonl`.
HEAD is `08c08565c743f39350c9b959e1df7d30aa1cae5d`; script hash disambiguates uncommitted code.
All 12 words enumerated, 5 nonminimal. No AAS cover, 5 w1 placements, 2 w2 placements;
w2 is excluded only by E-357. All w1 placements conflict with the future AAS member.
p13: 8192 cycles, 221 nonminimal-donor/nonempty-tight-B checks, 143 nonpositive checks.
p14: 16384 cycles, 532 nonminimal checks, 658 nonpositive checks. No violations.
Actual nonminimal example: p13 `AASSSAAAASSSS`, donor10 with window `SAAAASSSAAS`,
donor sign S, B={7}, N(B)={4}; this exercises the lack of donor-current-A too.

Implementation correction (one allowed): first Lean finite table reused the old
two-bit `aasClash`; Lean's `decide` rejected it. For the two newly compatible w1
words, the two AAS past bits can both be A, while the putative AAS member itself
would have sign S. The Python table already included current-member A. Fix the
Lean table to check all three required A signs. Main theorem quantifiers unchanged.
Failed source and exact failure log are archived as `ShortTightDonorAvoidance_nonminimal_v1.lean`
and `build_nonminimal_local.log`. This is not a counterexample to the card statement.
The creation timestamp above was entered as 15:02 before a fresh clock check;
actual calls confirm this unit was underway by 14:59 and the failure was at15:01.

## Semantic audit

- Abstract periodic signs, not real-orbit provenance.
- Not vacuous: H-01 supplies explicit nonempty tight sets; this cycle must
  separately exhibit nonminimal donors with nonempty tight B.
- Quantifier audit must distinguish donor minimality (removed) from member
  minimality (retained) and true oldest offset from the fixed offset 11.
- No positivity or full-U premise may slip into the implementation.

## Decision

The exact statement is implemented as `short_tight_avoids_ss2_window`, including
integer donor clock and no donor-current-A. `w1_future_aas_member` gives the
actual future member and its ownership. `./scripts/check.sh` passed with 2566
audited declarations, allowed axioms only; module lint 14/15 substantive,
vacuity scan 0/15 flagged. Original output: `daytime/check_nonminimal.log`.
Thus the Lean candidate and computational protocol are complete. Card remains
CONJECTURED for promotion bookkeeping until the required independent-session
semantic audit; do not read this as an independent review having occurred.

Same-session shortcut audit: the existing fixed shortOff assignment does NOT
already avoid donor oldest S. Three compatible lag-11 charge collisions exist
in `daytime/short_charge_donor_exploratory.jsonl` (OBSERVED, exploratory script
was an inline command). This rules out that particular shortcut, not all possible
fixed injections. The tight-owner-family reasoning is not merely a direct use
of the old injection's image property.
