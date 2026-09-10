# Hypothesis card: one-SS windows and a centered charge

- ID: `H-20260910-13`
- Created: 2026-09-10 JST
- Owner: Codex, four roles sequentially
- Status: `REFUTED` (periodic and canonical, `PROVED-LEAN` certificates); map `STOPPED`
- Base HEAD: `8dfbfb8f15eb2ff3d84629385cde99cd9f2bc9aa`

## Bounded question and exact candidate

Consider a periodic sign word with no cyclic SAAS. Freeze the proved
complete short/clean injection. For each remaining supplied A phase whose
minimum P2 window has exactly one adjacent SS, d≥15, set h=(d+3)/2.
If the sign at offset h is S, charge it. Otherwise charge offset h+1 when
the newest window sign is S, and offset h−1 when the newest sign is A.
Does this charge always hit an unused S and inject across all such phases?

This is a new restricted hypothesis based on the no-SAAS/one-SS language;
the unrestricted midpoint selectors stopped in E-088 are not reopened.
No offset repair is permitted in this card. A failure stops this centered
map even if full residual domains would still have a matching.

## Proposed structural explanation (to audit, not assume)

For n S and n+1 A, write A gaps around the S positions. Exactly one SS
means exactly one internal zero gap z. The other internal gaps start at1,
leaving three extra As. No-SAAS excludes an internal gap2. After excluding
shorter P2 prefixes, the possible long minimum windows should reduce to:

1. both ends S, one internal gap4 at j≠z, all others1, with
   n=6j−2z+1;
2. newest end A, oldest end S, one internal gap3 at j≠z, all others1,
   with n=4j−2z+1.

The other extra-A allocations either have impossible moment or already
have an earlier clean P2. The proposed shift of the midpoint uses the side
of the run4/run3 on which the central S lies. Hitting S is insufficient:
compatibility and injectivity are separate falsification gates.

## Predeclared tests / acceptance / stop

- Exhaust all binary periods3..12 discovery,13..18 holdout, filtering cyclic
  SAAS. Detect all short and clean supply and all minimum one-SS windows.
  A one-SS window has d≤2p+1 if the period contains SS; otherwise it is not
  one-SS. Scan through2p+2, stopping after the second SS once past lag11.
- Independently enumerate all gap allocations above with n≤32 discovery,
  n33..128 holdout; directly sum moments and all shorter prefixes. Include
  the other end allocations to audit the proposed classification.
- Place the resulting exact windows in cyclic words with an A current phase
  and SSS / ASSS / AASSS buffers; retain only no-SAAS cycles. Include
  concatenations of two windows with independent parameters.
- Record full word, lags, proposed image, colliding old/new sources and an
  independent direct witness check. Stop on the first valid counterexample.
- Acceptance: a general proof of the stated map, or an exact counterexample.
  Do not turn a successful finite CSP or a new lag table into the conclusion.

## Evidence and stopping decision

The discovery scan stopped at p12, chronological SSAAAASASASA. Its old
supplied phases4 and7 have minimum lags3 and7, charging1 and0. The new
phase9 has minimum lag15 and newest-first window SASAAAASSASASAS, with
exactly one SS. Its center offset9 also charges0. The period has no cyclic
SAAS. Holdout and gap-family scans were not run after this failure.

The unmodified rule also fails canonically: sign times1350 and1352 (steps
1351 and1353) both charge sign time1343 (subtraction step1344). Direct
recomputation gives all P2 lags[7,63] at1350 and[15,51,59] at1352, so the
claimed minimum lags are checked independently of the prefix-key lookup.

`PROVED-LEAN`: `OneSSChargeCounterexample` certifies the periodic no-SAAS
word, both minimum lags, one SS, and the collision. Its alternative map
[4→1,7→0,9→6] still uses distinct S phases, so the example does not refute
capacity or full residual matching. `CanonicalOneSSWindow` checks the
actual15-sign window with ordinary kernel `decide`; the standalone
computation required maxRecDepth100000. Symbolic transfer in
`CanonicalOneSSCounterexample` proves both canonical minimum lags and
`canonical_centered_collision`; its current A signs follow from E-111.

Commands and source hashes are in `one_ss_charge.txt` and
`one_ss_canonical_counterexample.txt`. Full audit passed1,445 declarations
in `check14_counterexample_period_bound.txt` (shared with H-14).

Stop this centered rule with no offset repair. The proposed two-family gap
classification has not been promoted to a theorem: its planned full gap
protocol was skipped after the first counterexample. Next work must use
an interaction rule capable of moving existing charges, or a different
capacity argument, rather than a repaired midpoint selector.


## Canonical transfer diagnostic declared after periodic refutation

The period12 word SSAAAASASASA refutes the general centered map: phase9,
minimum lag15, and old phase7, minimum lag7, both charge S phase0. The
map is stopped; its offsets will not be repaired. Before finalizing the
handoff, test whether the same map failure occurs on the actual standard
prefix. Search times0..10^5 discovery,10^5+1..10^6 and10^6+1..10^7 holdout,
stopping at the first collision or non-S target. Freeze the old short/clean
map and the failed centered rule exactly. Independently recompute all lags
for the reported source times and both charge targets. This is a transfer
check, not a new candidate or a larger periodic census.
