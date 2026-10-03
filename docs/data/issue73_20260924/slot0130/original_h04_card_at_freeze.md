# Hypothesis card: boundary at donor length 15

- ID: `H-20260920-04`
- Created: 2026-09-20 15:10 JST
- Status: `REFUTED` (the period-16 literal certifies only the nonminimal length-15 extension)
- Owner: same-session four-role pass; limited independent review on 2026-09-23

## Exact question

Does H-03 remain true if the donor's length 11 is changed to 15, keeping
P2 and SS count 2 and still allowing a nonminimal donor window? The short
collection B, its tightness, periodicity and current-A premises are unchanged.

Acceptance is either a proof of this exact statement or an explicit periodic
countermodel with positive period mass, a current-A donor and a nonempty tight
short B that excludes donor phase u0 but covers its true oldest S. The extra
positive-mass/current-A properties are desirable properties of a
counterexample, not added theorem premises.
If a counterexample exists, do not silently replace the claim with minimal donors.

## Prior work and search

E-133 refutes joint oldest-S injectivity across some longer SS2 windows; that
does not itself refute tight-set avoidance. E-350 is length11 only. The older
2026-09-11 card predates the vacuity audit and its broad prose is not evidence.
SS2AASCollisionObstruction bounds a shared-endpoint intervening length below by
12; this points to length15 as the first possible AAS collision. The current
question is about actual oldest S and a concrete tight set, not a fixed endpoint.

## Falsification before formalization

- Discovery: enumerate all 2^15 words, test exact P2 and overlapping SS=2.
- Place AAS and the consistent w1 triple {-3:AAS,0:w1,2:AAS} on the oldest S
  in all ways consistent with the entire donor word and its current A.
- Embed a surviving placement into a periodic word with no overlapping
  inconsistent bits, verify the actual least short supplies and tightness.
- Independently verify any counterexample from its literal periodic string,
  including all proper donor prefixes, true oldest phase, N(B), deletion and
  full-U Hall at the positive-period finite bound p(p+1).
- This is a counterexample search; no arbitrary larger period census is a
  success condition and no holdout is needed to certify one literal witness.
- Stop as REFUTED if one literal witness passes independent arithmetic and
  Lean computation; stop the broad length replacement, not the length11 theorem.
- Time limit: stop discovery by15:25 and preserve a negative result if no witness.

## Evidence / decision

The length15 replacement is refuted. Period16 chronological word
`SAAASSSASASASAAA`, donor15 with word `AASASASASSSAAAS`, mass1, moment0,
SS count2. B={3} has minimal AAS, N(B)={0}; donor's true oldest S is0,
so deletion leaves N empty. Period mass2; donor current A; donor not in B.
Donor has proper P2 prefix3, so this is NOT a counterexample with a minimal donor.

Discovery: all32768 length15 words,85 P2/SS2 donors,46 minimal. One AAS overlap
and one w1-triple overlap survive, both from the same nonminimal donor word.
Frozen source/card hashes: `daytime/PRE_DONOR_LENGTH_SHA256SUMS`.
Original output: `daytime/donor_length_boundary.jsonl`.
Command: `python3 -u experiments/issue73_20260920/donor_length_boundary.py`.
These historical census figures and the w1 example were not part of the
2026-09-23 independent review.

The original same-session implementation reads literal periodic strings,
recomputes supply up to p(p+1), and checks subsets for Hall in two examples.
For period16, full U={1,3,11,15} with least lags11,3,39,3. Hall itself holds;
the donor's NONMINIMAL lag15 selection is exactly the failed assumption change.
Command: `python3 -u experiments/issue73_20260920/verify_donor_length_boundary.py`.
Original output: `daytime/donor_length_boundary_verified.jsonl`.
Only the period-16 literal and its full-U check were independently rechecked
on 2026-09-23; the second example remains outside that review.

Lean `nonminimal_donor_length15_counterexample` certifies period, positive
mass, current A, donor P2/SS2 and its proper P2 prefix, AAS member, N={0},
true oldest phase0 and empty deleted neighborhood. Original build log:
`daytime/build_length15_counterexample.log`. This was same-session verification;
the later independent review below is the separate procedural check.

Decision: STOP the nonminimal length15 extension. If proceeding with minimal
donors, use a new exact question and keep this counterexample as a control.

## 2026-09-23 limited independent audit

Procedure verdict: **PASS for the one period-16 literal and this limited stop
decision**, following an independent Sol report and parent comparison of the
reported source, commands, raw output and hashes. The review record is
`docs/adversarial_audits/H-20260920-04_20260923_0100.md`. The audited Lean
source `Recaman/ShortTightDonorAvoidance.lean` has SHA-256
`bb12f35acc8e48c584cead52d675e36b034afda22f0f28ecfd245031f70fee85`;
the scoped candidate packet `docs/data/issue73_20260923/slot0100/candidate_packet.md`
has SHA-256
`d8b4f8292d7430d9ac7afd71720fcc545e25d3a835646a03d510b61d58284d11`.
Exact literal recomputation, verbatim statements, command/timeout/exit records,
raw stdout/stderr and the original 28-file manifest are in that slot directory.

The p16 witness has `B=[3]`, `N(B)=[0]`, actual oldest S phase 0, and empty
deleted neighborhood; it negates true-oldest avoidance and deletion Hall while
meeting all proposed premises. Its donor has proper P2 prefix3, so the
certificate supports `REFUTED` only for the nonminimal length-15 replacement.
The old 32768/85/46 census, second w1 example, minimum-period or minimum-lag
optimality, arbitrary-lag owner search, general Gate T6, and actual-orbit
claims were not independently reviewed here. No evidence-registry row is
added or promoted for this card.

The daytime formalization lacked an independent pre-formalization entry
check. The later adversarial review does not retroactively supply that
missing step. A minimal length-15 donor question requires its own exact
card and audit; the current witness does not decide it.
