# Hypothesis card: minimal SS2 donors and short tight motifs, arbitrary donor length

- ID: `H-20260920-05`
- Created: 2026-09-20 15:14 JST
- Status: `CONJECTURED`
- Owner: same-session research roles, no independent reviewer

## Exact question

For every integer sign stream e, a current-A clock u0, and any d with
P2(past e u0 d), no proper positive P2 prefix, and SS count2, is the oldest S
incompatible with (a) an AAS member covering it or (b) a w1 member covering it
together with the forced next two A signs?

Formally, if v=past e u0 d, s=u0-oldestOffset(v), e u0=A, and v satisfies
those three word conditions, then neither of these configurations is possible:
1. e(s+1)=e(s+2)=e(s+3)=A (an AAS member at s+3).
2. for t=s+1, s+6 or s+7, past e t 7=w1, e t=e(t+1)=e(t+2)=A.
The three shifts correspond to w1's actual S offsets1,6,7.

If established, H-01's short-owner theorem and the H-03 prefix reduction give
avoidance/deletion for arbitrary-length MINIMAL SS2 donors, while B still has
P2 windows of length<=11. It does not remove the short-B restriction or prove
all-lag Hall/capacity. H-04's nonminimal length15 counterexample remains valid.

## Prior evidence and dependencies

- E-350 covers donor length11; H-02 extends that to nonminimal length11.
- E-133 refutes oldest-S joint injectivity, which is not being proposed here.
- TwoSSEndpoint.ss_one_two_no_shared_endpoint excludes endpoint sharing of
  current-A SS1/SS2 windows, but oldest S need not be the endpoint (trailing A).
- SSGapBudget gives exact A-gap budget; with SS2 there are only two extra S
  within S-runs and four A beyond the mandatory separators for a mass1 word.
- The prior lag15 certificate route was explicitly stopped for kernel cost;
  do not restart forceful certificate checking as this question's substitute.

## Falsifier and acceptance

Discovery lengths11,15,19: enumerate SS2 mass1 words by their S-runs and A gaps.
Validate the generator independently against all2^d words through19.
For each P2 word record minimality, number of trailing A, and all compatible
AAS/w1-complete-motif placements. Nonminimal length15 control must reappear.
Holdout lengths23,27,31: freeze generator before running; check all such words,
not random samples. This computation is for structural discovery, not proof.
If a minimal compatible word occurs, build and independently verify a periodic
countermodel. One actual counterexample stops the broad statement.

Success requires a length-independent argument from the gap/moment conditions,
or a concrete countermodel. Merely extending a census is not frontier progress.
If no argument by15:50, stop formalization of the broad claim and record the
precise missing local word lemma; keep the established length11 candidates.
Complete the day's validation and handoff before16:30.

## Proposed dependency chain

Finite defect budget => classify possible terminal A-run and last few gaps;
moment0 plus no earlier P2 excludes AAS/complete-w1 cover patterns => local
oldest-S avoidance => periodic short-tight avoidance via the actual OwnerFamily.
The unknown edge is the terminal-pattern exclusion, not the periodic transport.

## Evidence / decision

Discovery generator exactly matches independent binary enumeration at11,15,19.
Holdout23,27,31 contains647,1673,3605 minimal SS2/P2 words, respectively; no
compatible AAS or complete-w1 pattern. Nonminimal controls reappear at all lengths.
Raw data and source hashes: `daytime/minimal_donor_{discovery,holdout}.jsonl`
and `daytime/PRE_MINIMAL_DONOR_PATTERNS_SHA256SUMS`. This remains finite evidence.

15:21 proof-route refinement, before implementation: the gap argument suggests
a simpler induction on actual words. The new lemma to falsify is:
for every w, if x=w++[A] has mass0, moment(x)+length(x)<=0 and ssCount(x)<=2,
then x has a strict S-ended P2 prefix. Split its final letters: AA is impossible
by a moment lower bound; SA strips off a neutral pair; SSA leaves a mass1
nonpositive prefix with at most one SS, and SSSA leaves a zero-SS prefix.
Existing LowSSEndpoint prefix lemmas handle the last two cases.

New lemma falsifier: all binary words through length18 (discovery), and all
ending-A mass0 words with exactly two SS at lengths20 and24 (holdout), generated
by S-runs with two extra S and three extra A. Test the full <=0 inequality,
not only equality. Also remove last-A or the SS bound as negative controls.
No mathematical statement of H-05 has been weakened by this proof-route change.
