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

## 2026-09-23 02:30 audit of the local word lemma

This audit is deliberately narrower than H-05. The exact Lean signature
`SS2OldestPattern.ss2_intervening_prefix` says: for arbitrary `w`, if
`X=w++[A]` has mass zero, `moment(X)+|X|<=0`, and SS count at most two, then
`X=(u++[S])++v` for a P2 prefix `u++[S]` and nonempty `v`. Since every finite
A-ended word has this form, this is equivalent in both directions to the 15:21
card lemma and paper section 2. `v != []` is precisely strictness.

The two direct inequalities also match paper section 1. For every natural q,
`moment_ending_A_budget` proves `q+1 <= moment(X)+q|X|` for an A-ended word
with SS count at most q. `moment_ending_AA_ss2` proves
`5 <= moment(X)+|X|` for an AA-ended word with SS count at most two. Their
proofs use structural induction and the earlier proved suffix mass bound. The
prefix proof is well-founded recursion on word length, excluding AA by the
second inequality, stripping terminal SA, and invoking the established
low-SS/zero-SS prefix lemmas in the SSA/SSSA cases. It neither assumes the
conclusion nor uses a defined unproved Prop, periodicity, OwnerFamily, or orbit
facts. The statements have no length cutoff.

The original frozen checker was replayed byte-identically: all binary words
through length 18 give 8 premise cases, and the generated ending-A mass-zero
exactly-SS2 length-20/24 sets give 8 and 16 cases. The literal all-word audit
through length 18 has 3 equality and 5 strict-negative cases; the smallest is
`AASASASASSSA` with P2 prefix `AAS`. It also checks the two inequalities on
434,721 and 45,976 instances. Removing ending A, mass zero, the moment bound,
or the SS bound yields respectively `AAASSS`, `SASASSSA`, `SA`, and
`AAASSSSA`, each lacking the conclusion. These are finite checks and controls,
not the proof or a new holdout.

E-130's standard-step-115 word `AAASSSASASA` still refutes the broad SS<=2
S-ended prefix normalization. It is outside the new lemma's mass-zero and
moment-plus-length premises. This local lemma must not be described as undoing
E-130 or proving a general normalization.

The target file SHA is
`a9540f5f891198ec91eefd73f62f9e35d4e59f645936dc3a349504e529b325de`.
Direct Lean, vacuity 0/13, lint 13/13, and full check (392 jobs; 2,572 axiom
declarations) pass. The modified root imports the module, but Audit and the
registry do not contain this result; the source is untracked. Build acceptance
does not register it or replace semantic review.

Candidate packet: `docs/data/issue73_20260923/slot0230/`, containing verbatim
signatures, dependency audit, frozen source/card/paper/experiment snapshots,
raw streams, commands, and a relative manifest. The independent Sol verdict is
recorded separately by the parent before any application of this proposed
card. Until then the procedural result is pending.

H-05 remains `CONJECTURED`. Paper sections 3-5 and the source's downstream
AAS/w1 lemmas, stream decomposition, periodic transport, donor avoidance, and
deletion are unreviewed obligations. The source has no final theorem for the
whole H-05 claim. H-02 and H-03 remain `CONJECTURED` with their historical
preformalization entry gap; this audit does not repair or use them as
established inputs. No registry/frontier/proof-map/Audit promotion follows
from this bounded local audit.
