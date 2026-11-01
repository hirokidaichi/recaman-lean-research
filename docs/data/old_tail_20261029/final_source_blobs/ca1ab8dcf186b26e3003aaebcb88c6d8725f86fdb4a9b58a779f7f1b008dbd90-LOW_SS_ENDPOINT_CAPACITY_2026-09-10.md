# Joint low-SS supplier capacity

`PROVED-LEAN` (E-128): in every periodic sign stream, the number of current
A phases having a P2 window with at most one adjacent SS is at most the
number of S phases. This includes clean and one-SS supply **together**.
There is no lag bound, positive-mass assumption, NoSAAS assumption, or
minimum-witness assumption in the theorem.

The full capacity E-070 and simultaneous-supply exclusion E-067 remain
open. The previous short-plus-clean theorem and this theorem have
incomparable domains: seven short canonical cases through 10^7 steps are
outside the new class. Their union has not been proved to share one budget.

## Exact objects and statements

A finite word is newest-first, with A=+1 and S=-1. Write

- `mass(w) = sum_i sign(w_i)`;
- `moment(w) = sum_i (i+1) sign(w_i)`;
- `P2(w)` for `mass(w)=1` and `moment(w)=0`;
- `ssCount(w)` for the number of adjacent SS edges, counting overlaps.

For a two-sided stream e, `past e t d` consists of the signs at
`t-1,...,t-d`. The source is the **current** sign e(t), outside the word.
An endpoint is the sign time `t-d`, not the state time of the blocked value.

`LowSSPeriodicSupply.periodic_lowSS_capacity` takes any positive integer
period p, its periodic stream e, and any duplicate-free list U of phases
in `[0,p)`. For every u in U it requires e(u)=A and the actual P2 predicate
on some `past e u d` with `ssCount<=1`. It returns

`length(U) <= length(subPhases e 0 p)`.

The end-S premise appears only in the intermediate
`periodic_Sended_lowSS_capacity`; the final theorem derives it by shortening
the witness. `periodic_clean_oneSS_capacity` explicitly discharges the
original clean-or-one-SS disjunction. `positive_period_requires_two_SS`
then gives an A phase all of whose P2 witnesses, if any, contain at least
two SS. That last statement does not assert that this phase has a supplier.

## Proof, with the new dependency chain

**1. A-ended mass and moment.** If a nonempty word ends A, every S can be
paired with a following A except for an S followed immediately by another
S. Thus `mass(w) >= -ssCount(w)`; the Lean proof removes initial A, SS,
or SA and checks the boundary cases.

Every suffix of an A-ended word with at most one SS has mass at least -1.
The first moment equals the sum of the masses of all nonempty suffixes.
The final A contributes +1, so

`moment(w) + length(w) >= 2`.

This bound does not require mass one or NoSAAS. In particular a word ending
AA with at most one SS has moment at least 3: appending its last A adds
`length(prefix)+1` to the prefix moment.

**2. Deriving an S endpoint.** First consider an SS-free word of mass one
and nonpositive moment. Remove its final pair. SS is impossible, AA has
positive moment, SA increases the previous moment by 1, and AS decreases
it by 1. If the AS-ended word has moment zero, it is the required P2
prefix. Otherwise removing the pair preserves nonpositive moment at mass
one, so induction gives an S-ended P2 prefix.

Now consider a mass-one, nonpositive-moment word ending A with at most one
SS. Its last pair cannot be AA, so it is SA. Remove this pair, leaving a
mass-one word of strictly smaller moment. If that prefix ends A, apply
induction. If it ends S, the removed pair creates an SS at the boundary;
the preceding prefix must therefore have **zero** SS, and the previous
lemma applies. These inductions also check empty and one-letter cases.

Consequently **every** P2 word with at most one SS has an S-ended P2
prefix. `stream_S_witness` proves that it is a shorter window in the same
stream, with `0<f<=d`; `minimum_endpoint_S` shows a minimum witness already
ends S. No paper classification is a premise of these Lean results.

**3. Different A sources cannot share an endpoint.** Suppose t<u and the
two P2 windows end at the same integer sign time. The later word splits as
`v ++ earlierWord`, where v is nonempty and ends with e(t)=A. The P2 moment
identities give

`0 = moment(v) + length(v)*1`,

contradicting step 1. The SS count of v is at most that of the later word.
The symmetric case treats u<t. This proves the actual stream theorem
`LowSSEndpoint.endpoint_injective`, independent of periodicity.

**4. Periodic gluing.** Choose an S-ended prefix from step 2 for each
source, and map it to `(u-f) mod p`. Equal residues can be lifted to equal
integer endpoints by shifting one source and its entire window by a
multiple of p. Step 3 then equates the two source residues. The resulting
map is an injection into the S phases, including windows wrapping around
the chosen period boundary. Finite list cardinality gives the theorem.

## Negative controls and scope

The stopped E-069 period12 control SSSSAAAASAAA still has an endpoint
collision: phases7/11 have minimum lags11/3 and share S phase8. The first
window has three SS and is outside E-128. The older E-073 A-ended minimum
word has two SS and is also excluded. `regression_controls.py` retains
both and independently replays the new canonical boundary.

`current_A_control` uses the common-endpoint words `AASSAAS` and `AAS`.
Both are P2 and the longer word has one SS, but the older current sign is
S. Omitting current A breaks the endpoint argument.

`two_SS_control` uses the intervening word `AASASASASSSA`, which ends A,
has mass zero, and has moment minus its length. Appending the P2 word AAS
gives another P2 word with two SS. This breaks raw endpoint rigidity when
the defect bound is relaxed. The longer witness in this control is not
minimum, so it is not claimed to refute minimum-witness capacity.

More decisively, `CanonicalLowSSBoundary` kernel-checks the **standard
orbit** at sign time 114 (step 115):

- current sign A;
- minimum P2 lag 11, backward word `AAASSSASASA`;
- exactly two SS and no SAAS;
- oldest sign at time 103 is A;
- no P2 window of length at most 11 ends S.

Thus even actual canonical provenance and NoSAAS do not rescue the
S-ended-prefix normalization at two SS (E-130, `REFUTED`). This does not
refute E-070 or a different allocation method for windows with more SS.

The old period-13 control `SSAAASASASAAA` has minimum suppliers at phases
11 and 12. Their former separate maps both used S phase 9. The new endpoint
map uses S phases 0 and 9 respectively. The old collision is actually
resolved, not removed by excluding family B.

## Reproducible finite evidence

E-129 is `COMPUTED`, independently of the proof.

1. `endpoint/periodic_falsifier.cpp` directly computes integer mass and
   moment on **all 8,388,606 binary words of periods 1..22**, all period
   masses, with SAAS allowed. The frozen split is discovery 1..13 and
   holdout 14..22. Every S-ended low-SS witness is checked, including
   nonminimum witnesses; no endpoint or capacity violation occurred.
2. `endpoint/finite_verifier.py` independently checks all **1,048,575**
   words of lengths 0..19 against the mass/moment bound and prefix
   normalization, with the negative controls above. This later semantic
   regression is not relabeled as a fresh holdout.
3. `endpoint/orbit_endpoint_census.cpp` replays the first 10^7 standard
   steps with E-111's exact prefix key. All **992,184** low-SS minimum
   suppliers have distinct actual S endpoints. This is **75.39988%** of
   the 1,315,896 finite-P2 supplied A steps. The 921,809 clean and 70,375
   one-SS counts and every replay checkpoint exactly match the prior
   independent SS census. This previously used canonical range is a
   regression, not fresh discovery/holdout evidence.

There are 70,208 newly covered canonical sources outside the previous
short-plus-clean class, and **seven** previously covered short sources
outside low-SS. All seven have word `AAASSSASASA` and an A endpoint. The
separate percentages cannot justify adding the two capacity inequalities.

The period scan bound 4p is complete for its S-ended predicate. For a
word ending S, mass one implies `AA_count <= SS_count+2 <= 3`, by counting
runs. Its period must contain an AA edge: without AA, an S-ended word has
mass at most zero. A window of length 4p+1 contains four copies of every
cyclic edge, hence at least four AA edges, a contradiction. This
completeness argument is on paper; the Lean capacity theorem has no scan
bound or finite-computation dependency.

Sources, exact commands, hashes, and outputs are in
`experiments/issue73_20260910/endpoint/` and
`docs/data/issue73_20260910/endpoint/`. The inherited evidence manifest
was separately verified against baseline commit `2ed8606` (495 entries,
47 logged source identities) before root/audit changes.

## Repetition budget beyond one SS (E-131)

`EndpointRepetitionBudget` proves a quantitative continuation of the same
obstruction. Consecutive current-A sources with a common endpoint force
at least two SS **inside their intervening segment**. SS count is
superadditive under append, so m+1 increasing source times with endpoint0
force at least 2m SS in the largest word. No SS upper bound is assumed.
The zero endpoint is a coordinate choice; the one-step increment theorem
allows any integer source time and common old endpoint.

The bound is sharp in an explicit common history. Set V=AASASASASSSA and
Wk=V^k AAS. V has length12, mass0, moment−12 and ends A. Every Wk is P2,
contains exactly2k SS, and is a suffix of WK for K≥k. In A++WK the current
source positions12(K−k) are distinct and A, and their window endpoints all
equal the last position. The whole history avoids SAAS. These assertions
are checked for every K,k in Lean, and the frozen finite falsifier checks
K0..8 discovery and K9..32 holdout.

The family has a lag3 P2 prefix AAS at **every** source. For k>0 the chosen
Wk is therefore not minimum, also proved in Lean. This rules out constant
multiplicity for arbitrary P2 choices, not minimum-window endpoint methods
or E-070. Different endpoint groups can reuse the same SS; the local 2m
budget is not yet a global S allocation. Full audit after E-131:1,635
declarations.

## Decision

The H-28 unit is complete: joint clean/SS1 capacity is `PROVED-LEAN`, and
its original end-S dependency on the paper classification is eliminated.
The next useful question is how to allocate windows with at least two SS
together with this class. Require a new common-history inequality that
survives the canonical step-115 control. Stop direct extension of
S-ended-prefix normalization; do not resume fixed offset or lag tables.
