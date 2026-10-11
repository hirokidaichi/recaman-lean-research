# Final independent audit: internal SSS and the complete NoSAAS/SSS collision subcase

**PASS.** H-20261006-03's standalone internal-SSS endpoint exclusion has a complete paper proof without NoSAAS or positive period mass. The subsequently supplied next-oldest-S argument also closes the remaining NoSAAS, start-S h=0, oldest-SSS case. Combining it with the previously audited pure-alternating argument proves H-02's stronger two-excluded-phase inequality, hence the local Hall inequality, for the entire explicitly NoSAAS + single-SSS collision class. Label these statements **PROVED-PAPER**, not PROVED-LEAN. The general H-01/H-02 statements and the NoSAAS case with two separated SS edges remain **CONJECTURED**.

The repository was read only. No Lean or repository files were edited, no issue was changed, and no new census or new constructed parameter value was examined. Base checked: 65c25ab742ab4aa749bfd5f48438dbcb7b774d1d. This addendum supersedes the earlier audit's temporary limitation that the start-S h=0 branch was still open; it does not change any frozen hypothesis or control file.

## 1. Exact standalone statement and proof

Let p>0, and let e:Int->Bool be p-periodic. Let W=past e u d be minimal P2 with exactly two overlapping SS edges. Let s be the actual integer clock of its oldest S. Suppose W contains an SSS at chronological clocks q,q+1,q+2 with s<q. No current-A premise on this donor is needed. Define E_low to contain the full endpoint phases of every positive-lag current-A, S-ended P2 window having SS<=1; these witnesses need not be minimal, and there is no lag bound.

Then phase(s) and phase(q) are distinct elements of W's actual subtraction neighborhood and neither belongs to E_low.

- E-368, `SS2LowSSTight.oldest_phase_ne_lowSS_endpoint`, excludes phase(s). Its exact source premises are p>0, periodicity, actual donor P2/SS2/minimality and the candidate's current-A/P2/lowSS conditions. It has no NoSAAS, positive-mass, owner or assumed Hall premise.
- For an endpoint at integer q, a positive lag 1 or 2 has current S, contradicting current-A. A lag at least 3 includes both SS edges of q,q+1,q+2, contradicting lowSS. This step does not require P2, donor minimality, or NoSAAS. Periodicity moves a putative endpoint phase(q) to integer q while preserving all the window data.
- If phase(q)=phase(s), periodicity moves the S at q+1 to s+1. W then contains the three distinct SS edges starting at s, q and q+1. All lie in W since s<q and q+2 is in W. Their starting clocks are distinct even if q=s+1; overlap is allowed in the SS count. This contradicts SS2.

Thus the standalone statement is correct for arbitrary wrapping and arbitrary period mass. The two excluded phases supplement the E-368 injective normalized lowSS endpoint image for any finite nodup current-A lowSS family L with arbitrary supplied P2 lags. With two distinct minimal SS2 donor phases, their combined neighborhood consequently contains at least |L|+2 phases. LowSS members need neither minimality nor S-ending: E-368 normalizes within each original supplied window. The usual phase-distinct family convention is retained.

## 2. Fixed controls: independent replay and direct scanner

The three frozen source hashes matched `source-frozen.sha256` exactly:

- `experiments/ss2_internal_sss_controls.py`: 3dfcc73a5fd1928ef4afa3aa01f4e9b72ac12c2d24cec0632bc51302f41db56a
- `experiments/verify_ss2_pair_endpoints.py`: d1352240d59816a7f2d42e419f4600736a79866ab5d29d1e9ff5306c2b0528c7
- `experiments/verify_ss2_collision_pair.py`: d016fff233909a2cea0e678c95ccd73d5da9e15ed990227cea2edbe50e427263

Both original commands returned exit 0 and JSON exactly equal to the saved data:

```
python3 experiments/ss2_internal_sss_controls.py discovery
python3 experiments/ss2_internal_sss_controls.py holdout
```

I also wrote and ran `/tmp/ss2-pair-next-audit-20261006/internal_sss_verify.py`. It imports neither parent verifier. It independently reconstructs signs, mass/moment, all proper donor-prefix P2 tests, SS edges, circular NoSAAS, all lowSS S-ended endpoint witnesses, actual donor S neighborhoods, and the residual parameter identities. It scans all current phases and all lags through p(p+1), without stopping at the first P2 window. Positive period mass is checked in these six computational models; the existing positive-mass bound makes this finite enumeration complete for their endpoint witnesses. That computational bound is not a hypothesis of the paper statements.

| Fixed model | p | NoSAAS | s,q | All endpoint witnesses | Excluded phase count |
|---|---:|---|---|---:|---:|
| Pure alternating positive | 33 | true | 0,4 | 5 | 10 |
| Drop NoSAAS | 33 | false | 0,0 | 2 | 13 |
| Reused second-prefix model | 22 | true | -13,-3 | 1 | 9 |
| Remaining shape r=0 | 32 | true | 0,0 | 3 | 12 |
| Remaining shape r=1 | 72 | true | 0,0 | 7 | 28 |
| Remaining shape r=2 | 112 | true | 0,0 | 11 | 44 |

The negative C=ASASAAASSS control preserves the minimal SS2 pure-prefix pair but has NoSAAS=false and q=s. It refutes dropping NoSAAS from the *pure-prefix conclusion q>s*. It does not refute H-03 (whose premise q>s fails), and does not refute H-02 (13 excluded phases remain).

The p22 model is an important boundary: a NoSAAS collision already exists within the reused period<=22 range. Any prose saying this census had no NoSAAS collision must stay corrected.

The r=1,2 controls were held out for the frozen H-03 construction protocol. They were already seen when the new phase(s+1) conjecture was proposed, so they are **not fresh holdout evidence for that new conjecture**. They provide regression checks only. The next proof is the basis for its all-lag label.

## 3. Necessary form of the remaining NoSAAS/oldest-SSS branch

Use the previously audited actual-history geometry after a periodic lift:

W_A=C A, W_S=X C, d=d_A, t_A<t_S,

where C covers s through t_A-1, mass(C)=0, moment(C)=-d, ss(C)=2, and X is SS-free, ends A, has mass 1 and moment d. Both donors are current-A, minimal P2, and phase-distinct. Global NoSAAS restricts X to the pure-alternating form or X=(SA)^j A, with d=3j+1 and j congruent 2 modulo 4, j>=6.

For the second form, suppose the unique SSS begins at the oldest clock q=s. Then C=T SSS, T is SS-free, ends A, mass(T)=3. The earlier audited A-run classification, including the actual S immediately after T, gives

- start A: T=(AS)^a AAA (SA)^b and a=3b+2;
- start S: T=(SA)^h AAA (SA)^b, h>=1, but its P2 moment equation is 3h-3b-2=0, impossible modulo 3.

Hence C=(AS)^a AAA (SA)^b SSS with a=3b+2. Now

|C|=2a+2b+6=8b+10,   d=8b+11=3j+1.

Thus 3j=8b+10, so b congruent 1 modulo 3. Since b>=0,

b=3r+1, a=9r+5, j=8r+6, r>=0,
d_A=24r+19, |X|=16r+13, d_S=40r+31.

The proposed period word reverse(X C) A has length 40r+32 and mass 2. These are correct necessary shape identities. The fixed computations establish the full minimality/NoSAAS compatibility of the constructed words for r=0,1,2; they do not by themselves prove the construction is a valid minimal donor model for every r. The capacity proof below is conditional on the actual donor hypotheses and holds for every surviving r, without needing that separate all-r existence claim.

## 4. New all-future endpoint exclusion closes the remaining capacity case

Normalize s=0. The A-ended current is t_A=d-1, and t_S=t_A+2j+1. Consider a putative positive-lag endpoint at integer 1; its current time v is at least 2. Write its mass as the sum of actual signs on clocks 1 through v-1. This chronological mass equals the backward P2 mass.

The chronological signs from 1 through t_A-1 are exactly

SS (AS)^b AAA (SA)^a.

At v=2 the current is S. After the initial SS the cumulative mass is -2. The AS blocks alternate -1,-2. The AAA block reaches -1,0,1. Each subsequent SA block alternates 0,1. At every mass-1 position before t_A the next/current sign is S. The only current-A candidate with mass 1 at or before t_A is therefore v=t_A.

At t_A, the endpoint-1 window is C with its oldest S removed. Its lag is d-2. The removed S had backward weight d-1, so its moment is

moment(C)+(d-1)=-d+(d-1)=-1,

not the P2 value 0. This eliminates the only mass/current candidate in the first interval.

The next actual segment, from t_A through t_S-1, is reverse(X)=A(AS)^j. Starting from mass 1, it yields mass 2 or 3 throughout, ending at mass 2 with last sign S. Hence every current v in [t_A+1,t_S] fails the P2 mass condition.

For any v>t_S, the candidate window already includes the SS edge (1,2). If it has SS<=1, no later SS edge can occur. Its extra chronological segment starts at t_S, whose actual sign is A (also forced by the preceding S and lowSS), and is SS-free. Every S of a finite A-starting SS-free segment has a distinct immediately preceding A, so this segment has nonnegative mass. Therefore the candidate's total mass is at least 2. This handles every later time, without any assumption about future signs beyond the candidate's own lowSS condition and without a cutoff at a period boundary.

Thus integer endpoint 1 is impossible at all positive lags. Periodicity lifts every endpoint congruent to 1 to this same argument. Phase(1) is excluded from E_low. Phase(0) is excluded by E-368. These phases are distinct: equality would force p=1, incompatible with the actual S at 0 and a current-A donor. Both phases occur as actual S signs in C. Therefore |N_pair minus E_low|>=2, and the E-368 normalized image gives the required local Hall inequality.

This proof has no hidden endpoint matching, owner, Hall or positivity hypothesis. NoSAAS is used in obtaining the two exact shapes; once the actual C and X shapes are known, the endpoint-1 calculation itself does not need NoSAAS. The calculation uses actual signs and exact moment, so it is substantive rather than a reformulation of the desired capacity conclusion.

## 5. Final scope and stop decision

For a NoSAAS collision pair whose two SS edges belong to one SSS run, the complete case split is now:

1. Its chronological first S q is later than the common oldest s: H-03 supplies phase(s),phase(q), regardless of the X branch.
2. q=s and X is pure alternating: impossible by the previously audited SAA/next-S contradiction.
3. q=s and X=(SA)^j A: the new all-future calculation supplies phase(s),phase(s+1).

All three cases are covered on paper, and the excluded signs are actual donor S signs. Positive period mass may be omitted from this explicitly stated subcase theorem. Keep NoSAAS and single-SSS explicit; this does not silently weaken or settle the original general H-01/H-02 question. Separated SS edges, absence of NoSAAS when q=s, larger SS families, and the original Recaman surjectivity bridge remain unproved here. Abstract periodic sign examples are not actual orbit constructions.

The original frozen card ends at the internal-SSS lemma and pure-prefix corollary. Append the new necessary-form and endpoint-1 proof as a dated follow-on paper result without rewriting the frozen protocol or labeling the already-seen r=1,2 models as a fresh holdout. Do not leave the now-proved conditional residual capacity marked open merely because the separate all-r model-existence question was not proved.

**Stop this short pass here.** Preserve this complete restricted proof and its control provenance. A later bounded unit may formalize the exact subcase or test a proposed second-phase mechanism for the two-separated-SS case; neither is part of this audit.

## Audit artifacts

All under `/tmp/ss2-pair-next-audit-20261006/`:

- `internal-sss-final-addendum.md`: this proof and scope audit.
- `internal_sss_verify.py`: independent fixed-model scanner and frozen replay.
- `internal_sss_verification.json`: exact results and source hashes.
- `internal_sss_replay_discovery.json`, `internal_sss_replay_holdout.json`: exact original-command output.
- `internal_sss_commands.log`: commands and replay outcomes.
- `capacity-subcase-addendum.md`: earlier pure-alternating proof retained for provenance.

No Lean compilation or kernel-axiom claim is made for the new paper statements.
