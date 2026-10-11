# Independent paper pass: common-oldest SS2 pair

Conclusion: STOPPED for a capacity proof in this independent pass. The local Hall claim remains CONJECTURED. There is a complete PROVED-PAPER auxiliary chronology/word-geometry argument below, but it is not a new allocation mechanism and does not resolve the acceptance target. The parent retains the independent periodic falsifier. No Lean, registry, repository, or git changes were made.

Base revision: ba7fe41e3c96d0762198731d658b10dbfd9f53d1. Read-only worktree: /Users/hirokidaichi/.codex/worktrees/p2-terminal-tail-bound/recaman-lean-research. Instructions, protocol, relevant glossary/proof-map/portfolio entries, current October 3 plan, E133 card/source, SS2LowSSTight, TerminalASSBound, TwoSSPeriodicSupply and TwoSSEndpoint were inspected. No alternate primary-checkout results were used.

## Exact research claim

All p>0 and p-periodic e:Int→Bool with positive period sign mass. Distinct current-A phases L within [0,p), arbitrary specified P2 windows with SS≤1. Distinct v,w outside L, current-A, specified positive-prefix-minimal P2 windows with exactly two overlapping SS edges, sharing the phase of their actual oldest S. Let B=L∪{v,w}, N the union of actual S phases in the specified windows. Ask |N|≥|L|+2. No lag/period/|L| upper bound, Hall/owner/NoSAAS/orbit assumptions.

## Complete auxiliary geometry (PROVED-PAPER)

Use E363 and full-endpoint injectivity to divide the donors into exactly one maximal terminal-A length 1 donor and one maximal terminal-A length 0 donor. Shift one by an integer multiple of p so their oldest S is the same integer s. Denote the current clocks t_A,t_S, the A-ended word W_A of lag d, and the S-ended word W_S of lag f. Write W_A=C A; C ends S. Then t_A=s+d−1 and t_S=s+f. Stripping the final A preserves SS, so ss(C)=2, mass(C)=0 and moment(C)=−d.

The clocks are unequal because their phases are distinct. If t_A>t_S, actual history gives W_A=X W_S A, where X is nonempty and ends in the actual current sign A at t_S. Since W_S consumes all two SS edges of W_A, X is SS-free. Mass append gives mass(X)=−1. But every SS-free word ending A has #S≤#A: pair each S with its immediately following A, an injection. Contradiction. Therefore t_A<t_S.

Put k=t_S−t_A>0. Actual history gives W_S=X C, |X|=k, and X ends A at t_A. Again ss(X)=0. Mass append gives mass(X)=1; moment append, using mass(C)=0, gives moment(X)=d. Also f=k+d−1. P2 lag mod4 (TwoSSEndpoint) gives k≡1 mod4.

An SS-free, mass-one word ending A has exactly one more A than S. If it starts A, all A runs have length 1: X=(AS)^r A, k=2r+1, moment(X)=r+1, hence d=r+1. If it starts S, every S run has length1 and the A runs contain exactly one additional A: X=(SA)^j A (SA)^h with j≥1,h≥0. Direct summation gives k=2(j+h)+1 and moment(X)=3j+h+1=d. The actual donor hypotheses restrict parameters further, but no extra restriction is needed for this necessary classification. Required congruences are j+h even and 3j+h≡2 mod4. A preliminary message incorrectly said j,h must be odd; this was corrected before handoff.

This geometry is all-period/all-lag and uses the actual common history. It neither asserts a universal finite span nor assumes the pair shares its full endpoint. NoSSMassOne E145 already classifies noSS mass-one words in greater generality: do not register the classification alone as a new frontier result.

## Exact boundary replay (COMPUTED)

Frozen before running in hypothesis-card.md: known/reused E133 pair only, no new discovery range, no claimed holdout. Script SHA256 9d5ba660f1ae5b59b058f895173c850cf58b71f17d324f7e9426b222191ce35c. Command:

`python3 /tmp/recaman-ss2-collision-sol61-20261006/boundary.py > /tmp/recaman-ss2-collision-sol61-20261006/boundary.out`

Exact output:

```json
{"A": {"length": 11, "mass": 1, "moment": 0, "p2_prefixes": [11], "ss": 2}, "C": {"length": 10, "mass": 0, "moment": -11, "p2_prefixes": [], "ss": 2}, "S": {"length": 19, "mass": 1, "moment": 0, "p2_prefixes": [19], "ss": 2}, "X": {"length": 9, "mass": 1, "moment": 11, "p2_prefixes": [], "ss": 0}, "compatible": true, "oldest": 0, "period16": "SASASSSAAAASAASA", "period_mass": 2, "source_A": 10, "source_S": 19}
```

Ascending phase word p16 SASASSSAAAASAASA has mass2. A-ended donor is current10/lag11, word AAASSSASASA, oldest0. S-ended donor current19≡3/lag19, word SASASAASAAAASSSASAS, oldest0. Both current phases are A, both windows have exactly two SS edges, and only their full positive prefix is P2. X=SASASAASA=(SA)^3 A(SA), satisfying d=11,k=9. Thus E133 survives ALL donor premises including positive drift and lag≥p; it refutes oldest injectivity, not this local Hall claim. With L empty the two donor neighborhoods have many S phases, so it is not a local Hall counterexample.

## Dependency chain and remaining edge

E368 gives |L| distinct actual lowSS S endpoint phases F⊆N(L) and excludes common oldest σ from F. The donors contribute σ∈N. Consequently |N|≥|L|+1. The above geometry controls the intervening prefix X but does not control all lowSS windows whose endpoints land on internal S positions of C or X after arbitrary periodic lifting. This is the precise missing interaction.

Attempt: prove a second donor S outside the fixed F. This is a stronger sufficient condition, not the original Hall assertion. Even if it fails, N(L) may contribute an extra S outside F and repair capacity. Attempt: assume |N|=|L|+1, so F exhausts N\{σ}, then rephrase the desired contradiction as an alternating assignment path. Without a structural transition rule this is only the target rewritten, not a research advance. Stop that route rather than implement an unproved endpoint-coverage Prop.

The weakest genuinely structural next input would have to restrict lowSS S-ended windows terminating at internal S positions of a core C satisfying the above mass/moment data, and force actual new neighborhood phases when such terminations cover both SS regions. No such restriction was proved here; treating that input as a premise would not eliminate the branch.

## Audit and next decision

The auxiliary proof uses current-A, actual history and exact SS budgets materially; periodicity only supplies the common-oldest lift and phase-distinctness. Positivity is not needed for geometry. The old card's textual phrase “largest q” for oldest is inconsistent with newest-first last S; all calculations here use the last S / smallest integer sign clock.

No finite computation is called a proof. No auxiliary geometry is called the local Hall theorem. No E067/E070 or surjectivity conclusion follows. Recommend retaining geometry only as a work packet, and let the parent's bounded falsifier determine whether any capacity-specific candidate survives. Reopen this independent paper route only with a concrete endpoint/core interaction beyond E368, not additional census bounds or an equivalent Hall wrapper.

Files created only in the requested /tmp directory: hypothesis-card.md, report.md, boundary.py, boundary.out. Commands also included read-only cat/sed/rg searches and shasum. No Lean validation commands were required because no Lean changed.
