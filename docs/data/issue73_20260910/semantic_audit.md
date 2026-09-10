# Semantic audit: September 10 research

The audit was performed sequentially by the same agent after proposing,
falsifying, and formalizing the claims. It is not represented as an
independent human review. Independent computational implementations are
identified specifically where they exist.

The exact Lean signatures were extracted with `lake env lean` from the
saved [input](semantic_statements_input.lean.txt), importing the root module.
The [output](semantic_statements.txt) is a successful 114-line signature
check. Full proof checking and permitted-axiom enforcement are recorded in
[check26](check26_ss_gap_budget.txt) and the final check log.

## E-065 / E-120: original finite-state scope is preserved

`FiniteSeedPeriodicSupply.seeded_eventual_supply` quantifies over arbitrary
`b : Nat`, `s : State`, `N p : Nat`. Its hypotheses are b≤N, p>0, and actual
seeded signs repeating after N. The output constructs the periodic integer
representative and proves positive mass and a P2 lag 0<d<p(p+1) for every
integer A phase. It takes no mass positivity, candidate positivity,
bounded supplier, P2 witness, or future return as a premise.

- Informal to formal: the old paper reduction's finite history is the
  existing finite List in State. The actual update is the existing
  SeededReplay.run, not a new abstract transition. An arbitrary finite
  preperiod is represented by N. A later N can always be used.
- Formal to informal: absoluteSign at n uses step size n+1 and seeded
  relative index n−b. The signed-step and history-membership lemmas derive
  their facts from that run. The final theorem's strict lag bound implies
  the older non-strict upper bound. Old prose using 'step into t' is
  reindexed to sign time t−1; no extra step is dropped.
- Finite seed: no assumption that the starting value belongs to seen is
  present. Generated history is added by actual steps; pre-b artificial
  absoluteValue values are included only in a harmless finite upper bound,
  never treated as generated blockers.
- No circular supplier: the generic helper has an explicit blocker
  dichotomy; `seeded_addition_obstruction` derives it from CanSubtract.
  The final seeded theorem supplies that proof, rather than assuming it.
- Positive drift: `NonpositivePeriodDrift.period_mass_positive` has only
  natural-valued nonnegativity and the exact weighted recurrence. Balanced
  value moments sum to zero; this is distinct from the older candidate
  phase drift sum −p². The proof uses every phase, not just a boundary
  subsequence that could stay nonnegative while an intermediate step fails.
- Negative controls: empty history and unrecorded initial value are
  included in the frozen seeded computation. Infinite external history
  permits all-A forever and lies outside finite State. Balanced words
  allow arbitrarily long collision/P2 lags when positive mass is omitted.

The conclusion does not prove E-067, E-070, or unconditional absence of an
eventual periodic orbit. Even excluding periodic signs would not decide
surjectivity or non-surjectivity.

## E-105 / E-106: the clean union is a partial capacity theorem

The final signature counts the complete short supplied phases, minimum
lag-11 phases, and a distinct list Q of current-A phases having a clean P2
lag at least 19. Its result is bounded by the actual period's S count.
The concrete short injection is discharged in the proof, not assumed.

Clean P2 lags are 8k+3 and unique/minimum. Thus clean lags below 19 are
already in the short class, and the signature implements precisely the
union described in prose. Q may contain all remaining clean phases of the
finite period; neither a global fixed-parity premise nor an upper lag
cutoff appears. Dirty long supply is not covered. The special theorem
with all odd times A (E-104) is not applied to the standard sequence.

## E-109 / E-111: word language and finite diagnostic meaning

`canonical_noSAAS` takes d≤t and refers to the actual canonical sign
function. No negative sign time leaks into a finite history. The word
language theorem retains NoSAAS for arbitrary periodic words; standard
recurrence, rather than a finite census, discharges it for actual windows.
The ASAASAS control proves that arbitrary SS-free P2 need not be clean.

`canonical_P2_iff_height_one_blocker` gives both a cumulative sign difference
of 1 and an actual value equality a(u+d)=a(u)+u+d+1. A general historical
blocker can lack that sign difference; the t5 control is retained. The
70.065% denominator is finite-P2-supplied A phases through 10^7, not all
A phases, all blockers, or a limiting density.

## E-113 / E-114 / E-115: qualifiers and strict inequalities

- The sharp clean bound 3d+7≤4p requires current A. The weaker d<2p does not.
  The p3,d3 current-S control prevents dropping that hypothesis.
- The blocker-rigidity inequality uses clock n=t+1. P2 is forced by the
  strict inequality d(d+4)<4n; the equality family and initial AA show that
  replacing strict by non-strict is false.
- Periodic collision lag bound assumes positive period mass and n>d.
  In a real post-preperiod historical window, n=t+1 and d≤t−N, so the
  latter is derived. It is not a statement about arbitrary signed clocks.

## E-121 / E-122 / E-124 / E-125: classification and realization

`family_A_P2` and `family_B_P2` quantify over all legal n,j,z and certify the
actual gapWord. They do not by themselves exhaust arbitrary words or
prove all-parameter minimum lag. The seven-allocation exhaustion and
proper-prefix proof are recorded as PROVED-PAPER, not PROVED-LEAN.

The special W_k family has separate Lean proofs of P2, all-proper-prefix
minimality, NoSAAS, exactly one overlapping SS pair, and embeddings at
K+1 different current-A positions of one finite word. The unbounded demand
statement is read together with `finite_history_certificate`,
`shared_SS_location`, and `window_minimum`; arbitrary source positions are
not silently treated as valid P2 sources. This is an actual common finite
*sign word*, not a claim of canonical reachability for all k. Its many
ordinary S positions remain available, so it is not an E-070 counterexample.

The small family-B seed uses the existing exact greedy transition and is
kernel-certified. That seed is not said to occur in the standard orbit.
The separate standard example at step96,911,838 is COMPUTED, checked by
C++ bitset search and independent Python dense-byte replay from a0.
Search stopped on its first candidate; no absence through10^9 is claimed.
The 10^7 B count of zero remains correct only for its completed range.

## E-126: the premise audit strengthens, rather than weakens, the claim

`word_gap_representation` covers every Bool word. `ssCount_gapWord`
identifies actual overlapping SS pairs with zero internal gaps.
`noSAAS_internal_gaps` derives exclusion of gap2 from the actual forbidden
substring. No proxy budget is a hypothesis. The exact endpoint-plus-extra
identity uses mass1 only; counting gaps≥3 also needs no NoSAAS premise.
Counting *every* enlarged internal gap uses NoSAAS, with ASAAS a certified
negative control. P2 implies mass1 and excludes the all-A case through an
existing theorem. Inter-window capacity does not follow from this identity.

## Stopped claims and evidence levels

The fixed centered charge, fixed SS budget, and family-B exclusion are
refuted in their stated scopes. The finite one-parity-defect Hall proposal
has not been refuted or proved generally; its work branch was stopped.
The phase-energy candidate was an exact affine rescaling of old κ, not a
new potential. Finite passage does not reopen that branch.

A successful Lean build certifies these exact statements. It does not
establish the missing combinatorial step or the original open problem.

## E-127: one-SS capacity is paper-only and cannot be added to clean capacity

The two-family *exhaustion* theorem is used, so E-127 is PROVED-PAPER.
Both candidate windows, after removing family B's initial A, are S-ended
prefixes of the same past. An internal gap retains both bounding S signs
under extension, which makes lengths4 and3 incompatible with the other's
unique enlarged gap. This rules out two sources in one A run. Distinct
cyclic A runs have different preceding S phases, including across the
period boundary. All-A/all-S cases are handled explicitly. This does not
make images disjoint from existing clean/short maps, and does not limit
the number of runs that can share one old SS pair. The2p finite scan is
complete only for one-SS windows, by counting repeated cyclic SS edges.

The overlap between maps is nonvacuous: period13 SSAAASASASAAA has
one-SS phase11 and clean phase12 both mapped to S phase9. More generally,
a family-B current A forces a third A by NoSAAS; that third A has clean
lag3 and shares the run's preceding S charge. This refutes only the naive
union of these two maps, not the union's possible capacity inequality.
