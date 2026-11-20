# Generic seed minimum and unbounded reuse by original-free additions

PROVED-PAPER, human review pending, not Lean checked. Outside a finite explicit set of exceptional base clocks, the exact minimum seed size is paid by DISTINCT affine candidate classes, not by the number of original free A. A new all-N family shows that one initial blocker can force arbitrarily many distinct original-free A while every original prefix is positive and the full word is coherently greedy-realizable. This refutes a constant per-seed load mechanism, not C1.

## Exact generic minimum: all finite words, all old history

Let f[0,Q) satisfy E759 I/II, with its full ORIGINAL Nat0 H/B/EndN-free census. Define normalized affine pairs

    O_u=(H(u),(u+1)H(u)-B(u)), 0<=u<=Q,
    C_q=(H(q)-1,(q+1)(H(q)-1)-B(q)), q original-free A.

The associated numerical value is x+b*h+k for a pair(h,k). Let K be the number of DISTINCT C_q pairs, retaining every free clock in its class. Let E be the set of nonnegative integer b at which two DISTINCT normalized pairs in O union C have equal b*h+k. If slopes agree and intercepts differ there is no equality; if slopes differ there is at most one integer base, computed by exact divisibility. Thus E is finite, independent of x. With n=Q+1 the intercept bound |k|<=2n^2 gives every exceptional b<=4n^2; b=100n^2 is safely outside E.

For EVERY b outside E put

    x_min=1-min_(h,k in O union C)(b*h+k).

The set includes O0=(0,0), so x_min>=1. For EVERY x>=x_min, the minimum cardinality of DISTINCT values in an initial visited stock V of a coherent exact realization of f is

    1+K; and it is2+K if0 is also required in V.         (1)

Basic.State.seen is a list with harmless multiplicities; (1) counts distinct members, not list length. Current-in-seen is explicit; 0-in-seen is a separate condition, not silently part of the structure. All outputs and original-free candidates are strictly positive by the chosen x.

For necessity, an original-free C_q cannot equal an earlier word output at a generic base: equality then means IDENTICAL affine pairs, namely exactly an original P2 source (the current output cannot match its own positive-clock subtraction candidate). Therefore every such positive candidate must already belong to the ORIGINAL initial stock, since it cannot be justified by a nonpositive candidate or any output created before q. Distinct C pairs give distinct required stock values, all different from initial current x. This proves the lower bound, keeping every external blocker rather than discarding it.

For sufficiency choose V={x} union the K candidate values, optionally union{0}. Every original actual A is forced by its prior literal source output. Every original-free A is forced by its stock value. A S landing cannot equal a prior output: generic equality would be identityI. Nor can it equal an earlier free candidate: that would be identityII. If it equals a FUTURE free candidate q, identity of pairs supplies an original source from this S landing to q, contradicting that q was original free; equality at q equal to the landing clock is impossible by the height difference1. All S landings are positive. Thus the complete seed, including all future free candidates, executes exactly f. This supplies the upper bound in (1), not a desired seed-size hypothesis.

At exceptional bases, unequal-height numerical blockers may coincide (E111); (1) is NOT asserted there or for a canonical clock without checking it. K is NOT replaced by total original free. No initial stock is assumed to have a reachable canonical prehistory.

## A new all-N load family, with the complete positive domain

For s>=1 let

    Z_s=A^s S^(2s+2) A^(s+2).

Starting at relative height1 and area0, this balanced cycle ends at height1 and area0. It has length4s+4. For ANY N>=1 define s1=1,L1=8 and, for n>=2,

    s_n=4(L_(n-1)+1),
    L_n=L_(n-1)+4s_n+4=17L_(n-1)+20.

Set P=s_N+3, h=L_N/2+2, a=h+P, and take the literal full word

    f_N=S^h A^a Z_(s1) ... Z_(sN) A.

The N cycle starts and the final A are N+1 distinct selected A clocks. They ALL have preheight P and the SAME original affine candidate pair. They are ALL original free. Every nonempty original prefix is positive, and f_N passes all I/II; hence the explicit large-base/current complete seed gives an actual coherent finite realization in which the SAME ONE initial stock value forces every selected A. Other seed values, original suppliers and source-before prefixes remain present.

## Proof of no S collision, for unbounded N

Use relative height0 at the common candidate level P-1. Each cycle starts at height1,area0. At a S landing of relative height t inside Z_s, the local key is

    K_s(t)=(2s^2+4s-(4s+1)t+t^2)/2.

After an elapsed length L of complete previous cycles, the new absolute key is K_s(t)-L*t. All old cycle states and all old A candidates have |t|<=L+1 and key magnitude<=2L(L+1). Put L'=L+1. For s=4L', at every such old height,

    K_s(t)-L*t >=7L'^2+(17/2)L' >2L(L+1).

Thus no new S can match ANY earlier cycle output or A candidate. This compares the whole old history, not a truncated last cycle. New heights outside the old height range have no old alternative. The first s1=1 cycle has no preceding cycle and is handled directly.

Internally, a S landing that can match its own initial ascent state gives a balanced A^k S^k area k^2>0. A matching earlier A candidate gives (k+1)^2-1>0 with k>=1. Thus neither I nor II occurs inside one cycle.

Initial all-S head states have absolute height<=0, while every later S landing is at least P-s_N-2=1. There are no initial-head A. For the initial ascent before the FIRST cycle, a matching relative height t<=0 has area

    (1-t)(2-t)/2 - L*t + K_s(t)>0.

For t1 the area is s^2-L>0 (s1=1,L0 or the displayed growth rule); at t>1 no initial-ascent state exists. An initial-ascent A candidate requires t<=0 and reduces the positive displayed area by1, still leaving a positive K term. These cases preserve the entire original head and ascent. The final A adds no future S test. Hence all I/II are excluded for EVERY N, not inferred from finite controls.

## Proof that the selected A are genuinely free and positive

The candidate level is relative0. In the initial ascent its unique output at that level has relative key -1. Inside any Z_s, the descending S visit to level0 has relative area s^2+2s>0, and the final A ascent's level0 output has area-1. No output has height0 AND key0. The initial head is strictly lower in absolute height. Therefore no selected A has ANY original P2 supplier. Complete cycles return to height1/area0, so their selected candidate pairs are identical; the selected endpoints themselves are not supplied as hypotheses.

In S^h A^a only the third A is supplied, leaving deficit>=h-1. During all cycles there are only L_N/2 additions in total, so even counting EVERY cycle A as actual gives deficit>=h-1-L_N/2=1; S can only improve it. The last selected A is free and does not lower the deficit. Thus the full original-positive domain is supplied without an assumed transformed-positive Prop or replacement of A by free.

Choose b=100(Q+1)^2 and x=100(b+Q+1)(Q+1), and retain the ENTIRE seed {0,x} union all original-free candidates. The intercept bound places b outside E and makes all candidates/outputs positive. No output equals the selected candidate class. Consequently its one stock value is necessary and is reused by N+1 original-free A in this actual finite word. The other stock mass is not restricted or removed.

For EVERY proposed fixed load bound K0, choose N>=max(1,K0); then N+1>K0. This is a quantified no-go for a constant number of original-free targets per initial blocker, even after imposing original positivity and full coherent numerical chronology. It does not refute a charge with an explicit depth/value/stock-provenance cost, nor a bound under canonical-history conditions. Initial h, numeric values, other stock and other free grow with N; none is a bounded C1 wallet.

## Falsifier, results and remaining scope

The frozen new predicate tested207 chronology-consistent short words,300 generic realizations and791 one-at-a-time necessary-blocker removals. The short words overlap earlier finite S controls; these are NEW predicates and parameter controls, not fresh independent orbit data. No candidate sharing appeared up to length7, which was not treated as an injectivity proof.

The NEW recursive family controls N1/2/3 have lengths25/356/5980, selected original-free clocks[16,24]/[199,207,355]/[3307,3315,3463,5979], all sharing one stock value per word. Total original free/classes are13/12,195/193,3302/3299 in these FINITE outputs; no extrapolated exact all-N census is claimed. Full chronology, every original positive prefix and complete actual seed replay passed; full frozen output includes the entire seed. Source/input hashes, argv, revision, budgets and exact wait4 CPU are in [protocol](data/depth_general_20261121/GENERIC_SEED_PROTOCOL.json).

No graph/table extension, stopped formalizer, stopped vacuity helper or new Lean adoption occurred. Original Nat0 free is distinct from absence of every numerical blocker: selected A are original free precisely while an external seed value forces them. These arbitrary finite States do not supply the missing sign prehistory of that stock, a canonical orbit, or one fixed infinite orbit across N. The next consumer must pay load using a real value/depth/provenance budget; assuming a uniform seed load or K=F is STOPPED. C1/Q/H/SL/surjectivity and H01/H02 remain unresolved.

## Constant LOW wallet and explicit non-C1 boundary

The same all-N family has exactly two original LOWfree under its natural initial-S h and threshold1-h: they are the first two initial A. The third is actual; every later initial-ascent A is higher than the band and every cycle has absolute height>=1. Therefore even a finite proposed load bound K(LOWfree) fails on this seed-blocker mechanism, by choosing N>=K(2). This is a PAPER consequence of the full height/source proof, not a newly run finite LOW census.

Its minimum is exactly the initial-h, never below it, and the selected A targets have high preheight P. They are not the restricted return2-h or nearest-initial-source targets of C1. The other original free, stock, numerical values and h grow with N. No LOW-free charge injection for the actual C1 consumers is refuted.

## Existing canonical negative control for the generic domain

The already Lean-checked E111 certificate at canonical time5 has current a5=7 and rejected candidate1=a1 at next clock6, yet no finite P2 supplier. It is OLD evidence, not a new experiment. In the six-step word AAASAA, the candidate at q5 has pair(2,1) and output at u1 has pair(1,1), so they coincide at base0 although their normalized pairs differ. Base0 is exceptional. Earlier free candidates in that prefix are also nonpositive. Thus neither the generic-base condition nor the positive-free-candidate premise in (1) can be erased when applying it to canonical stock. The displayed generic seed minimum is not the minimum seed for that canonical finite prefix. No old Lean certificate was recompiled or relabelled as new progress.

Two exact hand-audited controls separate the premises. At base0/current10/seen{0,7,9,10}, the same AAASAA has outputs11,13,16,12,17,23 and ALL original-free candidates positive (9,9,10,7,11). K remains5, yet the coherent stock has only4 distinct values (3 if0 is omitted), because base0 merges unequal affine pairs and supplies an internal non-P2 blocker. Thus the generic-base premise itself is essential. Conversely the one-letter word A at base1/current1/seen{1} has no exceptional nonnegative base, but its candidate-1 is nonpositive and stock size1 suffices although K1; this separates the positive-candidate premise. These are direct finite arithmetic/greedy checks in the paper auditor role, not a new CPU experiment, canonical-reachability claim or additional generalization result.
