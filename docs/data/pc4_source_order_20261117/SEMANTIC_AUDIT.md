# Separate semantic audit of the PC4 paper chain

Role: auditor, after proposer/falsifier draft and frozen probes. Same agent, separate pass; not independent human review or Lean checking of the new result. Outcome: the paper chain is complete for the stated fixed-free budget. No new mathematical assumption or repaired conjecture was needed. The finite checks support only their exact cases.

## Exact inputs checked against owning Lean source

`Recaman.SingleWindowEquality.EndN f 0 b` includes `f b=true` and an original source t>=0 with t+k=b, k>0, height difference1 and area0. The note's B(q)-B(u)-(q-u)H(u) equals Ar(f,u,q-u); it includes heights u+1 through q. Therefore strict past sources, endpoint A and free all agree. No source is dropped by a reset at v or R.

`Recaman.CapacityEqualityInduction.BlockWord.nil` proves BlockWord[]. With n=0/a=0, `seg f 0 0=[]++replicate 0 true` is the empty segment. This is a real constructor, not an unproved BlockWord hypothesis at the global minimum.

The exact rank input is:

    theorem positive_r3_additions_free_bound (f : Nat → Bool) (n a B : Nat)
        {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n=w++List.replicate a true)
        (hpos : ∀ k, 0<k → k≤B → cN (EndN f 0) n k+1≤cN (fun x => f x=false) n k)
        (hfree : cN (fun x => f x=true ∧ ¬EndN f 0 x) n B≤3) :
        cN (fun x => f x=true) n B≤2*cN (fun x => f x=true ∧ ¬EndN f 0 x) n B+1

Source: `Recaman/BlockOldRay.lean`; included in `Recaman/Audit.lean`, registry E414. Its hfree is established for[0,R) in the paper proof, not inferred for[0,T). All prefix-positive assumptions restrict from T to R. No new r3 data or stopped r4 table is run.

The exact floor input is:

    theorem actual_floor_supply_count (f : Nat → Bool) (n a K : Nat) (m : Int)
        {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n=w++List.replicate a true)
        (hfloor : ∀ i, n≤i → i≤n+K → m≤Fw f i) :
        cN (fun t => Fw f t=m+2 ∧ EndN f 0 t) n K≤
          cN (fun t => Fw f t=m ∧ f t=true ∧ ¬EndN f 0 t) n K

Source: `Recaman/FloorSupplyFreeBudget.lean`; included in Audit, registry E658. n=a=0, K=T are valid. No upper ceiling or positive assumption is hidden in the signature. Its underlying `actual_floor_supply_injection` pays each actual A clock with a distinct earlier floor free, even when the A has several sources. This is not a payment of every source/window separately.

## A: last minimum and first return

1. A finite integer walk attains its minimum on[0,T], and its last occurrence v exists. Under the contradictory case m<=-h-5, the endpoint is at least seven levels higher, so v<T and recovery is real.
2. Two distinct original free after v are at m and m+1. Both are low. Floor exclusion uses the whole[0,T] floor, so possible sources before v are also included. If two A were already before v, the globally first two are low free; those two clocks and the recovery clocks are disjoint. Thus A[0,v)<=1.
3. R is the first hit of2-h **after v**. It is not the first occurrence on[0,T], which could lie on the initial descent. The unit walk and H(T)=2-h give R<=T. For v<=q<R, H(q)<2-h; every A there is low. The possible single A before v is the global first A and has height<=-h. Every A, and hence every free, before R is low.
4. The rank theorem applies to the original prefix[0,R), with its derived total-free<=3. High free after R can be arbitrary. The counterfactual family S^h A^r S^(r-2) shows that the same substitution on[0,T) would be false.
5. A[0,R)<=7 and the rise from v to R>=7 force m=-h-5, A[0,v)=0 and S[v,R)=0. Hence the whole prefix is S^(h+5) A^7, with no unknown earlier history left to preload a source.
6. For target A with a earlier A, an initial-S source must leave a-1 S before the run. Its area is a*(2-a); a=0 has no admissible source, a=1 has area1, a=2 is the sole supplied case. An internal-A source is only the length1 A window, also area1. Exactly six of seven A are free, and their heights<=1-h, contradicting the three-free budget. h1 and larger h have the same derivation.

Conclusion A is a floor **derived** from original free and positive prefixes. No depth/upper/run cutoff was assumed. The argument intentionally uses a weaker floor than might be optimal; that exact floor suffices for PC4.

## B: all source visits, payments and endpoints

The visit set at c=m+2 partitions into S, free A and actual A. Free A pays itself at c; actual A is bounded by the checked injection to floor m. For S at q, the next return r>q to c exists because the endpoint is above c. Its previous clock r-1 is A at m+1 and is original free. If q<q' are two S visits, r(q)<=q', so r(q)-1<q'<=r(q')-1. Thus these payments do not collide. They are all<T and the initial descending S visit is included. The three payment levels m/m+1/m+2 are disjoint, so the three bounds can be added without overlap. No ordering of source keys is assumed.

The floor m need not be attained. If a matching level has no eligible payments, its visit class is empty by the applicable argument. A source may itself be S: it is explicitly counted. The word S at T1/m-2 refutes B after dropping endpoint recovery, so that hypothesis is not silently discarded.

## Parent consequence and scope

Use A to choose m0=-h-4, then B at c=-h-2. Its free wallet is a subset of low free because c<=1-h. Thus the count of all original c-visits is<=F_low(T)<=3. PC4 needs four distinct original c-visits: offset5 target height is -h-1; every source is one level lower and outside the plateau; different keys24j+15 prevent reuse. This derivation was rechecked directly from the Z coordinates, rather than assuming the desired free bound. Boundary source h-1 at T alone supplies H(T)=2-h; the full parent's remaining boundary conditions are stronger, so discarding them for impossibility is valid. No condition is discarded to certify a counterexample.

Nonvacuity check of the broader parent: the previously independently audited deep M4 certificate h22/T168/lowfree44 remains a witness when the lowfree<=3 condition is removed (`../prehistory_cost_20261117/deep-discovery-best-M4.json`). It is not rerun or misreported as a low-free counter.

Acceptance: PC4 has no such original history, **PROVED-PAPER**, new chain not Lean-checked and human review pending. The existence question is answered negatively; the inequality4<=F_low(T) for M4 follows. M>=5 with free>=4, general M<=F_low, C1 and standard-orbit surjectivity remain open. Uniform arbitrary-rank progress is not claimed and the daily generalization tracker is not reset.

## Finite audit and limitations

The independent forward-area checker passed10 fixed certificate/control cases, saving every source table and the three wallet maps. The targeted last-minimum/high-free controls are verification cases, not a replacement holdout. The original frozen holdout had0 eligible last-minimum cases; this limitation remains in the result. There was no failed job, conjecture repair, or resource retry in this PC4 unit. Expected guard CPU/wall kills are guard tests, not mathematical failures.
