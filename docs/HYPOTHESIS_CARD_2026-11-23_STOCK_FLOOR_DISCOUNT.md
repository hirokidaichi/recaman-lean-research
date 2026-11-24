# H-20261123-03: old visited-stock pays a floor-potential discount

Current verdict: **PROVED-PAPER, human review pending; no Lean**. [E772](RESEARCH_NOTE_2026-11-23_STOCK_FLOOR_POTENTIAL.md). Earlier proposer text below is chronological; frozen bytes are archived by protocol hash. Final work/journal values are not prepaid.


CONJECTURED, proposer-stage formula/proof to attack before adoption. Parent R-20261123-01, same independent numerical mechanism as H02 (not another parent or a renamed class-band hypothesis). main baseline ebb302144e5ce1bfb21c8e4124604fb91690f11b. No new Lean planned; all prior stops inherited.

## Exact all-depth producer

Take ANY actual greedy continuation of a coherent natural finite State at ORIGINAL clock cut c, with full seen set V_c and current x=X(c)>0, a=b+c>=0. Assume its literal height H never falls below H(c) through finite horizon Q, and H(Q)>H(c). Let v be the LAST visit to H(c), c'=v+1, z=X(v), t=v-c. The next A and floor H>=H(c)+1 after c' are supplied by this last-visit construction. Let

    K=# distinct values y in V_c with1<=y<x,
    N=# distinct values y in V_c with z<=y<x,
    P=a+2x, P'=(b+c')+2X(c').

Proposed NEW exact inequalities:

    3t+6z+4N<=6x,
    P'<=3P-1-4K,
    c'<=c+2x-1-ceil(4K/3).

K is frozen at the OLD cut c, never the future stock at v/c'. Full old stock is retained; count DISTINCT numerical values, not list duplicates, A, original free, or candidate classes. The global floor/horizon assumptions are explicit geometric conditions, not conclusions assumed as new Props.

Proposed proof chain: decompose the actual path c..v into primitive nonnegative floor-return excursions. A length2l primitive has area>=3l-2 (odd heights>=1, internal even heights>=2). Equal-height weighted values fall by exactly that area. Return values are distinct integers in[z,x-1] and are ALL fresh S landings, so their number m<=x-z-N. Thus3t<=2(x-z)+4m<=6(x-z)-4N. Since z+N>=K+1, substitute into P'=3a+3t+3+2z. This is a new quantitative use of actual S novelty; E764 only paid elapsed time/remaining value and its filled-stock consumer did not count arbitrary noncontiguous old values.

## All-depth consumer and exact sharpness proposal

For a finite actual word with H>=H(c0) through Q and H(Q)>=H(c0)+j, take successive last-level cuts c_i. P_(i+1)<=3P_i-1-4K_i yields

    P_j<=3^j P0-(3^j-1)/2-4*sum_(i=0..j-1)3^(j-1-i)K_i.

At every produced cut after the first, the previous floor value z>0 is already seen and lies below the new current, so K_i>=1 for i>=1. In particular P2<=9P0-8-12K0, improving OLD9P0-4. No source-before prefix or original free census is reset by this arithmetic cut. A last global minimum of a given actual word supplies a starting floor; it does not supply canonical reachability or a LOWfree budget.

The SAME numerical value may occur in many K_i. Exact weighted multiplicity is retained, bounded per value by(3^j-1)/2; it is NOT a one-time free-wallet charge or depth-independent load. Numerical stock cannot be substituted for original LOWfree. Remaining b/current/class-width/C1 costs remain explicit.

Sharpness discovery proposal: ALL integers x>=1,b>=0, complete initial stock{0,1,...,x}, word A(AS)^b A should be actual with c1=1,c2=2b+2,K0=x-1,K1=x and P0=b+2x,P1=3b+2x+3,P2=9b+2x+8. It attains BOTH stock-discount steps. At x1 it gives H02's coefficient9 no-go with fixed additive correction; at b0/x growing it should show coefficient4 on K is optimal. A distinct sparse-stock AASSA case x5/b>=4/V={0,2,3,4,5} should attain the ceil(4K/3) time discount with K3. These are proposer-derived examples, not fresh holdout data.

## Falsifier, acceptance and stop

Freeze worker parameters/source/argv before execution. Attack arbitrary extra stock, noncontiguous old values, b0/x1/empty return, large stock, all last-floor choices and full old prefix. Negative control: counting stock learned AFTER c instead of V_c should fail on the x1/b7 family, not be patched into the premise. Exact natural simulation must be independent of the area proof; a second checker must use actual sign words and literal primitive areas/past stock snapshots.

Accept only the all-word inequality proof with every initial/end/freshness term supplied, or an exact counter. Finite checks COMPUTED only. No equivalence/defined-hypothesis wrapper, no claim that K is original free. One repair maximum; resource-only retries of old failed Lean/guard/census are prohibited. Current math budget3CPU, used1.592267 before this unit; a new1second job launches only when measured remaining>=1. Guard1.129820CPU and Lean/other bookkeeping separate. Distinct numerical mechanism must receive>=25 actual minutes across H02/H03 before its parent allocation closes; no CPU job is a separate cycle.

Parent C1/Q/H/SL/surjectivity and the original class-depth/single-band conjectures remain open. A proven all-depth actual stock-paid potential would be depth_general_progress; a fixed example alone or the creation of this card would not.

## Stable result and remaining uncertainty

See [RESEARCH_NOTE_2026-11-23_STOCK_FLOOR_POTENTIAL.md](RESEARCH_NOTE_2026-11-23_STOCK_FLOOR_POTENTIAL.md) and data/depth_general_20261123/PAPER_STATEMENT_AUDIT.md for the COMPLETE all-parameter producer, falsifier and meaning audit. Finite exact checks remain COMPUTED; mathematical proof remains PAPER/unreviewed, not Lean. One parent, local_progress0/general new evidence; full old stock/sources retained and C1/Q/H/SL/surjectivity remain open. All previous stops persist. Publication/confirmed work finalize later.

## Final shared parent record

R-20261123-01: actual start2026-11-23T06:02:22.769093+09:00; last confirmed work end2026-11-23T07:26:53.834720+09:00; confirmed5071.066s/shortfall2128.934s. Closed by recover2026-11-23T10:25:46.921691+09:00, NOT ordinary predeadline stop; unconfirmed in-window gap1986.165s excluded. ONE shared parent total, not extra per card. Local0/general new evidence/streak0. All成果/records locally saved but UNCOMMITTED/UNPUSHED because next actual clock was10:24, beyond publication window; next allowed window only. See DAILY/journal/final summary.
