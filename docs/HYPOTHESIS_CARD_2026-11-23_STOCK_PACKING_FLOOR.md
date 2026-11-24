# H-20261123-04: sparse old-stock packing pays extra floor loss

Current verdict: **PROVED-PAPER, human review pending; no Lean**. [E772/E773](RESEARCH_NOTE_2026-11-23_STOCK_FLOOR_POTENTIAL.md). Earlier proposer text below is chronological; frozen bytes are archived by protocol hash. Final work/journal values are not prepaid.


CONJECTURED / proposer-stage refinement of H03, not a completed theorem or another parent cycle. Same independent numerical mechanism. Exact full original cut/current/seen/floor/horizon conventions are those of H03; all stock stays at the OLD cut, never future stock or original free labels.

Choose ANY subset W of V_c intersect[3,x-1] with distinct values separated by at least3; p=|W|. Proposed explicit extra price is d=max(K,ceil(13p/5)). Claim, for every actual floor step,

    Pnext<=3P-1-4d,
    cnext<=c+2x-1-ceil(4d/3).

This is not a desired orbit-capacity Prop: W consists of literal OLD numerical values with a simple integer separation condition. The selected p need not be maximal; a greedy sorted selection is one computable witness. No class/free/coverage conclusion is input. Sparse old values can make ceil(13p/5)>K, while a dense filled stock still uses H03's K.

Proposer chain to falsify: consecutive primitive floor returns omit blocks of A-1 integer values, where A is their literal positive Dyck area. Nonempty omitted blocks have length>=3; primitive area cannot be2,3,5,6,8,11, using3l-2<=A<=l² and A congruent l mod2. A block containing k3-separated chosen values costs at least3/6/8/11 for k1/2/3/4, and>=3k-2 for k>=5. Hence every such block costs>=13k/5. The bottom omitted tail starts at1 and selected values are>=3, so its cost>=3k. Summing gives at least ceil(13p/5) unavailable integer floor-return values. With m returns, m<=x-1-d; H03's primitive-area inequality3t+2z<=2x+4m yields both bounds. This retains every repeated old value's per-step weighted load under iteration; no global one-time free charge is asserted.

Acceptance: complete all-depth old-stock interval proof plus independent actual/raw-Dyck checks, or exact counter to the coefficient/domain. Do not describe13/5 as the optimal whole-orbit coefficient: it is proposed as a valid local omitted-block price; its area14/block13/k5 geometry alone is not global sharpness. Small-area certificates must be supplied mathematically, not assumed new Props. Missing S freshness, counting duplicate list entries, counting high stock above current, or importing future stock must stay invalid.

New sharp-family lift to verify (H02 supporting discovery): ALL x>=1,h>=2,b>=h+3, initial absolute base b-h/current I=x+hb-h(h-1)/2, COMPLETE stock{0,I} union[1,x-1], original word S^h A3 S2 (AS)^(b-4) A. Proposed exact actual execution/all-original-positive/return2-h/D0, original actual A only h+2 from source h-1, all other b-1 A original LOWfree and pair-distinct. At the ORIGINAL retained cut h, current x/base b, the two floor cuts have P0=b+2x,P1=3b+2x+3,P2=9b+2x-4, so ratio tends9 at fixed x,h. The naive initial-State family was valid in its own domain; this lift adds a genuinely new old-S source/chronology producer and is not a resource-only retry. No canonical prehistory is claimed.

Freeze all source/parameters before the final current3CPU budget worker. Remaining before this unit1.022228CPU includes every killed/repaired H01 job. Per-worker1CPU/10wall; all previous stops remain. Discovery/holdout are new predicates on finite controls, not fresh orbit data. One repair maximum, no range extension or second resource attempt; failed finite check does not become PROVED-PAPER. All Lean remains unlaunched.

## Stable result and remaining uncertainty

See [RESEARCH_NOTE_2026-11-23_STOCK_FLOOR_POTENTIAL.md](RESEARCH_NOTE_2026-11-23_STOCK_FLOOR_POTENTIAL.md) and data/depth_general_20261123/PAPER_STATEMENT_AUDIT.md for the COMPLETE all-parameter producer, falsifier and meaning audit. Finite exact checks remain COMPUTED; mathematical proof remains PAPER/unreviewed, not Lean. One parent, local_progress0/general new evidence; full old stock/sources retained and C1/Q/H/SL/surjectivity remain open. All previous stops persist. Publication/confirmed work finalize later.

## Final shared parent record

R-20261123-01: actual start2026-11-23T06:02:22.769093+09:00; last confirmed work end2026-11-23T07:26:53.834720+09:00; confirmed5071.066s/shortfall2128.934s. Closed by recover2026-11-23T10:25:46.921691+09:00, NOT ordinary predeadline stop; unconfirmed in-window gap1986.165s excluded. ONE shared parent total, not extra per card. Local0/general new evidence/streak0. All成果/records locally saved but UNCOMMITTED/UNPUSHED because next actual clock was10:24, beyond publication window; next allowed window only. See DAILY/journal/final summary.
