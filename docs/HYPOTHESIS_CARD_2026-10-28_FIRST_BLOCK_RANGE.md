# Hypothesis card: remove the first-block upper bound in E432

- ID: H-20261028-02
- Parent cycle R-20261028-01. Local exploration; planned25minutes, first15min gate. Separate audit from research; CPU discovery0.
- Status: PROVED-LEAN (E-433).

## Exact question / quantifiers

For every actual Nat sign f, original0, n,h,M,R and padded BlockWord whole prefix, all h>=0,M>=1,R>=5, actual tail `Sh AM S^(R+1) AR S A^(R+1)`, is actual original free count >=2R-2? Int original p must be preserved. No zero/positive/target hypotheses and no artificial EndN tags. Unlike E432, M has no upper bound.

## Proposed weakest new edges and paper argument (not yet Lean)

The first-A source of the third ray satisfies `(2e-R)(R+2)=3`, by E432's exact key equation. For R>=5 it is impossible for any integer e, independent of M. Middle-S source is still impossible at any nonnegative clock. Initial-S is at most one source/clock, so third local<=2; second local<=2 if its A-source is impossible. The latter would require `(R+1)(R+1-2e)=1`, impossible since R+1>=6. Therefore both later real supply counts<=3 (including old<=1), and first real free>=M-2. For M>=5 this gives totalfree>=M+2R-7>=2R-2. M<=3 already E432. For M=4, a sharper third-ray initial-S exclusion yields third supply<=2 and firstfree>=2, so totalfree>=2R-2. Check each equation/all source positions before using this chain.

## Falsifier / boundary

M4,R5 has second-ray localclock4, so the old local-clock2 classification does not generalize. R5,M5 has third-ray initial-S source q2 with key=-2 and clock0: S2 A5 S6 A5 S, not a C1 counterexample. R4 has middle-S extra localclock0. Keep M/R cases exact, h0 and large prefix; same old history; overlap supplies union bound.

## Acceptance / stop / switch

Accept a new unbounded-M local supply bound or a precise counterexample, then actual free count and Int p plus G5/Audit/fullcheck. Neither a finite M probe nor an input free bound qualifies. No finite table reruns. Mathematical repair at most once. Stop if key equation is false, or within15minutes no edge/candidate reduction; switch to second-S target source/free coupling rather than adjust a constant blindly. Final free inequality may still hold if a stronger intermediate classification fails: distinguish parent versus auxiliary claims.

## Allocation

H01's accepted result frees the remaining exploitation reservation for the next missing edge; do not count completed time twice. Old plan setup10/exploit60/explore30/audit10/handoff10. H02 is local exploration, with symbolic source divisibility as an independent pruning mechanism; audit overruns deducted from research. Actual intervals only journal.

## Premise lookup correction before count implementation

Existing E414 `BlockOldRay.rayCount_S_A_S` already supplies local second-ray<=2 for all h/M/m. Reuse it directly rather than re-prove/count it as a new edge. New edge here is third-ray all-M exception classification and original totalfree coupling. The proposed second-ray divisibility argument is consistent but redundant.

## Result

PROVED-LEAN E433, fullcheck06:13:44,429jobs/2932declarations. `family_free_lower_all` / Int original p. First new all-M third-ray source edge checked06:09:31, gate passed. Exact exceptional R5/M5/h>=2 clock0 retained. Generic second-ray bound consumed E414; no duplicated result. No mathematical repair. First fullcheck was rejected for missing E433 frontier reference, added current scope and reran successfully; no gate bypass. Next H03 source-conditional actual count mechanism.

<!-- journal actual -->
## 確認済み実績（親cycleと二重加算しない）

2026-10-28T06:07:55.253101+09:00–2026-10-28T06:14:38.779084+09:00、6分43.526秒（当unitのresearch/audit込み）。[journal](data/daily_research/2026-10-28.json)の確定区間のみ。親cycle全体は119分13.128秒、未終了区間は未計上。予定局所上限と実績は別。終了後の確定値はDAILY参照。
