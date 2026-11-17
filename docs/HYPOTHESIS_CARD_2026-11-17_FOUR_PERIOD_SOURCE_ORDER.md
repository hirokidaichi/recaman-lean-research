# H-20261117-PC4: four periods with at most three original low free

- Owner: Codex; explicit user continuation, 2026-11-17.
- Status: PROVED-PAPER for nonexistence of PC4; work state completed (new chain not Lean-checked, human review pending). This is an unscheduled bounded research unit, not a new daily parent cycle.
- Parent: H-20261117-PC / E728. All stopped constructor/SMT/beam jobs remain stopped.

## Exact question and domain

Does any original sign history f:Nat->Bool satisfy the PC card with M=4 and F_low(T)<=3? In full: h>=1, T>=h, L=T+33; initial S^h; every nonempty prefix through L has original actual-supplied A count+1<=S count; f[T,L)=Z^4 A, Z=ASSSSAAA; every A there is original EndN; each of the five boundary clocks T+8j has complete source set {h-1}. H(k)=sum(i<k)sign(f(i)), B(k)=sum(1<=i<=k)H(i). Original Win(u,q) is u<q, H(q)=H(u)+1 and B(q)-B(u)-(q-u)H(u)=0. F_low(T) counts original free A at q<T with H(q)<=1-h. No standard-orbit reachability is asserted. Depth, upper height, length, run count, and high free are unrestricted.

The necessary first source family comprises four distinct clocks at c=-h-2; the exact keys are24j+15 in the PC normalization. The second family and all alternative sources remain part of the parent. An impossibility argument may discard requirements only to prove a stronger exclusion, never to certify a parent counterexample.

## Candidate mechanisms fixed before their falsification

A. Last-minimum/first-return: under initial S^h, original positive prefixes, H(T)=2-h and F_low(T)<=3, conjecture min(H[0,T])>=-h-4. Try to break this without any depth/upper ceiling. A candidate dependency chain is: two original free on recovery from the last global minimum; at most one A before that minimum; a first-return prefix has all its free low; apply existing total-free rank-three bound only to that proved prefix. The conversion from low-free to total-free is an obligation, not an assumption.

B. Floor-visit accounting: for any original history with floor m on[0,T] and H(T)>m+2, conjecture #{q<T:H(q)=m+2}<=#{q<T:f(q)=A, not EndN0(q), H(q)<=m+2}. All upper excursions unrestricted. Split a visit by S / free A / actual A; pay the S visits with distinct later upcrossings at m+1 and actual A with the existing floor-supply injection at m. Check collisions, the last visit, and the initial descending visit. No rebasing at a minimum.

If A and B survive and admit complete proofs, apply B at m=-h-4: four necessary source clocks force at least four original low free, contradicting the parent budget. This is the weakest proposed chain; no assertion yet that it works.

## Roles, evidence, allocation and stops

Proposer freezes A/B above. Falsifier first checks small cases, endpoint equality, original versus declared supply, and histories with high free; a weakened model may refute only the relevant auxiliary. Formalizer does not create Lean until a useful complete paper chain survives. Auditor separately checks the exact original definitions, all quantifiers and theorem applicability, then independently checks any finite certificate.

Acceptance: an exact parent counter with all original sources/domain independently verified, a complete arbitrary-length/depth exclusion of PC4, or a strict new necessary condition. Finite absence alone is not acceptance. First checkpoint15 minutes from this card's freeze. Reserve25 minutes for distinct floor-visit/payment mechanism B and its semantic counterfactual audit; preserve actual timestamps and do not turn a reservation into claimed elapsed time. No request for a100-minute daily cycle is inferred. Local M4 completion and depth-general progress are reported separately; no tracker reset for a fixed-rank result alone.

No old stopped worker is rerun or expanded. New calculations, if needed, must freeze exact controls/discovery/holdout, hashes and CPU/wall caps in a separate packet before execution; initial mathematical worker budget0. Previously inspected prefixes are discovery/control only, never fresh holdout. One technical verification repair may be recorded as a separate version with unchanged inputs/limits; no silent mathematical repair. Paper-only branches use boundary/countermodel analysis with range not applicable. Stop a candidate after a counterexample or no new edge at15 minutes; no resources-only continuation. No paid service or external literature claim is needed.

## Existing inputs and remaining obligations

E728 first-family source extraction and source spacing are PAPER, not Lean. Existing Lean inputs under review: BlockSuffixPositivity.two_nonsupplied_additions_of_recovery; BlockOldRay.positive_r3_additions_free_bound; FloorSupplyFreeBudget.actual_floor_supply_count; original floor non-supply. n=0, empty BlockWord must satisfy each interface explicitly. The hypotheses do not provide total free<=3 on all[0,T]. Existing rank-three clock theorems cannot be applied to the whole history from the low budget alone.

## Evidence and decision

At freeze the candidates were unproved. Discovery/holdout returned no auxiliary counterexample; the finite method stopped after its planned jobs. Discovery4096 words:2636 depth cases,99 first-return interfaces,64364 floor-visit cases. Frozen holdout84 words:114 depth cases,13371 floor-visit cases, **zero first-return interfaces**; no independent evidence for that interface is claimed. The separate forward-area audit passed10 fixed certificate/guard cases. Targeted first-return/high-free controls are verification, not retrospectively fresh holdout.

The complete paper proof is RESEARCH_NOTE_2026-11-17_FOUR_PERIOD_SOURCE_ORDER.md, separate audit in data/pc4_source_order_20261117/SEMANTIC_AUDIT.md. Candidate A holds: last global minimum before the second A, first return gives a true total-free<=3 prefix, existing rank bound gives<=7 A, and an excessively deep equality case is S^(h+5) A7 with six low free. Candidate B holds: free A/actual A/S visits at floor+2 spend disjoint wallets at floor+2/floor/floor+1. Hence all source-height visits<=3, so four distinct required sources are impossible in any order. No height or depth bound was imposed; the needed floor is derived from low-free3.

E729 PROVED-PAPER; no new Lean theorem. The dropped terminal-recovery version of B is REFUTED by S at T1/m-2. The broader parent remains nonempty (existing M4/free44 certificate) but PC4/free<=3 is impossible. No other failed claim or resource failure occurred. All source/free definitions are original0; the global high-free pool is unrestricted. Uniform arbitrary-rank/general M<=F_low and C1 remain CONJECTURED. No daily cycle or tracker reset is inferred. Stop this M4 unit; next M5/free4 needs a new mathematical interface, not a stopped r4/SMT/generator retry.

Actual timestamps/CPU and unused allocations are saved in FINAL_SUMMARY.json. The25-minute distinct-mechanism reservation is not reported as25 minutes of completed work. The bounded mathematical question was decided earlier; no extra search is run to fill the allocation. Preserve the unrelated docs/data/daily_research/2026-11-07.json.
