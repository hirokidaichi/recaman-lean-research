# H-20261105-29: actual unit-mass old target accounting

- Status: PROVED-LEAN (E575; arbitrary mixed tail and originalp); 07:13:54 semantic audit follow-up.
- Question: for arbitrary f:Nat→Bool, original base0, n,B,j,t:Nat witht<=n, positive actual count ONLY at endpoint n+B, S gap lengthj, same actual target Win startingt and old suffixmass1, does j+1<=actual free acrossB follow without BlockWord/headmass/run-count/source assumptions?
- Exact domain: mass(seg f t(n-t))=1; cN(EndN f0)nB+1<=cN(S)nB; gapallS and Win f t(n+B+j-t). No free/headfree conclusion or defined Prop input. B0 is impossible underendpointpositive and is not silently omitted.
- Chain: reconstruct target word as oldsuffix++mixedtail++S^j; itsmass1 andoldmass1 givemass(mixedtail)=j. Originalactual partition and endpointpositive givemass(mixedtail)+1<=free. OriginalIntp adapter derives endpointrelativepositivity fromoriginalzero atn andpositive atn+B; same P2/Endable basep, no reset.
- Falsifier: B0 endpointpositive is false; j0 stillneedsactualpositive toforcefree1; if dropzero atn, absolutepositive doesnotautomatically implyrelativepositive. If oldmassC>1, accounting givesonly j+2-C, notfullgap. For t=n oldsuffixempty hasmass0, incompatiblewith1. P2area is strongerthanrequired; do notclaim anarea-based source elimination.
- Acceptance: kernel -j1-M512/currentbytes; exactG5; existing mass1 narrower outputs explicitlymarked accounting-subsumed ratherthannewindependentC1 edges. Newclaim covers allmixedtails/allrun counts onlythis oldmass1target, notgeneralC1.
- Stop: one mathrepair; resourcefailurequarantine withnocap/tactic/importretry; before07:45 stopnewmath. Workerbudget0.

Preformalization extension: retain arbitrary Nat C and prove free+C>=j+2, then mass1 fullgap and actualcounter C>=2 as bookkeeping corollaries. This is a general actual count identity, not a new source-collision edge.

Final review: exact time/CPU/publication values are in RESEARCH_HANDOFF_2026-11-05_DAILY.md and docs/data/daily_research/2026-11-05.json; no planned/open interval credited.
