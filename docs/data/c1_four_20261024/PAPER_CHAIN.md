# H-20261024-01: frozen proposer and falsifier pass

Original base remains0. Let state have word w, total A=a, saturated S=s≤19, free A=r.
Set gap(s,j) to append S^j, saturate S at19, trim to the last19 only after saturation.
No A counter is capped. At a next A, use the exact local suffix checker and the independent
necessary old signature when S<19; retain both actual supplied and actual nonsupplied tags.

Falsifier before Lean:
- j=0 changes no signs; the root has deficit0, so an immediate A must fail the positive gate.
- j=18 preserves an exact sub-saturation state when the old S count is0.
- j=19 and20 both end in S^19 with saturated S19 and unchanged A/free counts.
- Appending a nonsupplied A after either long gap must remain a legal edge when free budget is available;
  its word is S18 A, count A+1 and free+1. Pruning it would be unsound.
- A local P2 window with10 A has length19; trimming to18 can lose it. The literal
  SSSSAAAAAASASASASAS has mass1 and area0, with no shorter P2 suffix. This controls the19 width.
- Without BlockWord, the old SSAAA | AS example invalidates the old-window count barrier.
- If the initial boundary n=b is omitted, the endpoint z=S is lost; retain the root and its S-ray.

Chain to formalize:
1. trim19(trim19(w) ++ v) = trim19(w ++ v), and arbitrary S-gap≥19 saturates exactly.
2. gap composition and the actual-S update give a representation actual=gap(member,j).
3. A≤10 comes from the member certificate invariant before the next A.
4. Local windows need at most19 prior signs; S≥19 excludes old windows by E-385.
5. At each actual A, original-base EndN supplies exactly one admitted A0/A1 edge.
6. The verified A-event graph changes only at A; all j=0..19 are checked, including root S endpoints.
7. Strong induction / representation yields all-prefix A≤10 and endpoint classification, then depth4.

The weakest new edge is full actual-word simulation through the saturated gap, not a new wrapper.
CPU exploration remains0. Kernel controls and checking Lean are validation, recorded separately.

## Certificate engineering decision,06:25

Three global-table representations were stopped on memory limits, with no mathematical predicate weakened.
The last attempt completed row0 but hit4GiB before256. A distinct source of read amplification was identified:
every child lookup expanded a record containing both the64-bit state and its560-bit outgoing edges.
The next representation separates these columns so child equality reads state bits only. Same graph/predicates,
4GiB guard and06:40 cutoff remain; no time-only extension. Failure switches to the generic terminal criterion.
These are engineering attempts, not repaired mathematical conjectures or separate research results.
