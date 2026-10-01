# Independent statement audit: E-364 / issue #76

**PASS — the fixed all-q construction has the exact requested P2, all-positive-proper-prefix minimality, overlapping SS count, and maximal terminal A-run length.** No material statement/prose mismatch or unproved hypothesis was found.

- Reviewer: independent delegated auditor, separate from the proposer/formalizer and same-session auditor; 2026-10-01.
- Worktree used for every command: `/Users/hirokidaichi/.codex/worktrees/first-p2-ending-s/recaman-lean-research`.
- Base/HEAD at opening and at the completed kernel controls: `cbe51b7b1216f9700f432eb14803277113c02af4`; the reviewed module was staged but uncommitted.
- Final snapshot at 09:19:49 UTC: HEAD `6a4350b9a02ce5cb8ef7a7f42a5ba1cca94f7e37` after the coordinating session committed the staged source. The source SHA-256 remained identical; the review did not depend on the commit message.
- Reviewed `Recaman/TerminalASharpWords.lean` SHA-256: `e7395372b0f890dbd65c47bb5612ce818d578bd5a88ae03c77a28063a0401451`.
- Hypothesis-card status read: `H-20261001-04`, `PROVED-LEAN` with independent review pending. This document supplies that independent review for #76 only. The existing card, registry, source, root, viewer and index were not edited.
- GitHub issue #76 was OPEN at the independent read. This document does not declare it closed.
- Research question: does the exact fixed construction in #76 satisfy the whole all-q claim under the existing definitions, rather than a cutoff, a changed family, or assumed minimality?
- Acceptance: read the actual definitions/proof bodies; check both directions of the prefix classification, nonzero moments, subtraction/casts, boundary cases and maximum-run meaning; independently re-elaborate with trust 0 and check the axiom set.
- Stop: 15 minutes from 09:15:20 UTC or an immediate material mismatch/counterexample. No replacement construction or orbit realization research.
- Context consulted: AGENTS.md, AI_RESEARCH_PROTOCOL.md, README.md, STATUS_REPORT_2026-08-30.md, ROADMAP.md; relevant GLOSSARY/PROOF_MAP entries; stopped/countermodel entries of RESEARCH_PORTFOLIO.md; E-361 paper section 5 and the exact #76 issue text. The same-session audit was read only as a comparison after the source had been examined; its verdict was not used as evidence.

## Definition and quantifier audit

The module imports `Recaman.OneSSMultiplicity` only. Independently traversing source imports found 29 modules including Std; `Recaman.FirstP2EndingS` (E-362) and `Recaman.TerminalASSBound` (E-363) are absent. No upper-bound result is used in the construction or its minimality proof.

`ShortPeriodicSupply.sign true=1`, `sign false=-1`; `LeadingRunSupply.mass` is the sign sum. Its recursion
`moment (b::w)=sign b + mass w + moment w` gives the 1-based weighted sum. `LeadingRunSupply.P2 w` is exactly `mass w=1 ∧ moment w=0`. `SSFreeSupply.alt false n` recursively prepends false,true, so it is exactly `(SA)^n`, in the stated newest-first order. `OneSSMultiplicity.ssCount` checks each head and its next head before recursing one position, hence overlap is counted: SSS has count 2.

The source defines precisely:
`W0=AAS`, `W1=SAAAASS`, `W2=AAASSSASASA`; for every q≥3,
`Wq=AAA S (SA)^n S^q A^(q−1)`, with `n=q*q-2*q-2` in Nat.
There is no head-A assumption; in particular the required W1 starts S.

`word_properties (q : Nat)` has no hypothesis: q=0 and q=1 have saturated q−1=0, and q=2 has terminal length 1. Its last conjunct explicitly ranges over **every** j with `0<j<length`. The complete word is not accidentally excluded, and the empty prefix is not counted. The two existential corollaries follow from this exact word and do not add evidence or an orbit claim.

## Informal dependency chain and meaning in both directions

1. The take lemmas split the explicit body into the four exhaustive regions: the first four signs; alternating pairs; the S run; the terminal A run. Equality boundary positions are included in adjacent formulas consistently.
2. `proper_mass_one_prefix` works for every q≥3 and every Nat n, not merely the chosen quadratic n. Every positive proper prefix with mass one has one of:
   - j=1, moment 1;
   - j=2i+3, 1≤i≤n, moment −i−2;
   - j=2n+5, moment −n−3.
   The initial region explicitly eliminates j=2,3,4. In the alternating region the local odd prefix has mass −1 and moment −i, giving 2−i−4=−i−2 after the four-sign head. In the first S of the final S run, the core moment n+2 and core length 2n+4 give n+2−1−(2n+4)=−n−3. In the final A run, mass one forces exactly q−1 A signs and hence the full length, contradicting properness.
3. `alt_S_prefix_at_pair` and `proper_mass_one_positions_iff` prove the reverse direction: every listed position (in the stated positive/proper domain) really has mass one. The classification is not just a candidate superset. All three moments are nonzero, including n=0. `body_minimal` consumes the two actual P2 equalities locally and concludes absence of every positive proper P2 prefix; it does not assume minimality.
4. `square_ge_twice_add_three` proves q*q≥2q+3 for q≥3. `pairCount_equation` therefore gives n≥1 and n+2q+2=q*q, with no truncated subtraction error. Casting that exact Nat equality establishes `pairCount_int`; the proof does not silently rewrite a truncated subtraction as integer subtraction.
5. Independently from minimality, the actual append/run formulas give mass 1 and
   `2*moment(body q n)=2*(q*q−2q−2−n)` in Int for q≥1. Substitution of the justified `pairCount_int` proves P2. The length formula similarly gives `2*q*q−2*q−1` for q≥3.
6. For the chosen n≥1, the initial S/first SA contributes one SS, S^q contributes q−1, and the remaining joins contribute zero. `body_ssCount` proves exact q with overlap. `terminal_S_A_length` reverses the word and takes true signs until a genuine false in S^q; this certifies the **maximal** terminal run, not an arbitrarily selected A suffix.
7. q=0,1,2 are separately proved by finite `decide` and a range-all control. An arbitrary proper j is put into `List.range length` and the all-check is applied to it. General q≥3 uses induction/classification, not a finite enumeration.

Thus informal → formal preserves the specified words, orientation, all-q quantifier and full minimality. Formal → informal gives exactly the claimed P2/count/maximum-tail properties, without a cutoff or hidden defined Prop. The substantive new frontier is the explicit family plus complete proper-prefix analysis, not its arithmetic helpers or final wrappers.

## Exact source signatures

The following signatures are copied verbatim from the reviewed source, stopping before the proof body. The first nine are exactly the E-364 registry citations. Four extra signatures pin the minimality and subtraction obligations.

### Recaman.TerminalASharpWords.proper_mass_one_prefix

```lean
theorem proper_mass_one_prefix (q n j : Nat) (hq : 3 ≤ q)
    (hj : 0 < j) (hlen : j < (body q n).length)
    (hm : mass ((body q n).take j) = 1) :
    (j = 1 ∧ moment ((body q n).take j) = 1) ∨
    (∃ i, 1 ≤ i ∧ i ≤ n ∧ j = 2 * i + 3 ∧
      moment ((body q n).take j) = -(i : Int) - 2) ∨
    (j = 2 * n + 5 ∧ moment ((body q n).take j) = -(n : Int) - 3)
```

### Recaman.TerminalASharpWords.proper_mass_one_positions_iff

```lean
theorem proper_mass_one_positions_iff (q n j : Nat) (hq : 3 ≤ q)
    (hj : 0 < j) (hlen : j < (body q n).length) :
    mass ((body q n).take j) = 1 ↔
      j = 1 ∨ (∃ i, 1 ≤ i ∧ i ≤ n ∧ j = 2 * i + 3) ∨ j = 2 * n + 5
```

### Recaman.TerminalASharpWords.body_P2

```lean
theorem body_P2 (q : Nat) (hq : 3 ≤ q) : P2 (body q (pairCount q))
```

### Recaman.TerminalASharpWords.body_ssCount

```lean
theorem body_ssCount (q n : Nat) (hq : 1 ≤ q) (hn : 1 ≤ n) : ssCount (body q n) = q
```

### Recaman.TerminalASharpWords.body_sharp_length

```lean
theorem body_sharp_length (q : Nat) (hq : 3 ≤ q) :
    (body q (pairCount q)).length = 2 * q * q - 2 * q - 1
```

### Recaman.TerminalASharpWords.body_terminal_length

```lean
theorem body_terminal_length (q n : Nat) (hq : 1 ≤ q) :
    ((body q n).reverse.takeWhile id).length = q - 1
```

### Recaman.TerminalASharpWords.word_properties

```lean
theorem word_properties (q : Nat) :
    P2 (word q) ∧ ssCount (word q) = q ∧
      ((word q).reverse.takeWhile id).length = q - 1 ∧
      (∀ j, 0 < j → j < (word q).length → ¬ P2 ((word q).take j))
```

### Recaman.TerminalASharpWords.exists_minimal_p2_with_terminal_length

```lean
theorem exists_minimal_p2_with_terminal_length (q : Nat) :
    ∃ w : List Bool, P2 w ∧ ssCount w = q ∧
      (w.reverse.takeWhile id).length = q - 1 ∧
      (∀ j, 0 < j → j < w.length → ¬ P2 (w.take j))
```

### Recaman.TerminalASharpWords.exists_minimal_p2_terminal_run

```lean
theorem exists_minimal_p2_terminal_run (t : Nat) :
    ∃ w : List Bool, P2 w ∧ ssCount w = t + 1 ∧
      (w.reverse.takeWhile id).length = t ∧
      (∀ j, 0 < j → j < w.length → ¬ P2 (w.take j))
```

### Recaman.TerminalASharpWords.body_minimal

```lean
theorem body_minimal (q n : Nat) (hq : 3 ≤ q) :
    ∀ j, 0 < j → j < (body q n).length → ¬ P2 ((body q n).take j)
```

### Recaman.TerminalASharpWords.square_ge_twice_add_three

```lean
theorem square_ge_twice_add_three (q : Nat) (hq : 3 ≤ q) : 2 * q + 3 ≤ q * q
```

### Recaman.TerminalASharpWords.pairCount_equation

```lean
theorem pairCount_equation (q : Nat) (hq : 3 ≤ q) :
    1 ≤ pairCount q ∧ pairCount q + 2 * q + 2 = q * q
```

### Recaman.TerminalASharpWords.pairCount_int

```lean
theorem pairCount_int (q : Nat) (hq : 3 ≤ q) :
    (pairCount q : Int) = (q : Int) * q - 2 * q - 2
```

## G5 binder/hypothesis/wrapper answers

- `proper_mass_one_prefix`: actual constructed take-prefix occurs in its range and mass hypotheses; no defined obstruction or conclusion hypothesis; substantive classification.
- `proper_mass_one_positions_iff`: actual constructed take-prefix occurs in its proper-range hypothesis/conclusion; no assumed mass-one property on the reverse direction; substantive bidirectional classification.
- `body_P2`, `body_sharp_length`, `body_terminal_length`, `word_properties`: outer binders are Nat only, while the conclusions evaluate an explicitly defined Bool word. No obstruction/minimality/P2 hypothesis is supplied. These are derived properties/assembly, counted W for novelty.
- `body_ssCount`: outer binders are Nat only; the conclusion computes the actual body list. q≥1 and n≥1 are checked numeric domain premises, not the count itself. The SS junction proof is substantive.
- The existence corollaries quantify a concrete `List Bool` existentially but their proofs merely choose the already-proved word (or q=t+1). They are W.
- Extra `body_minimal`: q≥3 is its only hypothesis; the full j/minimality statement is its conclusion. The subtraction helpers have no mathematical obstruction assumption but are arithmetic support, not independent novelty.

No cited theorem assumes its conclusion or a conjunct of it, an unproved defined Prop, a length cutoff, a matching, a phase restriction, canonical history, or seeded orbit realization.

## Conservative R/W/C/T assessment

Here R means a new structural/formula theorem about actual constructed words, W includes arithmetic/elementary helpers and derived wrappers, C means an unproved key obstacle premise, T means a vacuous equality/conclusion-as-premise. Routine arithmetic helpers are deliberately not counted as research novelty. The heuristic lint's 25 substantive labels are not this manual judgment.

| Declaration | Class | Reason |
|---|---|---|
| mass_replicate_S | W | Elementary constant-run arithmetic |
| twice_moment_replicate_S | W | Elementary triangular-sum helper |
| alt_S_negative_prefix | R | Inductive full classification of odd SA prefixes with exact moment |
| head_mass | W | Fixed finite evaluation |
| head_moment | W | Fixed finite evaluation |
| core_mass | W | Imported append/alt formula arithmetic |
| core_moment | W | Imported append/alt formula arithmetic |
| body_length | W | Elementary append length helper |
| body_mass | W | Derived run sum |
| body_twice_moment | R | Exact moment formula for the actual whole body with arbitrary q,n |
| take_body_alt | R | Actual bounded take decomposition in the alternating region |
| take_body_S | R | Actual bounded take decomposition in the S region |
| take_body_A | R | Actual bounded take decomposition in the A region |
| proper_mass_one_prefix | R | Exhaustive proper-prefix classification and exact moments |
| body_minimal | W | Consequence of the new classification, not independent novelty |
| alt_S_prefix_at_pair | R | Realization of every pair candidate with exact moment |
| proper_mass_one_positions_iff | R | Both directions, including realization |
| square_ge_twice_add_three | W | Pure arithmetic helper, not word novelty |
| pairCount_equation | W | Saturated subtraction arithmetic helper |
| pairCount_int | W | Arithmetic cast helper |
| body_P2 | W | Instantiates the actual formulas at the checked quadratic n |
| body_sharp_length | W | Length and quadratic substitution |
| ssCount_replicate_A | W | Elementary constant-run count |
| ssCount_S_then_A | W | Elementary run helper |
| body_ssCount | R | Actual initial/tail SS junction calculation |
| terminal_S_A_length | R | Exact reverse/takeWhile stops at genuine S |
| body_terminal_length | W | Specialization of terminal_S_A_length |
| small_word_properties | R | Kernel-checked exact boundary words and all proper prefixes |
| word_properties | W | Assembly of the exact small/general family results |
| exists_minimal_p2_with_terminal_length | W | Chooses word q |
| exists_minimal_p2_terminal_run | W | Reindexes the preceding existence theorem |

Manual totals: **R/W/C/T = 11/20/0/0**. These are not 11 independent advances: the unit is the single fixed construction. No C/T content is required to obtain the advertised theorem.

## Independent commands and kernel evidence

All commands below were run from the stated worktree; no primary-checkout dirty source was read.

```sh
gh issue view 76 --json title,body,state,url
python3 scripts/report_vacuity.py --all Recaman/TerminalASharpWords.lean
python3 scripts/harness_gate.py --lint-module Recaman/TerminalASharpWords.lean
lake env lean Recaman/TerminalASharpWords.lean
lake env lean -t 0 Recaman/TerminalASharpWords.lean
./scripts/check.sh
shasum -a 256 Recaman/TerminalASharpWords.lean
```

Results: source elaboration exit 0, including trust 0; vacuity 2/31 flagged (`square_ge_twice_add_three`, `pairCount_int`), both acknowledged arithmetic helpers; lint 25/31 heuristic substantive. The independent full check passed: root reaches 390/390 modules, 110 direct-import contracts, 363 registry entries, 157 PROVED-LEAN rows linked to Audit, G1–G5 13 rows E-344+, protected claims intact, **393 build jobs and 2600 audited declarations**. All audited axioms were inside `{propext, Classical.choice, Quot.sound}`. No prohibited proof escapes were found.

The independent controls were executed without creating another file:

```sh
lake env lean -t 0 --stdin <<'LEAN'
import Recaman.TerminalASharpWords
open Recaman.TerminalASharpWords Recaman.LeadingRunSupply Recaman.OneSSMultiplicity
local instance (w : List Bool) : Decidable (P2 w) :=
  inferInstanceAs (Decidable (mass w = 1 ∧ moment w = 0))
example : word 0 = [true,true,false] := by decide
example : word 1 = [false,true,true,true,true,false,false] := by decide
example : word 2 = [true,true,true,false,false,false,true,false,true,false,true] := by decide
example : pairCount 3 = 1 ∧ (word 3).length = 11 ∧
    ((word 3).reverse.takeWhile id).length = 2 := by decide
example : word 3 = [true,true,true,false,false,true,false,false,false,true,true] := by decide
example : ((List.range 11).filter fun j =>
    decide (0 < j ∧ mass ((word 3).take j) = 1)) = [1,5,7] := by decide
example : moment ((word 3).take 1) = 1 ∧
    moment ((word 3).take 5) = -3 ∧ moment ((word 3).take 7) = -4 := by decide
example : ¬ P2 (body 0 (pairCount 0)) ∧
    ¬ P2 (body 1 (pairCount 1)) ∧ ¬ P2 (body 2 (pairCount 2)) := by decide
example : ssCount [false,false,false] = 2 := by decide
example : ssCount (body 3 0) = 3 ∧ ¬ P2 (body 3 0) ∧ ¬ P2 (body 3 2) := by decide
example (q : Nat) (hq : 3 ≤ q) :
    word q = ([true,true,true,false] ++ Recaman.SSFreeSupply.alt false (q*q-2*q-2)) ++
      (List.replicate q false ++ List.replicate (q-1) true) := by
  simp only [word, if_pos hq, body, pairCount]
example (q : Nat) : ∃ w : List Bool, P2 w ∧ ssCount w = q ∧
    (w.reverse.takeWhile id).length = q-1 ∧
    (∀ j, 0<j → j<w.length → ¬ P2 (w.take j)) :=
  exists_minimal_p2_with_terminal_length q
#print axioms Recaman.TerminalASharpWords.proper_mass_one_prefix
#print axioms Recaman.TerminalASharpWords.proper_mass_one_positions_iff
#print axioms Recaman.TerminalASharpWords.body_minimal
#print axioms Recaman.TerminalASharpWords.pairCount_equation
#print axioms Recaman.TerminalASharpWords.pairCount_int
#print axioms Recaman.TerminalASharpWords.body_P2
#print axioms Recaman.TerminalASharpWords.body_ssCount
#print axioms Recaman.TerminalASharpWords.word_properties
#print axioms Recaman.TerminalASharpWords.exists_minimal_p2_with_terminal_length
#print axioms Recaman.TerminalASharpWords.exists_minimal_p2_terminal_run
LEAN
```

Final control exit: 0. Exact axiom output:

```text
'Recaman.TerminalASharpWords.proper_mass_one_prefix' depends on axioms: [propext, Classical.choice, Quot.sound]
'Recaman.TerminalASharpWords.proper_mass_one_positions_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Recaman.TerminalASharpWords.body_minimal' depends on axioms: [propext, Classical.choice, Quot.sound]
'Recaman.TerminalASharpWords.pairCount_equation' depends on axioms: [propext, Classical.choice, Quot.sound]
'Recaman.TerminalASharpWords.pairCount_int' depends on axioms: [propext, Classical.choice, Quot.sound]
'Recaman.TerminalASharpWords.body_P2' depends on axioms: [propext, Classical.choice, Quot.sound]
'Recaman.TerminalASharpWords.body_ssCount' depends on axioms: [propext, Quot.sound]
'Recaman.TerminalASharpWords.word_properties' depends on axioms: [propext, Classical.choice, Quot.sound]
'Recaman.TerminalASharpWords.exists_minimal_p2_with_terminal_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Recaman.TerminalASharpWords.exists_minimal_p2_terminal_run' depends on axioms: [propext, Classical.choice, Quot.sound]
```

This verifies the imported proof objects with trust 0 in addition to re-elaborating the actual source. The finite `decide` controls are kernel checks, not `native_decide`; they do not establish the infinite family.

## Independent falsifier and counterfactuals

**COMPUTED** semantic regression: all q=0..100 and all arbitrary bodies with q=3..12,n=0..16. This reuses the pre-existing q=0..40 range; q=41..100 is an additional audit check, not advertised as a new discovery-free holdout. The whole-word and every proper-prefix scan below is linear in word length and independent of the repository's experiment script. Computation is not the general proof.

```sh
python3 - <<'PY'
from pathlib import Path
import hashlib, json
src=Path('Recaman/TerminalASharpWords.lean').read_bytes()
def body(q,n): return [1,1,1,-1]+[-1,1]*n+[-1]*q+[1]*max(q-1,0)
def word(q):
    if q==0: return [1,1,-1]
    if q==1: return [-1,1,1,1,1,-1,-1]
    if q==2: return [1,1,1,-1,-1,-1,1,-1,1,-1,1]
    return body(q,q*q-2*q-2)
def stats(w):
    H=M=0; visits=[]; p2=[]
    for j,e in enumerate(w,1):
        H+=e; M+=j*e
        if j<len(w) and H==1: visits.append([j,M])
        if H==1 and M==0: p2.append(j)
    t=0
    for e in reversed(w):
        if e!=1: break
        t+=1
    return {'length':len(w),'mass':H,'moment':M,'ss':sum(a==b==-1 for a,b in zip(w,w[1:])),'tail':t,'visits':visits,'p2':p2}
for q in range(101):
    s=stats(word(q))
    assert (s['mass'],s['moment'],s['ss'],s['tail'],s['p2'])==(1,0,q,max(q-1,0),[s['length']]), (q,s)
    if q>=3:
        n=q*q-2*q-2
        expected=[[1,1]]+[[2*i+3,-i-2] for i in range(1,n+1)]+[[2*n+5,-n-3]]
        assert s['visits']==expected, (q,s['visits'],expected)
        assert s['length']==2*q*q-2*q-1
for q in range(3,13):
    for n in range(17):
        s=stats(body(q,n))
        assert s['visits']==[[1,1]]+[[2*i+3,-i-2] for i in range(1,n+1)]+[[2*n+5,-n-3]]
        assert s['moment']==q*q-2*q-2-n
        assert s['ss']==q
        assert all(m!=0 for _,m in s['visits'])
print(json.dumps({'source_sha256':hashlib.sha256(src).hexdigest(),'all_q_range':[0,100],'arbitrary_body_q_range':[3,12],'arbitrary_n_range':[0,16],'failures':0,'q3':stats(word(3)),'general_small_controls':{str(q):stats(body(q,max(max(q*q-2*q,0)-2,0))) for q in range(3)},'wrong_n_q3':{str(n):stats(body(3,n)) for n in [0,2]}},sort_keys=True))
PY
```

Exact output:

```json
{"all_q_range": [0, 100], "arbitrary_body_q_range": [3, 12], "arbitrary_n_range": [0, 16], "failures": 0, "general_small_controls": {"0": {"length": 4, "mass": 2, "moment": 2, "p2": [], "ss": 0, "tail": 0, "visits": [[1, 1]]}, "1": {"length": 5, "mass": 1, "moment": -3, "p2": [], "ss": 1, "tail": 0, "visits": [[1, 1]]}, "2": {"length": 7, "mass": 1, "moment": -2, "p2": [], "ss": 2, "tail": 1, "visits": [[1, 1], [5, -3]]}}, "q3": {"length": 11, "mass": 1, "moment": 0, "p2": [11], "ss": 3, "tail": 2, "visits": [[1, 1], [5, -3], [7, -4]]}, "source_sha256": "e7395372b0f890dbd65c47bb5612ce818d578bd5a88ae03c77a28063a0401451", "wrong_n_q3": {"0": {"length": 9, "mass": 1, "moment": 1, "p2": [], "ss": 3, "tail": 2, "visits": [[1, 1], [5, -3]]}, "2": {"length": 13, "mass": 1, "moment": -1, "p2": [], "ss": 3, "tail": 2, "visits": [[1, 1], [5, -3], [7, -4], [9, -5]]}}}
```

- q=3 is exactly `AAASSASSSAA`: n=1, length 11, mass 1, moment 0, SS=3, maximum tail 2. Proper mass-one visits are precisely (1,1),(5,−3),(7,−4), and P2 occurs only at 11. q=2 is a different length-11 word with SS=2 and tail 1.
- Forcing q=0,1,2 into the general body gives (mass,moment)=(2,2),(1,−3),(1,−2); all fail P2. The explicit small branch is necessary.
- For q=3 with n=0 or n=2, moment is respectively 1 or −1, so a wrong pair count fails P2 even though mass=1, SS=3 and tail=2 still hold. This distinguishes true P2 from a mass/count-only weakening.
- n=0 is a useful trap: removing the SA part **does not** lower SS to q−1. The initial S joins S^q, producing S^(q+1), with SS count q. The distinct initial S/SA junction explanation only applies when n≥1. The production theorem uses the proved n≥1 and is correct.
- Initial audit controls failed first because P2's decidability instance in the module is local and was not exported. Adding a local instance that unfolds the established P2 conjunction fixed this harness issue.
- The next control tested the auditor's incorrect n=0 count q−1; Lean rejected it and the independent Python assertion also failed. Reading the merged S run corrected the audit control to SS=q. This was an auditor-side failed guess, not a source counterexample, and no production statement was repaired.
- There is no history premise to weaken: the objects are abstract finite Bool words. No canonical/seeded orbit occurrence, owner delta, Hall result, T6 or general #73 claim is inferred.

## Decision and remaining uncertainty

The #76 independent semantic acceptance test passes on the reviewed source hash. Retain E-364's local `PROVED-LEAN` construction claim; the next action is for the coordinating session to record the independent-review status and handle its already-authorized handoff. This reviewer does not modify issue state, registry labels or the existing card.

No mathematical uncertainty remains for the advertised abstract-word construction. Orbit realization and any owner/Hall consequence remain outside this unit and are unproved here. The upper-bound E-363 requires its own independent review before a combined claim is accepted. Stop this construction/review unit; further enumeration or wrapper lemmas would not strengthen the result.

Final document verification: all 13 quoted signatures match the source verbatim; manual table counts are 11 R and 20 W. The source hash was rechecked after the coordinator's commit. Completion was inside the 15-minute gate.

Only new file written by this reviewer: `docs/statement_audits/E-364-independent.md`. No commit, push, GitHub comment, additional subagent, index change or other source/document edit was performed.
