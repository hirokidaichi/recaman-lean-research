# E-362 independent semantic audit — issue #74

**PASS.** The current source proves the all-length issue #74 statement and its
least-positive-P2-prefix corollary with the intended word semantics. No added
unproved hypothesis, earlier-moment positivity assumption, length cutoff,
or prohibited proof mechanism was found.

This is a separate-session review by the independently delegated #74 auditor.
The existing same-session E-362 audit was not used as the answer. The issue,
definitions, complete proof bodies, boundary controls and kernel checks were
examined independently. Only this new Markdown file was written; no Lean
source, card, registry, root import, viewer, index, branch or GitHub state was
changed by this auditor. Existing staged #76 work was left untouched.

## Bounded question and acceptance gate

Question: does `Recaman/FirstP2EndingS.lean` prove exactly issue #74 for every
finite newest-first Bool word, including a genuinely least positive prefix,
without extra assumptions or finite cutoffs?

Acceptance: compare issue/card/paper quantifiers to source in both semantic
directions; inspect the underlying mass/moment/P2 definitions and all proof
bodies; reproduce small and weakened controls; verify actual Lean elaboration,
permitted axioms and lint; give PASS or an actionable semantic finding.
Stop: 15 minutes or the first major semantic discrepancy. No conjecture repair
or work on #73/#75/#76 was authorized in this audit.

Card reviewed: `H-20261001-02`,
`docs/HYPOTHESIS_CARD_2026-10-01_FIRST_P2_ENDING_S.md`, status `PROVED-LEAN`
(E-362). This independent PASS supplies its separate-session review requirement;
the card itself was not edited. Issue #74 was OPEN when queried and remains
OPEN in this document. This audit makes no GitHub closure claim.

## Source identity and context

Workdir for every shell command:
`/Users/hirokidaichi/.codex/worktrees/first-p2-ending-s/recaman-lean-research`.
Initial HEAD: `cbe51b7b1216f9700f432eb14803277113c02af4`.
Other-session staged #76 changes were present; the target #74 module had no
staged or unstaged diff. The audit is pinned to these SHA-256 digests, even if
HEAD later moves for the parent's #76 commit:

```text
Recaman/FirstP2EndingS.lean 9c07e5131aedcc7e4ce547d945e9a8ed7683ce1c3e01aae44d4213665bb4b439
Recaman/LeadingRunSupply.lean 0aff15293c82c92897c1715a6331ddc3624241f53227983eecd8409d9910ad4c
Recaman/ShortPeriodicSupply.lean d6f89f0fedbe89057157dc56ad8dce2409a2a12abae085846871e24f1966763e
```

Reviewed context: `AGENTS.md`, `docs/AI_RESEARCH_PROTOCOL.md`, `README.md`,
`docs/STATUS_REPORT_2026-08-30.md`, `docs/ROADMAP.md`; the relevant glossary
backward-word/P2/low-SS entries; proof-map E-128/E-130/E-361/E-362; portfolio
stopped charging, finite-lag and SS2 prefix-normalization routes; the existing
hypothesis card and paper section 3. In particular, E-130 already refutes an
unrestricted SS2 S-ended normalization. This result avoids that overclaim by
explicitly consuming ceiling two. It does not resolve Hall, owner maps,
periodicity, general #73, or either surjectivity alternative.

Issue read with `gh issue view 74 --json number,title,state,body,url`:
[issue #74](https://github.com/hirokidaichi/recaman-lean-research/issues/74).
The issue requests precisely the minimal-word theorem and the first-P2
corollary, using `LeadingRunSupply` definitions, without an orbit restriction.

## Exact source signatures

These quotations are copied from the inspected source. Its namespace is
`Recaman.FirstP2EndingS`, with `open LeadingRunSupply` and
`open ShortPeriodicSupply (sign)`.

```lean
theorem defect_append_sign (w : List Bool) (b : Bool) :
    defect (w ++ [b]) = defect w + 1 - mass w
```

```lean
theorem defect_pos_before_p2 (w : List Bool) (hne : w ≠ [])
    (hceil : ∀ j, j ≤ w.length → mass (w.take j) ≤ 2)
    (hno : ∀ j, 0 < j → j ≤ w.length → ¬ P2 (w.take j)) :
    0 < defect w
```

```lean
theorem minimal_p2_ends_S (w : List Bool) (hp : P2 w)
    (hmin : ∀ j, 0 < j → j < w.length → ¬ P2 (w.take j))
    (hceil : ∀ j, j ≤ w.length → mass (w.take j) ≤ 2) :
    ∃ u, w = u ++ [false]
```

```lean
theorem first_p2_prefix_ends_S (w : List Bool)
    (hceil : ∀ j, j ≤ w.length → mass (w.take j) ≤ 2)
    (hex : ∃ j, 0 < j ∧ j ≤ w.length ∧ P2 (w.take j)) :
    ∃ j, 0 < j ∧ j ≤ w.length ∧ P2 (w.take j) ∧
      (∀ k, 0 < k → k < j → ¬ P2 (w.take k)) ∧
      ∃ u, w.take j = u ++ [false]
```

## Definition and quantifier audit

`ShortPeriodicSupply.sign true = 1`, `sign false = -1`.
`LeadingRunSupply.mass w = (w.map sign).sum : Int`.
The recursion `moment [] = 0` and
`moment (b :: w) = sign b + mass w + moment w` gives the one-based weighted
sum `sum_{i=1}^L i*sign(w_i)`: prepending a sign shifts every remaining weight
by one. Thus this is the same backward moment as the issue, paper and periodic
P2 sum, rather than an unweighted or reversed moment. `P2 w` unfolds exactly
to `mass w = 1 ∧ moment w = 0`. All mass arithmetic is integer arithmetic;
there is no saturated subtraction of negative mass.

| Check | Result |
|---|---|
| Concrete object in binders | Yes: `w : List Bool`, actual `take` prefixes; no actual-orbit restriction is needed. |
| All lengths | Yes: unrestricted `w`, unrestricted Nat indices; the proof recurses on `w.length`, not a bounded census. |
| Minimality | Exactly every positive proper prefix: `0 < j → j < w.length → ¬ P2 (w.take j)`. |
| Ceiling | Every Nat index from 0 through the complete length: `j ≤ w.length`; Nat supplies `0 ≤ j`. |
| Added unproved defined Prop | None. `P2` is the explicitly requested, unfolded pair of equalities, not a newly assumed obstruction. |
| Conclusion among hypotheses | No; neither `w = u ++ [false]` nor existence of an S-ended P2 prefix is a premise. |
| Moment positivity premise | None. The derived invariant is D positivity before P2, not an assumption that all earlier moments are positive. |
| Leastness in corollary | Returned for the same output `j` with `P2 (w.take j)` and its S endpoint. |
| S/endpoint direction | `u ++ [false]` is the list's final/oldest sign under newest-first order. |
| Additional hidden word restriction | None: no NoSAAS, SS count, current-A, periodicity, reachability or history premise. |

Informal-to-formal: any word satisfying the issue's three premises supplies
`hp`, `hmin`, `hceil` directly; its terminal S means exactly the returned
append decomposition. For the first-prefix statement the existence witness is
explicitly positive and at most the length, so it supplies `hex` directly.

Formal-to-informal: all three main premises are the issue's concrete
conditions; the conclusion is exactly an S final sign. The corollary returns a
positive P2 index within the word and rejects every positive smaller index,
so it is the first one, including when the whole word is nonminimal.
This compares the representations in both directions; it does not assert the
false converse that an S-ending word must itself be P2.

## Independent proof-body audit

Let `D(w)=moment w-length(w)*(mass w-1)`. Existing append identities imply
`D(w++[b])=D(w)+1-mass w`, for either sign. A singleton has D=1.

For `defect_pos_before_p2`, the recursive predecessor inherits the ceiling and
no-P2 conditions by actual `take_append_of_le_length` equalities. If the final
sign is A, the complete-word ceiling forces predecessor mass at most 1, so D
cannot decrease. If it is S, predecessor mass at most 1 gives the same result;
at mass 2 the change is exactly -1. The induction hypothesis gives D≥1,
hence new D≥0. Equality would mean new mass 1 and moment 0, a P2 prefix at the
complete length, excluded by `hno`. The termination measure strictly reduces
the actual word length. There is no circular use of the desired endpoint.

For `minimal_p2_ends_S`, the empty word is rejected by P2. If its terminal
sign were A, its predecessor must be nonempty (A alone has moment 1) and has
mass 0 because the full P2 mass is 1. All predecessor positive prefixes are
proper full-word prefixes, so the invariant applies. Appending A increases D
by 1, contradicting full P2's D=0. The S branch returns the decomposition.

For `first_p2_prefix_ends_S`, strong induction first selects a least positive
P2 index below the supplied witness. It does not select an arbitrary S-ended
witness. `take j` has length j because j≤length(w); `take_take` transports the
original leastness and ceiling without dropping boundary indices. Applying
the main theorem then provides the S endpoint for that same least index.

## Counterfactuals and boundary cases

All examples below were recomputed from literal signs, independently of the
existing experiment output. They were also checked through Lean's concrete
`mass`, `moment`, `P2` and `defect` definitions with kernel `decide` controls.

| Word | Prefix ceiling | Positive P2 indices | Consequence |
|---|---:|---|---|
| empty | 0 | none | Cannot supply `hex`; D=0 makes helper nonemptiness necessary. |
| A | 1 | none | Mass 1 alone is insufficient; moment=1. |
| ASSA | 1 | none | No positive P2 prefix, even though full moment=0 (mass=0). |
| AAS | 2 | 3 | Main premises are inhabited; first P2 ends S. Full D=0 shows helper `hno` must include the full word. |
| AASASSA | 2 | 3, 7 | Full word P2 and A-ended; removing minimality is REFUTED. Main theorem rejects j=3; corollary returns the length-3 S-ended first prefix. |
| AAASSSASASA | 3 | 11 | Minimal P2 and A-ended; raising the ceiling to 3 is REFUTED. Original ceiling fails at j=3. |

In `ASS`, the moment is -4 while D=2>0; Lean checked this equality and
inequality. This confirms that the invariant does not smuggle positive
earlier moments into the proof. In `AASASSA`, D at prefix 5 is -1;
positivity is only before any P2, exactly as the helper states.

Independent exact arithmetic output:

```text
''       heights=[0] moments=[0] P2=[] D=[0]
A        heights=[0,1] moments=[0,1] P2=[] D=[0,1]
ASSA     heights=[0,1,0,-1,0] moments=[0,1,-1,-4,0] P2=[] D=[0,1,1,2,4]
AAS      heights=[0,1,2,1] moments=[0,1,3,0] P2=[3] D=[0,1,1,0]
AASASSA  heights=[0,1,2,1,2,1,0,1] moments=[0,1,3,0,4,-1,-7,0] P2=[3,7] D=[0,1,1,0,0,-1,-1,0]
AAASSSASASA heights=[0,1,2,3,2,1,0,1,0,1,0,1] moments=[0,1,3,6,2,-3,-9,-2,-10,-1,-11,0] P2=[11] D=[0,1,1,0,-2,-3,-3,-2,-2,-1,-1,0]
```

`COMPUTED`: independent exhaustive reproduction over lengths 0..11 and
12..16, using literal one-based integer sums, gave:

```text
0..11:  words=4095,   ceiling2=2638,  withP2=298,  first_end_violation=0, defect_violation=0
12..16: words=126976, ceiling2=70290, withP2=7442, first_end_violation=0, defect_violation=0
```

These are reruns of already used ranges, not a new holdout or an all-length
proof. The all-length evidence is the inspected Lean proof.

## R/W/C/T and harness results

R = concrete mathematical content; W = reused wrapper/helper;
C = conditional scaffold assuming the sought obstruction; T = tautology.

| Declaration | Class | Independent reason |
|---|---|---|
| defect_append_sign | W | Useful algebraic append identity over imported mass/moment identities. |
| defect_pos_before_p2 | R | Inductively derived strict invariant on the concrete prefix class. |
| minimal_p2_ends_S | R | Actual terminal-sign classification proved using that invariant. |
| first_p2_prefix_ends_S | R | Constructs and retains the first index, transporting real prefix constraints. |

Conservative totals **R/W/C/T = 3/1/0/0**. Expected hypotheses specifying the
issue's word class are not an assumed sought endpoint or a new unresolved
obstruction. `report_vacuity.py` reported 4 theorems, 0 flagged, 0 fully flagged
modules. Harness lint reported 3/4 substantive declarations. No `sorry`,
`admit`, `native_decide`, custom axiom or unsafe declaration was found in the
target module or existing semantic-control source.

## Commands and strongest verification

All completed with exit 0 unless explicitly described as a no-match scan:

```sh
gh issue view 74 --json number,title,state,body,url
git rev-parse HEAD
git status -s
git diff -- Recaman/FirstP2EndingS.lean
git diff --cached -- Recaman/FirstP2EndingS.lean
python3 scripts/report_vacuity.py --module Recaman/FirstP2EndingS.lean
python3 scripts/harness_gate.py --lint-module Recaman/FirstP2EndingS.lean
lake env lean Recaman/FirstP2EndingS.lean
lake env lean -t 0 Recaman/FirstP2EndingS.lean
lake build Recaman.FirstP2EndingS
lake env lean docs/data/first_p2_ending_s_20261001/semantic_controls.lean
lake env lean --stdin < [independent control block below]
```

Source scans used `rg -n '\bsorry\b|\badmit\b|native_decide|^axiom|unsafe'`
on the target and existing controls and returned no matches. The targeted
build completed 4 jobs. Direct source elaboration with trust level 0 passed.
Independent controls below passed; `#print axioms` for all four declarations
returned exactly `[propext, Classical.choice, Quot.sound]`, with no `sorryAx`
or custom axiom. `Recaman/Audit.lean` already prints all four at lines
2689–2692, verified by source read. No Lean source changes were made, so this
auditor did not rerun the entire repository check; the parent's integration
check is separate from this scoped semantic audit. Existing check logs were
not substituted for the fresh targeted checks above.

## Independent kernel controls (reproduce via `lake env lean --stdin`)

```lean
import Recaman.FirstP2EndingS
open Recaman.LeadingRunSupply Recaman.FirstP2EndingS
namespace IndependentIssue74Controls
local instance (w : List Bool) : Decidable (P2 w) :=
  inferInstanceAs (Decidable (mass w = 1 ∧ moment w = 0))
def w7 : List Bool := [true,true,false,true,false,false,true]
def w11 : List Bool := [true,true,true,false,false,false,true,false,true,false,true]
example : P2 w7 ∧ P2 (w7.take 3) := by decide
example : ∀ j, j ≤ w7.length → mass (w7.take j) ≤ 2 := by
  intro j hj
  have hall : ∀ k : Fin 8, mass (w7.take k.val) ≤ 2 := by decide
  exact hall ⟨j, by simp [w7] at hj; omega⟩
example : ¬ ∃ u, w7 = u ++ [false] := by
  rintro ⟨u, hu⟩
  have hr := congrArg List.reverse hu
  simp [w7] at hr
example : P2 w11 := by decide
example : ∀ j, 0 < j → j < w11.length → ¬ P2 (w11.take j) := by
  intro j hj hjlen
  have hall : ∀ k : Fin 11, 0 < k.val → ¬ P2 (w11.take k.val) := by decide
  exact hall ⟨j, by simpa [w11] using hjlen⟩ hj
example : ∀ j, j ≤ w11.length → mass (w11.take j) ≤ 3 := by
  intro j hj
  have hall : ∀ k : Fin 12, mass (w11.take k.val) ≤ 3 := by decide
  exact hall ⟨j, by simp [w11] at hj; omega⟩
example : mass (w11.take 3) = 3 := by decide
example : ¬ ∃ u, w11 = u ++ [false] := by
  rintro ⟨u, hu⟩
  have hr := congrArg List.reverse hu
  simp [w11] at hr
example : ∀ j : Fin 1, ¬ P2 (([] : List Bool).take j.val) := by decide
example : ∀ j : Fin 2, ¬ P2 ([true].take j.val) := by decide
example : ∀ j : Fin 5, ¬ P2 ([true,false,false,true].take j.val) := by decide
example (w : List Bool)
    (hall : ∀ j : Fin (w.length+1), ¬ P2 (w.take j.val)) :
    ¬ ∃ j, 0 < j ∧ j ≤ w.length ∧ P2 (w.take j) := by
  rintro ⟨j, hj, hjlen, hp⟩
  exact hall ⟨j, by omega⟩ hp
example : P2 [true,true,false] ∧
    (∀ j : Fin 3, 0 < j.val → ¬ P2 ([true,true,false].take j.val)) := by decide
example : defect ([] : List Bool) = 0 := by decide
example : defect w7 = 0 ∧ defect (w7.take 5) = -1 := by decide
#check minimal_p2_ends_S
#check first_p2_prefix_ends_S
#print axioms defect_append_sign
#print axioms defect_pos_before_p2
#print axioms minimal_p2_ends_S
#print axioms first_p2_prefix_ends_S
end IndependentIssue74Controls
```

A second independent stdin check, also exit 0:

```lean
import Recaman.FirstP2EndingS
open Recaman.LeadingRunSupply Recaman.FirstP2EndingS
example : moment [true,false,false] = -4 ∧ 0 < defect [true,false,false] := by decide
```

## Independent arithmetic reproduction command

The following inline Python command was run at the source revision and hashes
above. It enumerates all literal words, with the disjoint previously used
ranges retained. Exact returned count dictionaries were:

```text
independent_reproduction 0 11 {'words': 4095, 'ceil2': 2638, 'p2': 298, 'first_end_violation': 0, 'defect_violation': 0}
independent_reproduction 12 16 {'words': 126976, 'ceil2': 70290, 'p2': 7442, 'first_end_violation': 0, 'defect_violation': 0}
```

```sh
python3 - <<'PYCONTROL'
from itertools import product
import hashlib
from pathlib import Path
files = ['Recaman/FirstP2EndingS.lean', 'Recaman/LeadingRunSupply.lean', 'Recaman/ShortPeriodicSupply.lean']
for f in files:
 print(f, hashlib.sha256(Path(f).read_bytes()).hexdigest())
def metrics(w):
 h=m=0; hs=[0]; ms=[0]; p2=[]; ds=[0]
 for k,c in enumerate(w,1):
  s=1 if c=='A' else -1
  h+=s; m+=k*s; hs.append(h); ms.append(m); ds.append(m-k*(h-1))
  if h==1 and m==0: p2.append(k)
 return hs,ms,p2,ds
for w in ['', 'A', 'ASSA', 'AAS', 'AASASSA', 'AAASSSASASA']:
 hs,ms,hits,ds=metrics(w)
 print(repr(w),dict(heights=hs,moments=ms,P2_indices=hits,defects=ds,ceiling=max(hs)))
for lo,hi in [(0,11),(12,16)]:
 counts=dict(words=0,ceil2=0,p2=0,first_end_violation=0,defect_violation=0)
 for n in range(lo,hi+1):
  for bits in product('AS',repeat=n):
   w=''.join(bits); hs,ms,hits,ds=metrics(w); counts['words']+=1
   if max(hs)>2: continue
   counts['ceil2']+=1
   if hits:
    counts['p2']+=1
    counts['first_end_violation']+=int(w[hits[0]-1]!='S')
   elif n: counts['defect_violation']+=int(ds[-1]<=0)
 print('independent_reproduction',lo,hi,counts)
PYCONTROL
```

## Remaining uncertainty and next decision

No unresolved semantic obligation for this bounded #74 statement was found.
Finite computation is supporting validation only. The proof consumes the
prefix ceiling and does not derive it from an SS budget; #75 is a separate
unit. E-361's complete paper claim, #76 witnesses, actual-orbit occurrence,
owner constraints and general T6/Hall were not resolved by this audit.

Recommendation: accept E-362's independent meaning review as PASS, preserve
its exact scope, and hand this file to the integrating parent session.
Do not extend the word theorem's prose to the open global problem. No stop
recommendation is needed for this successfully completed bounded audit.
