# Independent semantic audit: E-363 / issue #75

**PASS.** The signatures prove the issue #75 bounds with the intended quantifiers
and maximal-terminal-run meaning. No mathematical discrepancy, hidden cutoff,
unproved obstruction hypothesis, or assumed ceiling was found.

Review date: 2026-10-01. Reviewer: a separate Codex subagent, delegated explicitly
for an independent meaning audit. The implementation session's audit is not used
as evidence for the verdict. Initial HEAD: `cbe51b7b1216f9700f432eb14803277113c02af4`.
Workspace: `/Users/hirokidaichi/.codex/worktrees/first-p2-ending-s/recaman-lean-research`.
Primary-checkout dirty files were neither used nor edited.

## Bounded question and gate

Do the E-363 signatures prove exactly the issue #75 terminal-A bounds for all
finite newest-first Bool words, with overlapping SS count and maximal terminal
run, without a cutoff or an assumed prefix ceiling? Acceptance requires reading
the actual definitions and dependencies, checking both meanings of the terminal
representation, preserving every predeclared control, kernel-checking the source
and independent controls, and inspecting axioms. Stop after 15 minutes or on a
material mathematical mismatch. No repairs or new research conjectures.

The protocol roles in this pass are separated: proposer = the frozen issue/card;
falsifier = independently reconstructed boundary and weakened-premise controls;
formalizer = checking existing declarations and independent kernel consumers;
auditor = comparing binders, dependencies, and scope. This audit introduces no
new research theorem or new Lean module.

## Exact signatures copied from source

### Recaman.TerminalASSBound.p2_terminal_decomposition

```lean
theorem p2_terminal_decomposition (w : List Bool) (hp : P2 w) :
    ∃ u t, w = (u ++ [false]) ++ List.replicate t true
```

### Recaman.TerminalASSBound.terminal_run_length

```lean
theorem terminal_run_length (u : List Bool) (t : Nat) :
    (((u ++ [false]) ++ List.replicate t true).reverse.takeWhile id).length = t
```

### Recaman.TerminalASSBound.p2_terminal_A_le_ss

```lean
theorem p2_terminal_A_le_ss (u : List Bool) (t : Nat)
    (hp : P2 ((u ++ [false]) ++ List.replicate t true)) :
    t ≤ ssCount ((u ++ [false]) ++ List.replicate t true)
```

### Recaman.TerminalASSBound.minimal_p2_terminal_A_lt_ss

```lean
theorem minimal_p2_terminal_A_lt_ss (u : List Bool) (t : Nat)
    (hp : P2 ((u ++ [false]) ++ List.replicate t true))
    (hmin : ∀ j, 0 < j → j < ((u ++ [false]) ++ List.replicate t true).length →
      ¬ P2 (((u ++ [false]) ++ List.replicate t true).take j))
    (ht : 0 < t) :
    t < ssCount ((u ++ [false]) ++ List.replicate t true)
```

### Recaman.TerminalASSBound.minimal_p2_terminal_A_le_ss_sub_one

```lean
theorem minimal_p2_terminal_A_le_ss_sub_one (u : List Bool) (t : Nat)
    (hp : P2 ((u ++ [false]) ++ List.replicate t true))
    (hmin : ∀ j, 0 < j → j < ((u ++ [false]) ++ List.replicate t true).length →
      ¬ P2 (((u ++ [false]) ++ List.replicate t true).take j)) :
    t ≤ ssCount ((u ++ [false]) ++ List.replicate t true) - 1
```

### Recaman.TerminalASSBound.minimal_p2_ss_two_terminal_A_le_one

```lean
theorem minimal_p2_ss_two_terminal_A_le_one (u : List Bool) (t : Nat)
    (hp : P2 ((u ++ [false]) ++ List.replicate t true))
    (hmin : ∀ j, 0 < j → j < ((u ++ [false]) ++ List.replicate t true).length →
      ¬ P2 (((u ++ [false]) ++ List.replicate t true).take j))
    (hss : ssCount ((u ++ [false]) ++ List.replicate t true) = 2) : t ≤ 1
```

### Recaman.TerminalASSBound.minimal_p2_terminal_bound

```lean
theorem minimal_p2_terminal_bound (w : List Bool) (hp : P2 w)
    (hmin : ∀ j, 0 < j → j < w.length → ¬ P2 (w.take j)) :
    ∃ u t, w = (u ++ [false]) ++ List.replicate t true ∧
      (w.reverse.takeWhile id).length = t ∧ t ≤ ssCount w - 1
```

### Recaman.TerminalASSBound.terminal_suffix_mass_lower

```lean
theorem terminal_suffix_mass_lower (u : List Bool) (t q : Nat) (c : Int)
    (hc : c ≤ 0) (hct : c ≤ (t : Int) - q - 1)
    (hss : ssCount ((u ++ [false]) ++ List.replicate t true) ≤ q) :
    ∀ j, c ≤ mass (((u ++ [false]) ++ List.replicate t true).drop j)
```

### Recaman.TerminalASSBound.prefix_ceiling_of_ss_le_terminal_A

```lean
theorem prefix_ceiling_of_ss_le_terminal_A (u : List Bool) (t : Nat)
    (hm : mass ((u ++ [false]) ++ List.replicate t true) = 1)
    (ht : ssCount ((u ++ [false]) ++ List.replicate t true) ≤ t) :
    ∀ j, j ≤ ((u ++ [false]) ++ List.replicate t true).length →
      mass (((u ++ [false]) ++ List.replicate t true).take j) ≤ 2
```

## Independent kernel controls and consumers

The block below is runnable through `lake env lean --stdin`. `decide` is
kernel reduction; there is no native proof escape. The generalized consumers
use only the proved terminal decomposition and bounds, so they check that the
concrete-decomposition signatures genuinely cover arbitrary P2 words.

```lean
import Recaman.TerminalASSBound
open Recaman.LeadingRunSupply Recaman.OneSSMultiplicity
open Recaman.TerminalASSBound
set_option maxRecDepth 4096
namespace Independent363

theorem overlap_control : ssCount [false,false,false] = 2 := by decide

theorem aas_control : P2 [true,true,false] ∧ ssCount [true,true,false] = 0 ∧
  ([true,true,false].reverse.takeWhile id).length = 0 ∧
  (∀ j : Fin 3, ¬ P2 ([true,true,false].take j.val)) ∧
  ¬ ((0 : Nat) < 0) ∧ (0 : Nat) ≤ 0 - 1 := by unfold P2; decide

theorem aasassa_control : P2 [true,true,false,true,false,false,true] ∧
  ssCount [true,true,false,true,false,false,true] = 1 ∧
  ([true,true,false,true,false,false,true].reverse.takeWhile id).length = 1 ∧
  P2 ([true,true,false,true,false,false,true].take 3) ∧
  ¬ ((1 : Nat) < 1) := by unfold P2; decide

theorem assa_control : moment [true,false,false,true] = 0 ∧
  mass [true,false,false,true] = 0 ∧ ¬ P2 [true,false,false,true] ∧
  ssCount [true,false,false,true] = 1 ∧
  ([true,false,false,true].reverse.takeWhile id).length = 1 ∧
  (∀ j : Fin 4, ¬ P2 ([true,false,false,true].take j.val)) ∧
  ¬ ((1 : Nat) < 1) := by unfold P2; decide

theorem a_control : mass [true] = 1 ∧ moment [true] = 1 ∧ ¬ P2 [true] ∧
  ssCount [true] = 0 ∧ ([true].reverse.takeWhile id).length = 1 := by
  unfold P2; decide

theorem saa_mass_only_control : mass [false,true,true] = 1 ∧
  ¬ P2 [false,true,true] ∧ ssCount [false,true,true] = 0 ∧
  ([false,true,true].reverse.takeWhile id).length = 2 ∧
  ¬ (2 ≤ ssCount [false,true,true]) := by unfold P2; decide

theorem q_two_sharp_control :
  P2 [true,true,true,false,false,false,true,false,true,false,true] ∧
  ssCount [true,true,true,false,false,false,true,false,true,false,true] = 2 ∧
  ([true,true,true,false,false,false,true,false,true,false,true].reverse.takeWhile id).length = 1 ∧
  (∀ j : Fin 11, ¬ P2 ([true,true,true,false,false,false,true,false,true,false,true].take j.val)) ∧
  mass ([true,true,true,false,false,false,true,false,true,false,true].take 3) = 3 := by
  unfold P2; decide

theorem all_word_weak (w : List Bool) (hp : P2 w) :
  (w.reverse.takeWhile id).length ≤ ssCount w := by
  obtain ⟨u, t, hw⟩ := p2_terminal_decomposition w hp
  subst w
  rw [terminal_run_length]
  exact p2_terminal_A_le_ss u t hp

theorem all_word_saturated (w : List Bool) (hp : P2 w)
  (hmin : ∀ j, 0 < j → j < w.length → ¬ P2 (w.take j)) :
  (w.reverse.takeWhile id).length ≤ ssCount w - 1 := by
  obtain ⟨u, t, hw⟩ := p2_terminal_decomposition w hp
  subst w
  rw [terminal_run_length]
  exact minimal_p2_terminal_A_le_ss_sub_one u t hp hmin

theorem all_word_strict (w : List Bool) (hp : P2 w)
  (hmin : ∀ j, 0 < j → j < w.length → ¬ P2 (w.take j))
  (ht : 0 < (w.reverse.takeWhile id).length) :
  (w.reverse.takeWhile id).length < ssCount w := by
  obtain ⟨u, t, hw⟩ := p2_terminal_decomposition w hp
  subst w
  rw [terminal_run_length] at ht ⊢
  exact minimal_p2_terminal_A_lt_ss u t hp hmin ht

end Independent363
#print axioms Independent363.overlap_control
#print axioms Independent363.aas_control
#print axioms Independent363.aasassa_control
#print axioms Independent363.assa_control
#print axioms Independent363.a_control
#print axioms Independent363.saa_mass_only_control
#print axioms Independent363.q_two_sharp_control
#print axioms Independent363.all_word_weak
#print axioms Independent363.all_word_saturated
#print axioms Independent363.all_word_strict
```

## Frozen finite sanity protocol

Before this auxiliary run, fix exhaustive words of lengths 0..7 as the discovery
pass and 8..15 as the disjoint check pass. These ranges are an audit sanity test,
not new unexposed holdout data and not evidence of an all-length theorem. Use an
independent positional-moment formula, adjacent-pair count and reversed terminal
scan. For every P2 word check the S-containing decomposition, weak bound, minimal
positive strict bound, saturated bound, SS=2 corollary and suffix lower bound.
Report the exact totals and violations; no parameter repair.

```python
import itertools, json

def mass(w):
    return sum(1 if b else -1 for b in w)

def moment(w):
    return sum((i+1)*(1 if b else -1) for i,b in enumerate(w))

def p2(w):
    return mass(w) == 1 and moment(w) == 0

def check(lo, hi):
    result = dict(lengths=[lo,hi], words=0, p2=0, minimal=0,
                  violations=dict(decomposition=0, weak=0, strict=0,
                                  saturated=0, ss_two=0, suffix=0))
    for n in range(lo,hi+1):
        for w in itertools.product((False,True),repeat=n):
            result['words'] += 1
            if not p2(w): continue
            result['p2'] += 1
            q = sum(not w[i] and not w[i+1] for i in range(n-1))
            t = 0
            for b in reversed(w):
                if not b: break
                t += 1
            v = result['violations']
            v['decomposition'] += int(t == n or w != w[:n-t-1]+(False,)+(True,)*t)
            v['weak'] += int(t > q)
            v['suffix'] += int(any(mass(w[j:]) < min(0,t-q-1) for j in range(n+1)))
            minimal = all(not p2(w[:j]) for j in range(1,n))
            if minimal:
                result['minimal'] += 1
                v['strict'] += int(t > 0 and not t < q)
                v['saturated'] += int(t > max(q-1,0))
                v['ss_two'] += int(q == 2 and t > 1)
    return result

for lo,hi in [(0,7),(8,15)]:
    print(json.dumps(check(lo,hi),sort_keys=True))
```

## Meaning audit and dependency chain

1. **Definitions.** `ShortPeriodicSupply.sign b = if b then 1 else -1`;
   `LeadingRunSupply.mass w = (w.map sign).sum`; `moment [] = 0` and
   `moment (b::w) = sign b + mass w + moment w`. Recursion gives
   `moment W = sum_i (i+1)*sign(W[i]) = sum_{j<length W} mass(W.drop j)`.
   P2 is literally `mass w = 1 ∧ moment w = 0`. The established
   `past_p2_iff` equates this with the original backward stream predicate.
   The leftmost symbol is newest; `take j` is the short backward window;
   the terminal run is the rightmost (oldest-side) A run. No orientation swap.
2. **Overlap.** `ssCount (b::w)` adds one exactly when `b=false` and
   `w.head?=some false`, then recurses on `w`. Thus SSS contributes two
   adjacent pairs, not one disjoint pair. The kernel control checks this.
   `ssCount_tail_le` includes pairs crossing a removed head/tail boundary.
3. **All words and maximality in both directions.** A P2 word contains S:
   otherwise `all_A_of_no_S` and the proved `not_p2_all_A` contradict P2.
   Last-sign recursion constructs `(u++[S])++A^t` for every S-containing
   word. Such a decomposition includes all terminal A symbols since the
   preceding symbol is S. Conversely, removing the actual maximal A suffix
   of an S-containing word leaves precisely a final S and a prefix u.
   `terminal_run_length` identifies every decomposition with the canonical
   reverse/takeWhile length; `terminal_length_unique` prevents different t.
   Substituting the issue's equality W=(X++[S])++A^t supplies the theorem's
   u,t binders. The independent all-word consumers show the reverse mapping:
   these decomposition-specific signatures apply to arbitrary P2 W.
4. **Suffix bound.** The concrete recursive `LowSSEndpoint.mass_ending_A`
   proves mass(w++A)>=-ssCount(w++A). Mass additivity and unchanged SS count
   imply mass(w)>=-ssCount(w)-1. `terminal_suffix_mass_lower` recurses over u,
   using this inequality and suffix count monotonicity before the final run,
   and nonnegative mass within the run. It handles every drop j, including
   j=0 and empty suffixes. The c<=0 binder expresses the minimum with zero;
   there is no word-length bound.
5. **Weak bound.** Negating t<=q gives t>q, hence t-q-1>=0. The suffix lemma
   supplies c=0. Recursive moment nonnegativity then gives moment W>=mass W=1,
   contradicting P2's moment W=0. No minimality or moment-sign assumption.
6. **Strict bound and derived ceiling.** Negating t<q gives q<=t. The suffix
   lemma supplies c=-1. Take/drop mass additivity and total mass 1 give
   every prefix mass<=2. This derived ceiling is passed to the proved
   E-362 `minimal_p2_ends_S`, together with P2 and exact proper-prefix
   minimality. The S-ended output contradicts t>0 by reversing the lists.
   The helper's q<=t assumption is the contradiction regime, not an
   unproved property of minimal P2 words. E-362's own source derives its
   defect positivity and assumes no sign condition on earlier moments.
7. **Zero and SS=2.** For t=0 the saturated Nat bound is trivial even at q=0;
   for t>0 strictness gives t<=q-1. No negative Int bound replaces Nat
   subtraction. The SS=2 corollary gives t<=1. Main signatures have no cutoff,
   assumed ceiling, NoSAAS, orbit, reachability, periodicity, current-A,
   owner-family or Hall condition.

G5 answers for the seven registry-cited signatures: concrete Bool-word
binders **yes**; conclusion or an unproved defined obstruction hypothesis
among inputs **no**. P2 is the specified original predicate; minimality
excludes exactly every positive proper take-prefix. Wrapper status is in the
classification below. A final omega step consuming proved word inequalities
is not itself evidence of vacuity.

## Counterfactuals preserved

| Control | Independent kernel result and implication |
|---|---|
| AAS | Minimal P2, q=t=0; removing t>0 makes strictness false, while Nat 0<=0-1 is true |
| AASASSA | P2, q=t=1; proper prefix length 3 is P2, so dropping minimality makes strictness false |
| ASSA | moment=0, mass=0, q=t=1; all proper prefixes non-P2 yet t<q false; moment-only cannot replace P2 in the strict statement |
| A | mass=1, moment=1, non-P2, no S; mass-only cannot support the all-P2 decomposition or bound |
| SAA (extra control) | mass=1, actual S/A decomposition, t=2,q=0; mass-only fails even the weak bound in the represented domain |
| AAASSSASASA | Minimal P2, q=2,t=1, prefix mass 3; excludes the invalid strengthening t=0 and detects a globally assumed ceiling that would omit a valid sharp case |
| SSS | ssCount=2, confirming overlapping adjacent pairs |

No counterexample to the intended statement was found. The first independent
Lean control attempt failed to synthesize Decidable for the opaque P2 predicate
with bare `by decide`. `unfold P2; decide` checked the same fixed statements.
This was an elaboration correction, not a mathematical repair or hypothesis
change. One subsequent report-writing shell heredoc failed before modifying
the file; a distinct delimiter corrected that tooling error.

## R/W/C/T manual classification

Following the 2026-09-15 audit definitions: R = actual-word content; W = proved
applications/corollaries; C = unproved key obstruction assumed; T = free
arithmetic or tautology. Independent assessment: **R/W/C/T = 9/7/0/0**.
The heuristic gate reports 16/16 substantive and 0/16 vacuity flags; that
is not the mathematical verdict.

| Class | Declarations | Reason |
|---|---|---|
| R | all_A_of_no_S; exists_terminal_decomposition_of_S | List induction and last-sign recursion |
| R | terminal_run_length | Induction/reduction on the actual appended run |
| R | ssCount_post_As; terminal_suffix_mass_lower | Actual appended/dropped words and overlap-count recursion |
| R | moment_nonneg_of_suffix_mass | Recursive inequality on all actual suffixes |
| R | p2_terminal_A_le_ss | P2 contradiction from the newly proved suffix budget |
| R | prefix_ceiling_of_ss_le_terminal_A | Actual take/drop relation derives the ceiling |
| R | minimal_p2_terminal_A_lt_ss | Derived ceiling, first-P2 theorem and final-sign contradiction |
| W | p2_terminal_decomposition; terminal_length_unique | Derived representation and uniqueness |
| W | mass_ge_neg_ss_sub_one; mass_le_moment_of_suffix_mass | Imported/proved word inequalities and immediate algebra |
| W | minimal_p2_terminal_A_le_ss_sub_one; minimal_p2_ss_two_terminal_A_le_one; minimal_p2_terminal_bound | Genuine corollaries of substantive bounds, not independent novelty |

The mild run-length/count inductions are R helpers, not separate research
advances. The substantive content is the suffix budget and weak/strict P2
bounds. No C or T declaration resolves an issue by fiat.

## Executed commands and exact outcomes

All commands used the stated worktree. `gh issue view 75 --json
number,title,state,body,url` returned OPEN and the exact quantifiers audited
above. Context/source inspection used cat, sed, rg, git status -s, git rev-parse
HEAD, git log -1 -- <target> and git show <initial-head>:<import-file>.
There was no Git index/branch mutation, commit, push, GitHub comment, registry
update or existing-card edit. Only this independent audit file was created.

- `python3 scripts/report_vacuity.py --all Recaman/TerminalASSBound.lean`:
  `Recaman/TerminalASSBound.lean: 0/16 theorems flagged` and
  `# modules 1, fully-flagged modules 0, theorems 16, flagged theorems 0`.
- `python3 scripts/harness_gate.py --lint-module Recaman/TerminalASSBound.lean`:
  `# Recaman/TerminalASSBound.lean: 16/16 substantive theorems`, exit 0.
- `lake env lean Recaman/TerminalASSBound.lean`: empty output, exit 0.
- `lake build Recaman.TerminalASSBound`: `Build completed successfully (31 jobs).`,
  exit 0. Independent controls were rerun after the dependency build, exit 0.
- Import closure: 30 project sources, all byte-identical to initial HEAD;
  no sorry/admit/native_decide/axiom token. During this audit #76 advanced
  HEAD to `6a4350b9a02ce5cb8ef7a7f42a5ba1cca94f7e37`; the audited source did
  not change. Target's introducing commit remains the initial HEAD.
- Independent `lake env lean --stdin`: seven control theorems have no axioms;
  three all-word consumers use only `{propext, Classical.choice, Quot.sound}`;
  exit 0. The exact executable block is preserved above.
- Separate axiom probe through `lake env lean --stdin`: all 16 target
  declarations plus `FirstP2EndingS.minimal_p2_ends_S`,
  `LowSSEndpoint.mass_ending_A`, `LeadingRunSupply.not_p2_all_A` give 19
  reports, all within the same permitted standard set; exit 0. No user axiom
  or sorryAx. The probe is generated with one `#print axioms` per name.
- Frozen finite sanity run (`COMPUTED`, not proof), exit 0:

```json
{"lengths": [0, 7], "minimal": 3, "p2": 5, "violations": {"decomposition": 0, "saturated": 0, "ss_two": 0, "strict": 0, "suffix": 0, "weak": 0}, "words": 255}
{"lengths": [8, 15], "minimal": 172, "p2": 292, "violations": {"decomposition": 0, "saturated": 0, "ss_two": 0, "strict": 0, "suffix": 0, "weak": 0}, "words": 65280}
```

| Audited object | SHA-256 |
|---|---|
| Recaman/TerminalASSBound.lean | 32d7fa24feefee9e9951f7ad3b2d01f5bac0e5c58decd30ee7620b79ea2e3212 |
| Recaman/FirstP2EndingS.lean | 9c07e5131aedcc7e4ce547d945e9a8ed7683ce1c3e01aae44d4213665bb4b439 |
| Recaman/LowSSEndpoint.lean | 3fa27e49ac3455c33f684994d4810c2c13e1d18a31465bcb26bb2f1a4d03884d |
| Recaman/LeadingRunSupply.lean | 0aff15293c82c92897c1715a6331ddc3624241f53227983eecd8409d9910ad4c |
| Recaman/OneSSMultiplicity.lean | 39929524f240425aafa9df0674eb1d88eddbfcf49a07a3553d1a03e85beb2155 |
| Recaman/ShortPeriodicSupply.lean | d6f89f0fedbe89057157dc56ad8dce2409a2a12abae085846871e24f1966763e |
| Independent Lean block plus newline | 097a17cbc608c84795c97d68b758d6baf7fd712783119f56cfe701c3c3bd69c5 |
| Independent Python block plus newline | c89e47d9c7d1f649d231dad2bf96ade07472649b74a60707f9237978f296e640 |

Rerun both embedded blocks without creating files:

```sh
python3 - <<'PY'
from pathlib import Path
import re, subprocess
text = Path('docs/statement_audits/E-363-independent.md').read_text()
lean = re.findall(r'```lean\n([\s\S]*?)\n```', text)[-1] + '\n'
subprocess.run(['lake','env','lean','--stdin'], input=lean, text=True, check=True)
probe = re.findall(r'```python\n([\s\S]*?)\n```', text)[-1] + '\n'
subprocess.run(['python3','-'], input=probe, text=True, check=True)
PY
```

No repository Lean source changed, so this reviewer did not rerun the full
`./scripts/check.sh`; targeted dependency build, direct source check,
independent kernel controls and axiom probe all passed. Integrating-session
whole-repository validation remains separate.

## Handoff and next decision

**PASS for #75 / E-363.** Existing H-20261001-03 is `PROVED-LEAN` and still
says independent review pending; this separate note supplies that review
without editing the card. Strongest evidence is the all-length source proof
with intended binders, direct kernel checks, axiom inspection and all-word
consumers. Finite enumeration is only auxiliary `COMPUTED` evidence.

Changed file: this audit only. Failed attempts: the Decidable elaboration
and report heredoc noted above; no mathematical repair. Counterfactuals:
all preserved above. Remaining mathematical uncertainty within #75: none
identified. The complete independent #74 review, #76 all-q construction,
owner delta, M1/M2, tight-family avoidance, general Gate T6/#73 and orbit
realization are outside this verdict. Stop this bounded research unit and
accept its exact scope; keep issue #75 OPEN until the integrating workflow
actually closes it. Do not infer capacity or surjectivity results.
