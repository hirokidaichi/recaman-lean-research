# SS2 collision-pair research handoff, 2026-10-06

The proposed local Hall inequality is **CONJECTURED**. The bounded
capacity-proof route is **STOPPED**: shared-oldest geometry alone does not
supply the second subtraction phase. No Lean theorem or central claim was
promoted. Parent research and a user-requested **GPT-6.1-Sol subagent** ran
in parallel; a separate auditor checked the entry conditions and final work.

## What was tested (COMPUTED)

All positive-mass binary words of periods 1 through 22, modulo rotation
but including imprimitive words: **178,373 representatives**, accounting
for **3,716,111 phase-labelled words**. All possible P2 lags are covered by
the positive-mass quotient formula, not a lag<p cutoff.

Only **24 same-oldest donor pairs**, and **86 pair/lowSS-subset cases**,
exercise the proposed inequality. All pass; the smallest slack
|N(L∪{v,w})|-|L|-2 is 3. The millions of words must not be presented as
millions of nonvacuous collision tests. These are finite results, not a
general proof.

| Partition | Periods | Collision pairs | All lowSS subsets | Violations |
|---|---|---|---|---|
| Discovery | 1–18 | 3 | 10 | 0 |
| Holdout | 19–22 | 21 | 76 | 0 |

[Protocol frozen before discovery](protocol-frozen.md). Some of these
period ranges have appeared in earlier research; the holdout label means
the frozen, disjoint partition for this new unit, not historically unseen
binary words. The finite-range scan includes arbitrary specified lowSS
lags by the monotonic first-P2-prefix argument in the protocol.

There are 16 exact output records, independently replayed in Python, plus
22 period summary rows checked against binomial positive-mass word counts.
The C++ run additionally checks its lag formula against a direct
p(p+1) scan for all current-A phases at p≤12 and every collision word
(2,613 phase checks). The known p16 E-133 pair is reproduced with lag19≥p.

## Paper result and limits

Sol's [complete report](sol61/report.md) records a necessary geometry.
After lifting the common oldest S to the same integer clock, the A-ending
donor always precedes the S-ending donor. Their words have the forms
W_A=C A and W_S=X C, where C has mass0, moment−d_A and two SS edges;
X ends A, is SS-free, and has mass1 and moment d_A.

This auxiliary argument is **PROVED-PAPER**, with
[independent final review PASS](audit/report.md); it is not a new Hall allocation.
The noSS word classification overlaps existing E-145 and is not counted
as a new frontier theorem. No Lean implementation was warranted.

Two attempts stop: requiring another S only inside the donors while fixing
all lowSS endpoint assignments is stronger than the requested target;
rewriting failure as N=F∪{sigma} and postulating an augmenting path provides
no independent structural input. The missing constraint concerns actual
lowSS windows ending at internal S positions of C/X. Reopen with a
concrete, separately falsifiable endpoint/core interaction, not a larger
period census or a Hall conclusion hidden in a hypothesis.

## Provenance and reproducible commands

Base: ba7fe41e3c96d0762198731d658b10dbfd9f53d1.
Primary checkout main75491ee is a divergent, unmerged research branch
with overlapping evidence IDs; its claims and dirty files were not used.

Run from the repository root:

~~~sh
clang++ -O3 -std=c++17 experiments/ss2_collision_pair.cpp -o /tmp/recaman-ss2-collision-20261006
/tmp/recaman-ss2-collision-20261006 1 18
python3 experiments/verify_ss2_collision_pair.py docs/data/ss2_collision_pair_20261006/discovery.jsonl
/tmp/recaman-ss2-collision-20261006 19 22
python3 experiments/verify_ss2_collision_pair.py docs/data/ss2_collision_pair_20261006/discovery.jsonl docs/data/ss2_collision_pair_20261006/holdout.jsonl
python3 docs/data/ss2_collision_pair_20261006/sol61/boundary.py
~~~

Exact outputs: [discovery](discovery.jsonl), [holdout](holdout.jsonl),
[discovery verification](discovery-verification.json), [final verification](verification.json),
[Sol boundary replay](sol61/boundary.out).
Frozen C++ SHA256:
184f9c96d9f9c24d4b4a009e555adbd6c6a66b401e42eb351efc22e8ef9343b4.

The first verifier invocation failed before holdout because the local
Python lacks int.bit_count. Replacing it with bin(n).count("1") fixed
runtime compatibility; the C++ source, hypothesis and partitions did not
change. Discovery verification then passed before holdout was executed.
Holdout was executed once by the parent.

The auditor independently recounted the same frozen range with direct
mass/moment accumulation and a different subset/rotation implementation.
[All 22 periods and 10 fields per period match](audit/comparison.json).
The audit is a reproducibility check, not an additional holdout or range
extension. Its [code](audit/independent.cpp), [exact output](audit/independent.out),
and [commands](audit/commands.log) are retained. To rebuild that recount
from the saved files:

~~~sh
clang++ -O2 -std=c++17 docs/data/ss2_collision_pair_20261006/audit/independent.cpp -o /tmp/recaman-ss2-collision-audit
/tmp/recaman-ss2-collision-audit
~~~

Environment: Python 3.9.6, Apple clang 17.0.0 (arm64 macOS).
Repository checks: check_research_registry.sh, G1–G5 and protected claims
passed; viewer manifest check and git diff --check passed. Source and data
integrity hashes are in [SHA256SUMS](SHA256SUMS).

Changed files: hypothesis card, frontier/plan cross-references, this
data directory, C++ falsifier and independent Python verifier.
No Lean, registry, protected labels, gate code or other session files changed.
No full Lean rebuild is needed for these documentation/experiment changes.
