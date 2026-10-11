# Hypothesis card: internal SSS phase separation

- ID: `H-20261011-03`
- Owner: Codex; proposer, falsifier, formalizer and auditor are separate passes.
- Created: 2026-10-11
- Base: `47f4912a02e205801b218b319b2bce4788d29bd9`
- Status: `PROVED-LEAN` (E-372; narrower than full E-370)
- Research branch: `codex/e370-internal-sss-workpacket-20261011`

## Exact statement

For every `e : Int → Bool`, positive period `p` with `e(x+p)=e(x)` for
all integers x, integer u, natural d, and integer s,q, assume
`ssCount (past e u d) ≤ 2`, `u-d ≤ s < q`, `q+2 < u`, and
`e(s)=e(q)=e(q+1)=e(q+2)=false`. Then `phase p s ≠ phase p q`.
In particular this applies to the actual oldest S of an SS2 donor.
No P2, minimality, current-A, NoSAAS, positive mass, Hall, owner map,
or actual Recamán orbit assumption is needed for this local separation.

## Why it would matter

This is the missing phase-distinctness edge in the q>s part of the E-370
work packet. With E-368 oldest-S exclusion and the existing internal-SSS
endpoint exclusion, a minimal SS2 donor has two distinct excluded phases.
The q=s collision case and the full E-370 capacity theorem remain separate.

## Provenance and dependencies

Use actual `past`, `ssCount`, and `phase` from the existing modules.
Dependency chain before implementation: periodic phase equality transports
the S at q+1 to s+1; the two SS edges q,q+1 already exhaust the window's
budget; the earlier edge s is a third distinct edge, a contradiction.
The smallest new structural input counts that third edge even when s=q-1.
Search: E-369/E-371 refute collision-injectivity shortcuts; the separated
SS endpoint candidate H-20261011-02 remains conjectural. None is reused as
an assumption. The E-370 packet already contains the informal argument.

## Falsification plan

- Discovery: all binary periods p=1..5, all current phases u=0..p-1,
  d=0..3p+3, and all eligible s,q in each window.
- Frozen holdout: the same protocol for p=6..9, run once after discovery.
- Weakening: remove the SS budget, strict s<q, or triple containment;
  record concrete countermodels. Arbitrary sign histories are allowed,
  including negative/zero drift, non-P2 windows and cyclic wrapping.
- One repair allowed only for an explicitly diagnosed statement error.
- Stop: a full-premise counterexample, a circular capacity premise, or
  a second repair; otherwise finish the bounded separation lemma.

## Evidence log

| Date | Label | Revision / command | Result |
|---|---|---|---|
| 2026-10-11 | `COMPUTED` | Base above + probe SHA256 `b87eeb7a3c2abf4b718e0e742f8c6c859f750999366393f74de953114e39172e`; `python3 experiments/internal_sss_phase_probe.py discovery` | p=1..5: 62 words, 4,470 windows, 37 eligible pairs, 32 wrapping, 37 nonpositive mass, 0 violations |
| 2026-10-11 | `COMPUTED` | Same source; `python3 experiments/internal_sss_phase_probe.py holdout` | Frozen p=6..9: 960 words, 231,040 windows, 6,857 eligible pairs, 4,675 wrapping, 5,094 nonpositive mass, 0 violations |
| 2026-10-11 | `REFUTED` | Same source; `python3 experiments/internal_sss_phase_probe.py controls` | Removing budget, strict s<q, or triple containment gives three explicit all-S periodic countermodels; these do not refute the full statement |
| 2026-10-11 | `PROVED-LEAN` | `lake env lean Recaman/SS2InternalSSS.lean`; source SHA256 `50c2fb72b83027939dd9653f75f3f4d9153809cd76eff494af0d67ef6c11e249` | Uniform phase separation and its composition with E-368 and endpoint exclusion compile; all seven theorem symbols added to Audit |

Exact JSONL outputs: [discovery](data/internal_sss_phase_20261011/discovery.jsonl),
[holdout](data/internal_sss_phase_20261011/holdout.jsonl),
[controls](data/internal_sss_phase_20261011/controls.jsonl).
The holdout was executed once, after discovery, before any Lean implementation.
Finite results are only `COMPUTED`; the unbounded evidence is the Lean proof.

Static check: `python3 scripts/harness_gate.py --lint-module Recaman/SS2InternalSSS.lean`
passes 7/7. Complete check: `LEAN_NUM_THREADS=1 make test` (includes
`./scripts/check.sh`), 397 build jobs and 2,664 permitted-axiom declarations.
Exact final output: [make_test.log](data/internal_sss_phase_20261011/make_test.log).
`lake env lean --stdin < docs/data/internal_sss_phase_20261011/independent_controls.lean.txt`
was rerun by the parent after rebuilding the final module: exit0, no output.
Final-source [statement audit](statement_audits/E-372.md) and
[independent audit](statement_audits/E-372-independent.md) record exact scope.

One rejected illustrative control: repeating SASSS and taking six clocks
adds a third SS edge across the period seam, so the proposed count two was
false and Lean rejected it. The final SASSSA control wraps seven clocks
with exactly two SS edges. This was a control correction, not a repair of
the conjecture. Initial proof-script fixes were a missing natural-arithmetic
step and the orientation of `lift_equal_mod`; no hypotheses changed.

## Semantic audit

Check that all S clocks and the SS budget refer to the same actual window;
integer distinctness alone is insufficient because phases may wrap.
Both directions of the intended statement use the explicit bounds above.
The claim is independent of reachability and does not establish a full
collision capacity theorem. Independent donor-level nonvacuity: chronological
period ASASASSSAAA, p=11,u=d=11, minimal P2 word AAASSSASASA with SS=2,
oldest clock s=1, internal q=5. The same stream has current-A lowSS AAS at
t=10,l=3. Thus both the donor and endpoint quantifiers are inhabited.
The final conclusion omits restatements of its hypotheses and writes the
oldest phase explicitly so the G5 parser quotes the entire signature.

## Decision

Complete this bounded formalization. E-372 proves the internal q>s phase
separation and two-excluded-phase result; E-370 stays `PROVED-PAPER`.
Next decision: formalize concrete-neighborhood counting and the q=s
NoSAAS collision classification from actual donor windows. Stop this unit
here; do not substitute the new internal hypothesis for the missing q=s
case, extend the lag census, or promote any pinned central claim.

## Changed files and CI repair

- `Recaman/SS2InternalSSS.lean`: explicit edge counting, phase separation,
  donor composition and wrapping control; `Recaman/Audit.lean`: four new
  axiom reports alongside the three existing endpoint reports.
- `experiments/internal_sss_phase_probe.py` and
  `docs/data/internal_sss_phase_20261011/`: frozen falsifier, exact outputs,
  independent Lean controls and final full-test log.
- E-372 registry row, exact statement and independent audits, this card,
  `CURRENT_FRONTIER.md`, `PROOF_MAP.md`, and E-370 work packet: scope and
  remaining obligations synchronized after the evidence stabilized.
- `.github/workflows/ci.yml` and `viewer/manifest.json`: fix the observed
  stale manifest failure and check generated metadata immediately after
  checkout. The full final `make test` still checks it again.

CI failure inspected: run38139001903 at commit2eef0e3 passed Lean, axiom
audit and empirical regressions, then failed on stale viewer metadata.
Fix47f4912 regenerated it and added the early check. Local `make test`
passes; GitHub hosted execution is tracked on PR90. No research gate was
weakened. The original checkout's uncommitted work was left untouched;
all changes in this unit are in an isolated managed worktree.
