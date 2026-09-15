# AI research instructions

This repository studies an open problem. A successful build is evidence that Lean accepts a
statement, not evidence that the statement captures the intended mathematical claim. Follow
[`docs/AI_RESEARCH_PROTOCOL.md`](docs/AI_RESEARCH_PROTOCOL.md) for every research task.

## Before starting

1. Read `README.md`, `docs/STATUS_REPORT_2026-08-30.md`, `docs/ROADMAP.md`, and the relevant
   entries in `docs/GLOSSARY.md` and `docs/PROOF_MAP.md`.
2. Search the repository before proposing a new definition, invariant, or branch. In particular,
   check the stopped approaches and countermodels in `docs/RESEARCH_PORTFOLIO.md`.
3. State one bounded research question, its acceptance test, and its stopping condition. Do not use
   “prove surjectivity” as a work unit.

## Research loop

- Separate four roles even when one agent performs all of them: proposer, falsifier, formalizer,
  and auditor. The falsifier must try small cases, boundary cases, and weakened-history models
  before formalization begins.
- Maintain a hypothesis card using `docs/HYPOTHESIS_CARD_TEMPLATE.md`. Record the exact
  quantifiers, dependencies, evidence, counterexamples, and status.
- Prefer a falsifiable inequality, finite classification, monotone quantity, or explicit
  countermodel over a new wrapper type or an equivalent reformulation of coverage.
- Use computation to discover and kill conjectures. Split discovery and holdout ranges and record
  the command, source revision, parameters, and exact output. Computation is never a proof.
- Before Lean implementation, write an informal dependency chain and identify the weakest new
  lemma that would change the current research frontier.
- Formalize the intended statement, not merely a convenient provable weakening. Audit both
  directions against the informal claim with examples and counterexamples.
- Keep independent research branches isolated. Parallel work is appropriate for genuinely
  independent conjectures, counterexample searches, or literature searches; do not have multiple
  workers edit the same module or silently share an unverified assumption.

## Harness gates (INC-20260915-01)

The 2026-09-15 incident (`docs/INCIDENT_REPORT_2026-09-15_VACUOUS_SYNTHESIS_LOOP.md`) showed that
Lean acceptance plus prose is not evidence. The following are enforced by `scripts/harness_gate.py`
(called from `scripts/check_research_registry.sh`) and `.githooks/pre-commit`; the rules below say
what they check so you can work with them rather than around them.

- **One substantive theorem per registered row (G1-G3).** A new `PROVED-LEAN` row must cite
  theorems that exist; none may have its conclusion (or a conjunct of it) among its hypotheses or
  be `x = x`; at least one must be neither pure arithmetic over free `Nat`/`Int` variables, nor a
  wrapper (`intro`/`exact`/`refine`/`rcases` only), nor a bare `omega`/`rfl`. Check a file with
  `python3 scripts/harness_gate.py --lint-module Recaman/Foo.lean` before registering it.
  Arithmetic helper lemmas are fine; a module made only of them is not a research result.
- **Quote the statement (G5).** Every new `PROVED-LEAN` row (E-347 on) needs
  `docs/statement_audits/E-NNN.md`, generated with `--audit-template E-NNN`, quoting each cited
  signature verbatim and answering: do the binders mention `e`, `a`/`stateAt`, windows or phase
  lists; is any hypothesis an unproved defined `Prop` or the conclusion itself; is the proof a
  wrapper. A "no/yes/yes" means the row must not be described as resolving anything.
- **Defined hypotheses are not eliminations.** `def FooHypothesis : Prop := ...` followed by
  `FooHypothesis → goal` proves nothing about the orbit. `H → ¬ P` where `¬ P` is definitional
  is not the elimination of branch `P`. Such rows stay `PROVED-LEAN` only with the hypothesis
  named in the claim text; the unconditional statement stays `CONJECTURED`.
- **Central claims are pinned (P).** `docs/PROTECTED_CLAIMS.tsv` fixes the labels of E-001,
  E-067, E-070 and E-179. Do not edit that file: changing a central label is a human decision
  and the commit needs `RECAMAN_HUMAN_APPROVED=1`. Never write that an issue is CLOSED in the
  docs unless it is closed on GitHub.
- **No inflated names (G4).** Theorem and module names containing grand, master, universal,
  closure, synthesis, resolution or apex are rejected for new rows. Name the inequality or
  invariant actually proven.
- **One module per commit, 30 minutes apart.** The pre-commit hook rejects commits that add
  more than one `Recaman/*.lean` or follow the previous module-adding commit by less than
  30 minutes; `RECAMAN_ALLOW_BURST=1` is for the human monitor. Use the time for the falsifier:
  search `docs/EVIDENCE_REGISTRY.tsv` for `REFUTED` rows and existing certificates (E-240 refuted
  the pure-AAS route while it was being "proved").
- **Git hygiene.** Never `git add -A` or `git add .`; commit with `git commit -- <paths>` and
  inspect `git status -s` first. Do not stage or commit another session's files.

## Evidence labels

Use these exact labels in research notes:

- `PROVED-LEAN`: checked by Lean and included in the repository audit.
- `PROVED-PAPER`: complete human argument recorded, not yet checked by Lean.
- `COMPUTED`: exact finite computation with a reproducible command.
- `OBSERVED`: exploratory data without a frozen protocol or holdout.
- `CONJECTURED`: precise, falsifiable statement without proof.
- `REFUTED`: counterexample or countermodel recorded.
- `STOPPED`: branch failed its predeclared continuation gate.

Do not describe `COMPUTED`, `OBSERVED`, or `CONJECTURED` claims as theorems. A theorem whose
formal statement is weaker than its prose description has failed the audit even if Lean accepts it.

## Validation and handoff

- Run `python3 scripts/harness_gate.py --lint-module <file>` on any new Lean file and
  `bash scripts/test_harness_gates.sh` after touching the gates.
- Run `./scripts/check.sh` after Lean changes. New major theorems must be added to
  `Recaman/Audit.lean`.
- Do not add `sorry`, `admit`, `native_decide`, or user-defined axioms.
- A research handoff must contain: conclusion first; hypothesis-card status; changed files;
  commands run; strongest evidence; failed attempts and counterexamples; remaining uncertainty;
  and the next decision, including a stop recommendation when appropriate.
- Update the proof map or development log only after the claim and its evidence level are stable.
