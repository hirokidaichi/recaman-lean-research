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

- Run `./scripts/check.sh` after Lean changes. New major theorems must be added to
  `Recaman/Audit.lean`.
- Do not add `sorry`, `admit`, `native_decide`, or user-defined axioms.
- A research handoff must contain: conclusion first; hypothesis-card status; changed files;
  commands run; strongest evidence; failed attempts and counterexamples; remaining uncertainty;
  and the next decision, including a stop recommendation when appropriate.
- Update the proof map or development log only after the claim and its evidence level are stable.
