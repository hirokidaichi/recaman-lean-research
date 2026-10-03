# H-20260920-05 local word lemma candidate, slot 02:30

## Conclusion first

The exact local word lemma `ss2_intervening_prefix` and its two direct terminal
inequalities match paper sections 1-2 and the card's 15:21 refinement in both
directions. They are inhabited, length-independent statements with direct
structural proofs. The source does not assume its conclusion, a defined
unproved proposition, periodicity, an OwnerFamily, or an orbit fact. Exhaustive
replay in the already declared ranges passes, including the full `<= 0`
inequality; dropping any one of the four target premises produces a small
counterexample.

This is only a candidate audit of the three declarations. It does not complete
H-20260920-05, establish arbitrary-length donor avoidance, audit paper sections
3-5, or repair H-02/H-03's historical preformalization entry gap. H-05 remains
`CONJECTURED` pending the separate Sol verdict and all downstream obligations.

## Frozen question, acceptance, stopping condition

Question: for arbitrary `w : List Bool`, does `X=w++[A]`, mass X=0,
`moment X + length X <= 0`, and `ssCount X <= 2` force a strict S-ended P2
prefix, exactly as stated in the paper, without a length bound or hidden
conclusion? The direct inequalities are the general A-ended q-budget bound and
the SS<=2 AA-ended lower bound.

Acceptance requires exact signatures and unfolded definitions, a nonempty and
boundary finite check, negative controls for premise deletion, proof/dependency
inspection, vacuity/wrapper/free-arithmetic attacks, direct Lean and full check,
and independent Sol review. Stop without extending the frozen ranges or writing
new research Lean. Stream, periodic, donor-avoidance, and deletion consequences
are an obligation inventory, not this candidate.

Frozen at HEAD `08c08565c743f39350c9b959e1df7d30aa1cae5d`.
Target SHA-256 `a9540f5f891198ec91eefd73f62f9e35d4e59f645936dc3a349504e529b325de`.
Card SHA-256 `a85e406c648131011c20a689cf79d52b77424867e485f974ea2c48b2422e9fd6`.
Paper SHA-256 `e6d9c4dfd0013b00d431f6dae27a6db4f6d96ada11f48d9805a9168a0a92e0e6`.
Experiment SHA-256 `1ae348ab0b64db9168f7db27b07cf6763757939763d32f79fe8bdcb1be2d545a`.

## Strongest evidence

The verbatim statements, definitions, paper/Lean map, and exact proof chain are
in `statement_audit.md`. `P2 z` is exactly mass 1 and moment 0; `v != []`
makes the S-ended prefix strict. Every A-ended finite X is uniquely representable
as `w++[A]` for some w, so the paper and Lean quantifiers coincide.

The original frozen checker replay is byte-identical to both daytime outputs.
Discovery checks every binary word through length 18 and finds 8 premise cases.
Holdout regenerates all ending-A, mass-zero, exactly-SS2 words at lengths 20/24
and checks 8/16 cases. This is the already used range, not a new holdout and
not evidence for an infinite theorem by itself.

The independent literal checker over all binary words through 18 finds 8
premise cases, 3 at equality and 5 with strict negative `moment+length`.
The smallest is length-12 `AASASASASSSA`, whose strict P2 prefix is `AAS`.
It checks 434,721 q-budget inequality instances and 45,976 AA inequality
instances. Negative controls are `AAASSS` (drop ending A), `SASASSSA` (drop
mass zero), `SA` (drop moment bound), and `AAASSSSA` (drop SS bound); all meet
the remaining conditions and lack the conclusion.

The known E-130 `AAASSSASASA` counterexample to general SS<=2 S-ended prefix
normalization remains valid. It lies outside the new local lemma's mass-zero and
moment-plus-length hypotheses. This packet does not relabel E-130 or claim a
general normalization.

## Formal and procedural checks

Direct compilation of the untracked target exits 0. `report_vacuity.py --all`
reports 0/13 flagged. `harness_gate.py --lint-module` reports 13/13 substantive.
The full `./scripts/check.sh` passes 392 jobs and the 2,572-declaration axiom
audit. `#print axioms` shows only allowed core axioms. All commands use
`gtimeout 120s`; all recorded exits are 0 and stderr files are empty.

The current modified `Recaman.lean` imports `SS2OldestPattern`, so the root build
reaches it. `Recaman/Audit.lean` does not cite it, the evidence registry has no
row for it, and E-360 names it as pending separate audit. Therefore the full
check is build evidence only, not registration or meaning evidence.

The theorem bodies are not wrappers or pure arithmetic: both inequalities
structurally induct on Bool lists, and the prefix theorem performs well-founded
recursion plus terminal case analysis. No direct or imported dependency points
back to this new module. The result is a genuine local word statement, but the
newness decision remains bounded to that lemma.

## Downstream obligations and decision

Not audited as results here: `ss2_aas_oldest_has_prefix`, `ss2_no_w1_oldest`,
the oldest-offset/past decomposition, the three w1 placements, H-02 future AAS,
H-03 prefix reduction, periodic lift, short tight avoidance, deletion, arbitrary
lag, full supply capacity, and actual Recaman orbit consequences. The source
does not yet contain a final theorem expressing all of H-05. H-02/H-03 remain
`CONJECTURED` and procedurally incomplete; this later slot cannot retroactively
supply their missing entry reviews.

Writer judgments are separated: semantic correspondence **pass** for these
three declarations; mathematical novelty **limited pass** as a new local
length-independent lemma only; procedure **pending independent audit**.
Recommended card status remains `CONJECTURED`. If the independent audit passes,
record only the bounded local result and leave the complete H-05 chain open.

No source repair was made. No research Lean, original card, paper, experiment,
registry, frontier, proof map, Audit, root, gate, protected claim, or handoff was
edited. No stage or commit occurred. Raw stdout/stderr, exit files, frozen
source/card/paper/experiment snapshots, commands, and the relative manifest are
in this directory.
