# Proposed post-approval card and handoff updates

This file is a draft only. It must not be copied into the live cards or handoff unless the
independent registration auditor approves the exact E-360 row/G5 and the parent explicitly assigns
the application step.

## H-20260917-01 card proposal

Change the header status from `CONJECTURED` to `PROVED-LEAN` and append:

> 2026-09-21 registration (conditional on application): E-360 registers
> `short_tight_avoids_ss2_donor` for the frozen source hash
> `bb12f35acc8e48c584cead52d675e36b034afda22f0f28ecfd245031f70fee85`.
> The exact established Q is limited to arbitrary positive-period sign words whose nodup tight B
> consists of current-A minimal P2 windows with lag in {3,7,11}, and to a minimal lag-11 SS=2
> donor. It concludes true-oldest-phase nonmembership only. Ambient U, assumed Hall and positive
> drift are absent because short-window Hall is proved. General Gate T6, arbitrary lag, actual
> orbits, E-070/E-067 and surjectivity of the Recamán sequence remain unproved. The daytime missing entry audit and the
> 01:00 checker-source retention gap remain historical process debt.

The exact old-card-to-E-360 implication must be recorded with the promotion: `U.Nodup` plus
`B.Sublist U` gives `B.Nodup`; U completeness gives phase bounds, current-A and P2 windows for B;
the old minimal-lag condition gives `hB_min`; and `u0 ∈ U` with `lag u0 = 11` gives the donor P2
and minimality hypotheses. The old positive drift, ambient-U completeness after those projections,
assumed Hall, and `u0 ∉ B` are unused in the E-360 application. Thus the exact old card Q follows
from E-360 without silently changing the old quantifiers.

Add an evidence-log row labelled `PROVED-LEAN` pointing to E-360, the final G5, the independent
registration audit, and the exact successful validation command log. Do not relabel the used
p32/33 holdout from finite evidence to proof.

## H-20260920-01 card proposal

Change the header status from `CONJECTURED` to `PROVED-LEAN` and append:

> 2026-09-21 registration (conditional on application): E-360 registers the exact local conditional
> W as two conclusions: `w1_owns_oldest` gives `own t = t - 7`, and `w1_next_addition` gives
> `e (t + 1) = true`. Their exact premise is the four-field `OwnerFamily e mem own lag`; this defined
> structural premise is named, expanded, and not called unconditional. Under the existing concrete
> assumptions p>0, periodicity, nodup U, Hall on U, tight B sublisted from U, phase bounds,
> current-A members, and minimal P2 lag 3/7/11 windows, the E-358/E-359 construction
> `tight_owner_family` supplies the structure. The extracted constructors themselves are not new results.

Add an evidence-log row labelled `PROVED-LEAN` with the same source/audit references. Preserve the
weakened-model counterexamples as controls and do not promote later ShortTight declarations.

## RESEARCH_HANDOFF_2026-09-21_SOL.md proposal

Append a 02:00 section stating conclusion first:

> The independently approved E-360 registration records only the frozen local W and concrete
> short-tight donor-avoidance Q. The live row and official G5 passed G1-G5 in an isolated copy
> before application and passed the full repository check after application. No Lean mathematics,
> protected label, or central claim was changed; CURRENT_FRONTIER and PROOF_MAP each received one
> bounded E-360 entry. The exact
> source hashes, commands, exit codes, audit decision, changed files, process debts, excluded later
> theorems, and next decision are recorded in slot0200.

The applied card/frontier/proof-map/handoff metadata and hashes are part of the final independent
audit package; draft hashes alone do not authorize promotion. If the independent auditor rejects or requests a mathematical change, keep both cards
`CONJECTURED`, record the rejection, and do not apply the row or official G5.
