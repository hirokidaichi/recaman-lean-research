# Endpoint/core follow-up, 2026-10-06

Conclusion: **PROVED-PAPER**, independently audited, for local Hall of a
same-oldest minimal SS2 current-A pair under global NoSAAS when its two
SS edges form one SSS run. Positive period mass is not required.
The unrestricted endpoint candidate and H-01 local Hall remain
CONJECTURED. No Lean source changed.

Read [the strategy and exact proof scope](../../RESEARCH_PLAN_2026-10-06_SS2_REMAINING.md)
and [final independent reconstruction](audit/oldest-sss-endpoint-addendum.md).
E-369 records the refuted NoSAAS-only oldest-injectivity shortcut;
E-370 records the complete paper capacity subcase. This advances beyond
the previous STOPPED geometry-only route with a concrete second S.

## Exact finite diagnostic

H-02 asks whether N_pair minus ALL lowSS S-ended endpoint phases has at
least two elements. The endpoint universe includes nonminimal witnesses.
All 24 collision pairs in the reused p1..22 domain pass, minimum excluded
count5. Discovery p1..18:3 pairs; holdout p19..22:21. This is COMPUTED only,
on a previously used domain, with no period-range extension.

The parent emitted every pair and endpoint witness. Its Python checker
directly enumerates all positive lags through the positive-mass bound
p(p+1). The auditor separately recounted the same domain and endpoint
sets: [exact agreement](audit/verification.json). All 24 pairs match.
There is **one** circular NoSAAS collision at p22, which exercises the
second prefix family. Do not state that the domain has zero such pairs.

Base: 65c25ab742ab4aa749bfd5f48438dbcb7b774d1d.
[Pre-run protocol](protocol-frozen.md), [discovery](discovery.jsonl),
[holdout](holdout.jsonl), [parent verification](verification.json),
[Sol constructed p33 control](sol61/output.json).

Reproduce from the repository root:

~~~sh
clang++ -O3 -std=c++17 experiments/ss2_pair_endpoints.cpp -o /tmp/recaman-ss2-pair-endpoints
/tmp/recaman-ss2-pair-endpoints 1 18
python3 experiments/verify_ss2_pair_endpoints.py docs/data/ss2_pair_endpoints_20261006/discovery.jsonl
/tmp/recaman-ss2-pair-endpoints 19 22
python3 experiments/verify_ss2_pair_endpoints.py docs/data/ss2_pair_endpoints_20261006/discovery.jsonl docs/data/ss2_pair_endpoints_20261006/holdout.jsonl
python3 docs/data/ss2_pair_endpoints_20261006/sol61/check.py
~~~

The C++ includes the previous frozen falsifier's helpers and renames its
unused main. Clang warns that this renamed, never-invoked entry has no
explicit return; the actual new entry and computations run successfully.
Independent direct implementations do not use that included entry.

## Proof and countermodel audit

[Sol's complete evolving paper report](sol61/report.md) retains the
sequence of refinements; later sections supersede earlier temporary open
cases. The final argument handles internal SSS, pure-prefix oldest SSS,
and start-S oldest SSS. The second phase is respectively the first S
of the triple, or the next-oldest S. The latter uses an all-future mass
bound rather than a finite endpoint enumeration.

[Initial final audit](audit/report.md) verifies NoSAAS prefix reduction,
the all-p>=33 collision family and the finite diagnostic.
[Pure-prefix addendum](audit/capacity-subcase-addendum.md) proves the first
capacity subcase. [Final addendum](audit/oldest-sss-endpoint-addendum.md)
also proves the start-S/oldest-SSS case and independently replays all six
fixed models. These are paper statements, not Lean statements.

The six supplementary models are saved in
[the internal-SSS controls directory](../ss2_internal_sss_20261006/README.md).
The final endpoint s+1 idea was derived after those outputs existed, so
they are regression checks for that idea, not fresh holdout evidence.
The all-lag evidence is the complete independent paper proof.

Commands, exact independent outputs, replay scripts and hashes are under
audit/ and SHA256SUMS. No binary is required for reproduction.
Source/registry/manifest checks are recorded in the final handoff.

