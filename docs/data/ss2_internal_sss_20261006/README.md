# Internal-SSS fixed controls

H-20261006-03, base65c25ab. The [frozen protocol](protocol-frozen.md) and
[source hashes](source-frozen.sha256) precede the controls.

- Discovery: p33 positive pure-X model; p33 removal-of-NoSAAS control;
  reused p22 second-prefix collision; constructed r0 oldest-SSS model.
- Holdout: constructed r1/r2 oldest-SSS models, p72/p112.
- Both runs PASS. These are six explicitly selected constructions, not an
  exhaustive census through period112 and not a proof by sampling.
- The final s+1 endpoint exclusion was proposed after the six outputs.
  Thus they are regression evidence for that new statement, not a fresh
  holdout. Its proof covers all future clocks symbolically.

The negative model preserves minimal P2/SS2 donors but violates NoSAAS
and has its SSS start at the oldest S. It refutes removing NoSAAS from
the pure-X q>s conclusion; it does not refute the general endpoint or
local Hall inequality.

~~~sh
python3 experiments/ss2_internal_sss_controls.py discovery
python3 experiments/ss2_internal_sss_controls.py holdout
~~~

Exact output: [discovery](discovery.json), [holdout](holdout.json).
The auditor replayed both and independently scanned all eligible endpoint
windows of these positive-mass models, with exact agreement:
[verification](../ss2_pair_endpoints_20261006/audit/internal_sss_verification.json).
The general paper theorem does not require positive mass.

[Complete independent proof and scope](../ss2_pair_endpoints_20261006/audit/oldest-sss-endpoint-addendum.md).
No Lean changes or kernel-check claim were made. The next research unit
is the separated-SS collision class; the SSS class is PROVED-PAPER.

