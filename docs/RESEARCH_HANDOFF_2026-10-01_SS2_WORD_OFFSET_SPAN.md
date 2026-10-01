# Fixed-SS2 offset-span handoff (#73 bounded unit)

Conclusion: E-365 is `PROVED-PAPER`. V_k=(SA)^k SAAASSAAASS (AS)^(3k)
is minimal P2, SS=2 and NoSAAS with an explicit current A, yet its
newest-to-oldest S span is 8k+10 while terminal A length is zero.
Stop word-only constant-span arguments. This marks an S, not an owner
in a Hall-tight family, and does not refute #73 or owner-family bounds.

Hypothesis card: H-20261001-05, `PROVED-PAPER`, independent review pending.
Separate branch/worktree based on `cbe51b7b1216f9700f432eb14803277113c02af4`.
The padding method is the existing E-122 method with a fixed SS=2 core;
no new general padding theorem or capacity claim is made.

## Changed files and commands

Paper proof, hypothesis card, this handoff, `experiments/ss2_word_offset_span.py`,
frozen data/core controls, and registry/frontier/proof-map synchronization.
No new Recaman Lean module, root import or all-k axiom-audit entry.

```bash
shasum -a 256 -c docs/data/ss2_word_offset_span_20261001/PRE_RUN_SHA256SUMS
python3 experiments/ss2_word_offset_span.py discovery
python3 experiments/ss2_word_offset_span.py holdout
lake env lean docs/data/ss2_word_offset_span_20261001/core_controls.lean
./scripts/check.sh
```

Full repository check: 392 jobs and 2,569 permitted-axiom reports on this
base. The independent #76 module is not in this branch. Existing build
cache was copied from the isolated worktree; Lake rebuilt the different
root, and the new fixed-core checks were run in this worktree.

## Strongest evidence, failures and uncertainty

The complete paper argument covers all prefixes in initial SA, fixed core,
and final AS regions. Every proper mass-one moment is strictly positive.
NoSAAS is checked inside all blocks and at every four-sign junction.
Endpoints are actual S positions. For every Nat C0, k=C0 gives span>C0.

Frozen computation checks k=0..10 discovery and k=11..80 holdout, including
complete position/moment lists. Largest word length651, span650. These are
COMPUTED; the all-k claim remains paper-only. Only the fixed core's
mass/moment/count/prefix table/NoSAAS scan is checked by Lean.

No mathematical failure or hypothesis repair occurred. Deliberately using
the wrong core at k=1 gives earlier P2 at7; one extra AS gives moment-1
and an earlier P2 at19. The full proof path was recorded within the
predeclared 20-minute gate. Separate-session review is pending.

Next decision: a bounded actual owner-delta question must specify an
additional tight-family/owner condition and falsify it separately. Do
not increase the constant or reuse terminal-A length as total extent.
General #73, Hall, Gate T6 and protected central claims are unchanged.
