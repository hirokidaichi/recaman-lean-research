# H-20261001-05 exact evidence

Base cbe51b7b1216f9700f432eb14803277113c02af4. Card and scripts were
frozen before discovery k=0..10 and disjoint claim-specific holdout k=11..80.
The previous repository may have examined some words elsewhere; this is
not a repository-wide untouched-data claim.

Run from the repository root:

```bash
shasum -a 256 -c docs/data/ss2_word_offset_span_20261001/PRE_RUN_SHA256SUMS
python3 experiments/ss2_word_offset_span.py discovery
python3 experiments/ss2_word_offset_span.py holdout
lake env lean docs/data/ss2_word_offset_span_20261001/core_controls.lean
```

The JSON files contain exact outputs and complete proper mass-one
positions/moments for each finite word, including source digest. Both
phases pass. Negative controls are in discovery.json. core_controls.log
is empty because the fixed kernel checks succeed without diagnostics.

Finite results are COMPUTED. The all-k claim is PROVED-PAPER only.
The marked newest S is not asserted to be an owner in a Hall-tight family.
